use anyhow::{anyhow, bail};
use itertools::Itertools;
use lazy_static::lazy_static;
use litrs::StringLit;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Mutex;

pub type ExprID = usize;

lazy_static! {
    static ref NEXT_ID: Mutex<ExprID> = Mutex::new(0);
}

fn next_id() -> usize {
    let mut next_id = NEXT_ID.lock().unwrap();
    let this_id = *next_id;
    *next_id += 1;
    this_id
}

#[derive(Debug)]
pub struct Program {
    pub block: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block(pub Vec<BlockEl>);

impl Block {
    pub fn exprs(&self) -> impl Iterator<Item = &Expr> + '_ {
        self.0.iter().filter_map(|block_el| match block_el {
            BlockEl::Expr(expr) => Some(expr),
            BlockEl::NewLine => None,
        })
    }

    pub fn exprs_mut(&mut self) -> impl Iterator<Item = &mut Expr> + '_ {
        self.0.iter_mut().filter_map(|block_el| match block_el {
            BlockEl::Expr(expr) => Some(expr),
            BlockEl::NewLine => None,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BlockEl {
    Expr(Expr),
    NewLine,
}

// TODO: should probably put a concept of newline into here because newlines from the programmer
// are important
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Block(Block),
    Ref(Ref),
    Comment(Comment),
    Assignment(Assignment),
    IntLiteral(i128),
    StringLiteral(String),
    ListLiteral(Vec<Expr>),
    FuncDef(FuncDef),
    FunctionCall(FunctionCall),
    While(While),
    If(If),
    BinOp(BinOp),
    ResultComment(ExprID, Box<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Div,
    Mul,
    Eq,
    Neq,
    Gte,
    Gt,
    Lte,
    Lt,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinOp {
    pub op: Op,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef {
    pub name: String,
    pub arg_names: Vec<String>,
    pub block: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Comment {
    pub name: Option<String>,
    pub body: String,
}

pub fn find_comments_mut(
    program: &'a mut Program,
) -> anyhow::Result<HashMap<String, &'a mut Comment>> {
    let mut comments = HashMap::new();
    for expr in &mut program.block.exprs_mut() {
        try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
    }
    Ok(comments)
}

fn find_expr_comments_mut(expr: &'a mut Expr) -> anyhow::Result<HashMap<String, &'a mut Comment>> {
    let mut comments = HashMap::new();
    match expr {
        Expr::Block(block) => {
            for expr in block.exprs_mut() {
                try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
            }
        }
        Expr::Comment(c) => {
            let name = c.name.clone();
            if let Some(name) = name {
                try_insert(&mut comments, name, c)?;
            }
        }
        Expr::Assignment(Assignment { r#ref: _, expr }) => {
            try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
        }
        Expr::FunctionCall(FunctionCall { r#ref: _, args }) => {
            for expr in args {
                try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
            }
        }
        Expr::While(While { cond, block }) | Expr::If(If { cond, block }) => {
            try_extend(&mut comments, &mut find_expr_comments_mut(cond)?)?;
            for expr in block.exprs_mut() {
                try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
            }
        }
        Expr::Ref(_) | Expr::IntLiteral(_) | Expr::BinOp(_) | Expr::StringLiteral(_) => {}
        Expr::FuncDef(FuncDef {
            name: _,
            arg_names: _,
            block,
        }) => {
            for expr in block.exprs_mut() {
                try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
            }
        }
        Expr::ListLiteral(exprs) => {
            for expr in exprs {
                try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
            }
        }
        Expr::ResultComment(_, expr) => {
            try_extend(&mut comments, &mut find_expr_comments_mut(expr)?)?;
        }
    }
    Ok(comments)
}

pub fn try_extend<K: Eq + Hash + Send + Sync + Debug + Display, V: Send + Sync + Debug>(
    into: &mut HashMap<K, &'a mut V>,
    from: &mut HashMap<K, &'a mut V>,
) -> anyhow::Result<()> {
    for (k, v) in from.drain() {
        try_insert(into, k, v)?;
    }
    Ok(())
}

fn try_insert<K: Eq + Hash + Send + Sync + Debug + Display, V: Send + Sync + Debug>(
    into: &mut HashMap<K, &'a mut V>,
    k: K,
    v: &'a mut V,
) -> anyhow::Result<()> {
    if into.contains_key(&k) {
        bail!(anyhow!("key {} already exists", k));
    }
    into.insert(k, v);
    Ok(())
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ref {
    CommentRef(String),
    VarRef(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Assignment {
    pub r#ref: Ref,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
    pub r#ref: Ref,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct While {
    pub cond: Box<Expr>,
    pub block: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct If {
    pub cond: Box<Expr>,
    pub block: Block,
}

// usage of peg stolen from https://github.com/A1Liu/gone/blob/master/src/parser.rs
peg::parser! {
    pub grammar parser() for str {
        pub rule program() -> Program
            = block:block()  { Program { block } }

        rule block() -> Block
            = block_els:(block_el()+) { Block(block_els) }

        rule block_el() -> BlockEl
            = nbspace()? b:(block_el_expr() / block_el_blankline()) { b }

        rule block_el_expr() -> BlockEl
            = e:expr() { BlockEl::Expr(e) }

        rule block_el_blankline() -> BlockEl
            = newline() { BlockEl::NewLine }

        rule func_decl() -> Expr
            = "defn" _? name:ident() _? "(" _? arg_names:(ident() ** comma()) _? ")" _* "{" _? block:block() _? "}" {
                Expr::FuncDef(FuncDef {
                    name: name.to_string(),
                    arg_names: arg_names.iter().map(|n| n.to_string()).collect(),
                    block,
                })
            }

        rule if_statement() -> Expr
            = "if" _? "(" _? cond:expr() _? ")" _* "{" _? block:block() _? "}" {
                Expr::If(If {
                    cond: Box::new(cond),
                    block,
                })
            }

        rule while_loop() -> Expr
            = "while" _? "(" _? cond:expr() _? ")" _* "{" _? block:block() _? "}" {
                Expr::While(While {
                    cond: Box::new(cond),
                    block,
                })
            }

        rule expr() -> Expr
            = comment() /
              expr:(while_loop() / if_statement() / func_decl() / assignment()
                    / bin_op_expr() / term()) (nbspace()? / newline()) result_comment:result_comment()? {
                if result_comment.is_some() {
                    Expr::ResultComment(next_id(), Box::new(expr))
                } else {
                    expr
                }
            }

        rule result_comment() -> ()
            = "//" _? "#" comment_inner_text()? following_comment()* { () }

        #[cache_left_rec]
        rule term() -> Expr
            = string_literal_expr() / list_literal() / int() / func_call() / r#ref() / bin_op_expr()

        #[cache_left_rec]
        rule bin_op_expr() -> Expr
            = left:term() _? op:op() _? right:term() {
                Expr::BinOp(BinOp { lhs: Box::new(left), op: op, rhs: Box::new(right) })
            }

        rule op() -> Op
            = ("+" { Op::Add } / "/" { Op::Div } / "-" { Op::Sub } /
               "*" { Op::Mul } / "==" { Op::Eq } / "!=" { Op::Neq } / ">=" { Op::Gte } /
               "<=" { Op::Lte } / ">" { Op::Gt } / "<" { Op::Lt } / "&&" { Op::And } /
               "||" { Op::Or })

        rule func_call() -> Expr
            = r#ref:ref_ref() "(" _? args:(expr() ** comma()) _? ")" {
                Expr::FunctionCall(FunctionCall {
                    r#ref,
                    args,
                })
            }

        rule r#ref() -> Expr
            = r:ref_ref() { Expr::Ref(r) }
        rule ref_ref() -> Ref
            = var_ref() / comment_ref()
        rule var_ref() -> Ref
            = r:ident() { Ref::VarRef(r.into()) }
        rule comment_ref() -> Ref
            = r:comment_ident() { Ref::CommentRef(r) }
        rule comment_ident() -> String
            = "#" i:ident() { i.into() }

        rule assignment() -> Expr
            = "let" _ r:ref_ref() _ "=" _ expr:expr() { Expr::Assignment(Assignment {
                r#ref: r,
                expr: Box::new(expr),
            })}


        rule list_literal() -> Expr
            = "[" _? exprs:(expr() ** comma()) _? "]" { Expr::ListLiteral(exprs) }

        rule string_literal_expr() -> Expr
            = string_lit:string_lit() { Expr::StringLiteral(string_lit) }

        rule int() -> Expr
            = num:$("0" / "-"? ['1' ..= '9']+ ['0' ..= '9']*) { Expr::IntLiteral(num.parse().unwrap()) }

        rule comment() -> Expr = named_comment() / anon_comment()

        rule named_comment() -> Expr
            = "/" "/" _? name:comment_ident() body:following_comment()?  {
                Expr::Comment(Comment { name: Some(name), body: body.unwrap_or_else(|| "".into()) })
            }

        rule anon_comment() -> Expr
            = body:comment_string() { Expr::Comment(Comment { name: None, body })}

        rule comment_string() -> String
            = "/" "/" onespace()? body:comment_inner_text()? following:following_comment()*  {
                body.map(|b| b.to_owned()).into_iter().chain(following.into_iter()).join("\n")
            }

        rule comment_inner_text() -> &'input str
            = body:$([^ '\r' | '\n']*) { body }

        rule following_comment() -> String
            = newline() c:comment_string() {
                if c.starts_with("//") {
                    let c = c.trim_start_matches("//");
                    let c = c.strip_prefix(' ').unwrap_or(c);
                    format!("\n{}", c)
                } else {
                    c
                }
            }

        rule ident() -> &'input str = $(ident_start()+ ['a'..='z' | 'A'..='Z' | '_' | '-' | '0'..='9']*)
        rule ident_start() -> &'input str = $(['a'..='z' | 'A'..='Z' | '_']+)

        rule string_lit() -> String
            = str:$("\"" (!['"'][_] / "\"\"")* "\"") {?
                Ok(StringLit::parse(str).or_else(|e| { dbg!(str, e) ; Err("string_lit: " ) })?.value().to_owned())
            }

        rule comma() -> () = _? "," _?
        rule nbspace() = onespace()+
        rule onespace() = [' ' | '\t']
        rule newline() = "\n" / "\r\n"
        rule whitespace() = (nbspace() / newline())+
        rule _() = quiet!{ whitespace() };
    }
}
