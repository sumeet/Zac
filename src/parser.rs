use itertools::Itertools;

#[derive(Debug)]
pub struct Program {
    pub block: Block,
}

#[derive(Debug, Clone)]
pub struct Block(pub Vec<Expr>);

// TODO: should probably put a concept of newline into here because newlines from the programmer
// are important
#[derive(Debug, Clone)]
pub enum Expr {
    Block(Block),
    Ref(Ref),
    Comment(String),
    Assignment(Assignment),
    IntLiteral(i128),
    FunctionCall(FunctionCall),
    While(While),
}

#[derive(Debug, Clone)]
pub enum Ref {
    CommentRef(String),
    VarRef(String),
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub name: String,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct FunctionCall {
    pub r#ref: Ref,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct While {
    pub cond: Box<Expr>,
    pub block: Block,
}

// usage of peg stolen from https://github.com/A1Liu/gone/blob/master/src/parser.rs
peg::parser! {
    pub grammar parser() for str {
        pub rule program() -> Program
            = block:block()  { Program { block } }

        rule block() -> Block
            = _ exprs:(expr() ** _) _ { Block(exprs) }

        rule while_loop() -> Expr
            = "while(" _? cond:expr() ")" _* "{" _? block:block() _? "}" {
                Expr::While(While {
                    cond: Box::new(cond),
                    block,
                })
            }

        rule expr() -> Expr
            = comment() / assignment() / int() / func_call() / r#ref()

        rule func_call() -> Expr
            = r#ref:var_ref() "(" _? args:(expr() ** comma()) _? ")" {
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
            = "#" r:ident() { Ref::CommentRef(r.into()) }

        rule assignment() -> Expr
            = "let" _ ident:ident() _ "=" _ expr:expr() { Expr::Assignment(Assignment {
                name: ident.to_string(),
                expr: Box::new(expr),
            })}


        rule int() -> Expr
            = num:$(['1' .. '9']+ ['0' .. '9']*) { Expr::IntLiteral(num.parse().unwrap()) }

        rule comment() -> Expr = c:comment_string() { Expr::Comment(c) }
        rule comment_string() -> String
            = "/" "/" _? body:$([^ '\r' | '\n']*)? following:following_comment()*  {
                body.map(|b| b.to_owned()).into_iter().chain(following.into_iter()).join(" ")
            }
        rule following_comment() -> String
            = newline()? c:comment_string() {
                if c.starts_with("//") {
                    let c = c.trim_start_matches("//").trim_start();
                    format!("\n\n{}", c)
                } else {
                    c
                }
            }

        rule ident() -> &'input str = $(ident_start()+ ['a'..='z' | 'A'..='Z' | '_' | '0'..='9']*)
        rule ident_start() -> &'input str = $(['a'..='z' | 'A'..='Z' | '_']+)

        rule comma() -> () = _? "," _?
        rule nbspace() = [' ' | '\t']+
        rule newline() = "\n" / "\r\n"
        rule whitespace() = (nbspace() / newline())+
        rule _() = quiet!{ whitespace() };
    }
}
