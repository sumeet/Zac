use itertools::Itertools;
use std::iter::Peekable;
use std::slice::Iter;

#[derive(Debug)]
pub struct Program {
    exprs: Vec<Expr>,
}

#[derive(Debug)]
enum Expr {
    Comment(String),
    Assignment(Assignment),
}

#[derive(Debug)]
struct Assignment {
    name: String,
    expr: Box<Expr>,
}

fn assemble_program(program: &Program, assembled: &mut String) {
    let mut exprs = program.exprs.iter().peekable();
    while let Some(expr) = exprs.next() {
        assemble_expr(assembled, &mut exprs, expr)
    }
}

fn assemble_expr(assembled: &mut String, exprs: &mut Peekable<Iter<Expr>>, expr: &Expr) {
    match expr {
        Expr::Comment(ref body) => {
            for line in body.lines() {
                assembled.push_str("// ");
                assembled.push_str(line);
                assembled.push_str("\n");
            }
            if let Some(Expr::Comment(_)) = exprs.peek() {
                assembled.push_str("\n");
            }
        }
        Expr::Assignment(Assignment { name, expr }) => {
            assembled.push_str("let ");
            assembled.push_str(name);
            assembled.push_str(" = ");
            assemble_expr(assembled, exprs, expr);
        }
    }
}

peg::parser! {
  grammar list_parser() for str {
    pub rule program() -> Program
        = _ exprs:(expr() ** _) _  { Program { exprs } }

    rule expr() -> Expr
        = comment() / assignment()

    rule assignment() -> Expr
        = "let" _ ident:ident() _ "=" _ expr:expr() { Expr::Assignment(Assignment {
            name: ident.to_string(),
            expr: Box::new(expr),
        })}


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

    rule nbspace() = [' ' | '\t']+
    rule newline() = "\n" / "\r\n"
    rule whitespace() = (nbspace() / newline())+
    rule _() = quiet!{ whitespace() };
  }
}

pub fn main() -> anyhow::Result<()> {
    let input = r#"
// hell jwieof iaowef
// yo
//
// this is the continuation

let x123 = // hello


// this is a different comment
"#;
    let program = list_parser::program(input)?;
    let mut assembled = String::new();
    assemble_program(&program, &mut assembled);
    println!("{}", assembled);
    Ok(())
}
