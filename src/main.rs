use itertools::Itertools;

#[derive(Debug)]
pub struct Program {
    exprs: Vec<Expr>,
}

#[derive(Debug)]
enum Expr {
    Comment(String),
}

fn assemble_program(program: &Program) -> String {
    let mut assembled = "".to_owned();
    let mut exprs = program.exprs.iter().peekable();
    while let Some(expr) = exprs.next() {
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
        }
    }
    assembled
}

peg::parser! {
  grammar list_parser() for str {
    pub rule program() -> Program
        = _ exprs:(expr() ** _) _  { Program { exprs } }

    rule expr() -> Expr
        = comment()

    rule comment() -> Expr = c:comment_string() { Expr::Comment(c) }

    rule comment_string() -> String
        = "/" "/" _? body:$([^ '\r' | '\n']*)? following:following_comment()*  {
            let c = body.map(|b| b.to_owned()).into_iter().chain(following.into_iter()).join(" ");
            c
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


// this is a different comment
"#;
    let program = list_parser::program(input)?;
    println!("{}", assemble_program(&program));
    Ok(())
}
