use itertools::Itertools;

#[derive(Debug)]
pub struct Program {
    pub exprs: Vec<Expr>,
}

#[derive(Debug)]
pub enum Expr {
    Comment(String),
    Assignment(Assignment),
    IntLiteral(i128),
    Ref(String),
    FunctionCall(FunctionCall),
    While(While),
}

#[derive(Debug)]
pub struct Assignment {
    pub name: String,
    pub expr: Box<Expr>,
}

#[derive(Debug)]
pub struct FunctionCall {
    pub name: String,
    pub args: Vec<Expr>,
}

#[derive(Debug)]
pub struct While {
    pub cond: Box<Expr>,
    pub block: Vec<Expr>,
}

// usage of peg stolen from https://github.com/A1Liu/gone/blob/master/src/parser.rs
peg::parser! {
    pub grammar parser() for str {
        pub rule program() -> Program
            = _ exprs:(expr() ** _) _  { Program { exprs } }

        rule block() -> Vec<Expr>
            = _ exprs:(expr() ** _) _ { exprs }

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
            = name:ident() "(" _? args:(expr() ** comma()) _? ")" {
                Expr::FunctionCall(FunctionCall {
                    name: name.into(),
                    args,
                })
            }

        rule r#ref() -> Expr
            = r:ident() { Expr::Ref(r.into()) }

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
