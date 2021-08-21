#![feature(exclusive_range_pattern)]

use crate::parser::{find_comments, Expr};
use interp::Interpreter;

mod interp;
mod parser;
mod reassemble;

pub fn main() -> anyhow::Result<()> {
    let input = r#"
// #header
// yo
//
// this is the continuation
let mystring = // hello

// TODO: can't set mynum to 0
let mynum = 1

let #header = // here u go

// this is a different comment
add(mynum, mynum)

// while(1) {
// let x = 123
// }
"#;
    let program = parser::parser::program(input)?;

    let mut interp = Interpreter::new();
    for comment in find_comments(&program) {
        interp.add_comment(comment)?;
    }

    let block = Expr::Block(program.block.clone());
    interp.interp(&block)?;

    let assembled = reassemble::output_code(&program);
    println!("{}", assembled);

    Ok(())
}
