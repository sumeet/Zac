#![feature(exclusive_range_pattern)]

use crate::parser::Expr;
use interp::Interpreter;

mod interp;
mod parser;
mod reassemble;

pub fn main() -> anyhow::Result<()> {
    let input = r#"
// header:
// yo
//
// this is the continuation
let mystring = // hello

// TODO: can't set mynum to 0
let mynum = 1

// this is a different comment
add(mynum, mynum)

// while(1) {
// let x = 123
// }
"#;
    let program = parser::parser::program(input)?;
    let assembled = reassemble::assemble_program(&program);
    println!("{}", assembled);

    let interp = Interpreter::new();
    let block = Expr::Block(program.block);
    interp.interp(&block)?;

    Ok(())
}
