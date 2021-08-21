#![feature(exclusive_range_pattern)]

use interp::Interpreter;

mod interp;
mod parser;
mod reassemble;

pub fn main() -> anyhow::Result<()> {
    let input = r#"
// yo
//
// this is the continuation
let mystring = // hello

// TODO: can't set mynum to 0
let mynum = 1

// this is a different comment
add(mynum, mynum)

while(1) {
let x = 123
}
"#;
    let program = parser::parser::program(input)?;
    let mut assembled = String::new();
    reassemble::assemble_program(&program, &mut assembled);
    println!("{}", assembled);

    let interp = Interpreter::new();
    for expr in &program.exprs {
        interp.interp(expr)?;
    }

    Ok(())
}
