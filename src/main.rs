#![feature(exclusive_range_pattern)]

use interp::Interpreter;

mod interp;
mod parser;
mod reassemble;

pub fn main() -> anyhow::Result<()> {
    let input = r#"
// hell jwieof iaowef
// yo
//
// this is the continuation

let mystring = // hello
let mynum = 1234

// this is a different comment
add(mynum, mynum)
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
