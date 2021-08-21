#![feature(exclusive_range_pattern)]
#![feature(map_try_insert)]
#![feature(in_band_lifetimes)]

use crate::parser::{find_comments_mut, Expr};
use anyhow::anyhow;
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
// and this is more

// this is a different comment
// and the continuation
add(mynum, mynum)

// while(1) {
//   let x = 123
// }
"#;
    let mut program = parser::parser::program(input)?;

    let mut interp = Interpreter::new();
    for (_, comment) in find_comments_mut(&mut program)? {
        interp.add_comment(comment)?;
    }

    let block = Expr::Block(program.block.clone());
    interp.interp(&block)?;

    let mut comments = find_comments_mut(&mut program)?;
    for (name, body) in interp.comments() {
        let code_comment = comments
            .get_mut(name)
            .ok_or_else(|| anyhow!("original code didn't contain comment {}", name))?;
        code_comment.body = body.to_string();
    }

    let assembled = reassemble::output_code(&program);
    println!("{}", assembled);
    Ok(())
}
