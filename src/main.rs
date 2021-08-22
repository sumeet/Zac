#![feature(exclusive_range_pattern)]
#![feature(map_try_insert)]
#![feature(in_band_lifetimes)]

use crate::parser::{find_comments_mut, Expr, Program};
use anyhow::anyhow;
use interp::Interpreter;
use std::fs::{read_to_string, File};
use std::io::Write;

mod interp;
mod parser;
mod reassemble;

pub fn main() -> anyhow::Result<()> {
    let filename = parse_args()?;

    let input = read_to_string(&filename)?;
    let mut program = parser::parser::program(&input)?;

    let mut interp = Interpreter::new();
    for (_, comment) in find_comments_mut(&mut program)? {
        interp.add_comment(comment)?;
    }

    let block = Expr::Block(program.block.clone());
    interp.interp(&block)?;

    replace_comments_in_source_code(&mut program, &mut interp)?;

    let assembled = reassemble::output_code(&program);
    File::create(&filename)?.write_all(assembled.as_bytes())?;
    Ok(())
}

fn parse_args() -> anyhow::Result<String> {
    let mut args = std::env::args();
    let cmd_name = args.next().unwrap();
    args.next()
        .ok_or(anyhow!("usage: {} <code.zack>", cmd_name))
}

fn replace_comments_in_source_code(
    mut program: &mut Program,
    interp: &mut Interpreter,
) -> anyhow::Result<()> {
    let mut comments = find_comments_mut(&mut program)?;
    for (name, body) in interp.comments() {
        let code_comment = comments
            .get_mut(name)
            .ok_or_else(|| anyhow!("original code didn't contain comment {}", name))?;
        code_comment.body = body.to_string();
    }
    Ok(())
}
