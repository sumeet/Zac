#![feature(exclusive_range_pattern)]
#![feature(map_try_insert)]
#![feature(in_band_lifetimes)]
#![feature(box_syntax)]

use anyhow::anyhow;
use std::fs::{read_to_string, File};
use std::io::{stdout, Write};
use zac_lib::replace_comments_in_source_code;

use zac_lib::interp::Interpreter;
use zac_lib::parser;
use zac_lib::parser::{find_comments_mut, Expr};
use zac_lib::reassemble;

pub fn main() -> anyhow::Result<()> {
    let (filename, is_dry_run) = parse_args()?;

    let input = read_to_string(&filename)?;
    let mut program = parser::parser::program(&input)?;

    let mut interp = Interpreter::new();
    for (_, comment) in find_comments_mut(&mut program)? {
        interp.add_comment(comment)?;
    }

    let block = Expr::Block(program.block.clone());
    interp.interp(&block)?;

    replace_comments_in_source_code(&mut program, &mut interp)?;

    let assembled = reassemble::output_code(&program, &interp);
    if is_dry_run {
        stdout().lock().write_all(assembled.as_bytes())?;
    } else {
        File::create(&filename)?.write_all(assembled.as_bytes())?;
    }
    Ok(())
}

fn parse_args() -> anyhow::Result<(String, bool)> {
    let mut args = std::env::args();
    let cmd_name = args.next().unwrap();
    let filename = args
        .next()
        .ok_or_else(|| anyhow!("usage: {} <code.zac> [--dry]", cmd_name))?;
    let dry_run = args.next() == Some("--dry".to_string());
    Ok((filename, dry_run))
}
