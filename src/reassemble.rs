use std::iter::Peekable;
use std::slice::Iter;

use crate::parser::{Assignment, Expr, FunctionCall, Program};

pub fn assemble_program(program: &Program, assembled: &mut String) {
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
            assembled.push_str("\n");
        }
        Expr::IntLiteral(n) => assembled.push_str(&n.to_string()),
        Expr::Ref(s) => {
            assembled.push_str(s);
            assembled.push_str("\n");
        }
        Expr::FunctionCall(FunctionCall { name, args }) => {
            assembled.push_str(name);
            assembled.push_str("(");
            if let Some((last, init)) = args.split_last() {
                for arg in init {
                    assemble_expr(assembled, exprs, arg);
                    assembled.push_str(",");
                }
                assemble_expr(assembled, exprs, last);
            }
            assembled.push_str(")");
        }
    }
}
