use crate::parser::{Assignment, BlockEl, Comment, Expr, FunctionCall, Program, Ref, While};
use itertools::Itertools;

pub fn output_code(program: &Program) -> String {
    let mut assembled = String::new();
    assemble_expr(&mut assembled, &Expr::Block(program.block.clone()));
    assembled
}

fn assemble_expr(assembled: &mut String, expr: &Expr) {
    match expr {
        Expr::Block(block) => {
            for block_el in &block.0 {
                match block_el {
                    BlockEl::Expr(expr) => {
                        assemble_expr(assembled, expr);
                    }
                    BlockEl::NewLine => assembled.push_str("\n"),
                }
            }
        }
        Expr::Comment(Comment { name, body }) => {
            if let Some(name) = name {
                assembled.push_str("// #");
                assembled.push_str(name);

                if body.is_empty() {
                    return;
                }
            }

            if body.is_empty() {
                assembled.push_str("//");
                return;
            }

            let mut lines = body.lines().peekable();
            while let Some(line) = lines.next() {
                assembled.push_str("\n// ");
                assembled.push_str(line);
            }
        }
        Expr::Assignment(Assignment { r#ref, expr }) => {
            assembled.push_str("let ");
            assemble_ref(r#ref, assembled);
            assembled.push_str(" = ");
            assemble_expr(assembled, expr);
        }
        Expr::IntLiteral(n) => assembled.push_str(&n.to_string()),
        Expr::Ref(r#ref) => assemble_ref(r#ref, assembled),
        Expr::FunctionCall(FunctionCall { r#ref, args }) => {
            assemble_ref(r#ref, assembled);
            assembled.push_str("(");
            if let Some((last, init)) = args.split_last() {
                for arg in init {
                    assemble_expr(assembled, arg);
                    assembled.push_str(", ");
                }
                assemble_expr(assembled, last);
            }
            assembled.push_str(")");
        }
        Expr::While(While { cond, block }) => {
            assembled.push_str("while (");
            assemble_expr(assembled, cond);
            assembled.push_str(") {\n");

            let mut inner = String::new();
            assemble_expr(&mut inner, &Expr::Block(block.clone()));
            let inner = inner
                .lines()
                .map(|line| {
                    if line.trim().is_empty() {
                        line.to_string()
                    } else {
                        // indentation
                        format!("  {}", line)
                    }
                })
                .join("\n");
            assembled.push_str(&inner);

            assembled.push_str("\n}");
        }
    }
}

fn assemble_ref(r#ref: &Ref, assembled: &mut String) {
    match r#ref {
        Ref::CommentRef(s) => {
            assembled.push_str("#");
            assembled.push_str(s);
        }
        Ref::VarRef(s) => assembled.push_str(s),
    }
}
