use crate::parser::{
    Assignment, BinOp, Block, BlockEl, Comment, Expr, FuncDef, FunctionCall, If, Op, Program, Ref,
    While,
};
use crate::{wrapping, Interpreter};
use itertools::Itertools;
use std::fmt::Write;

pub fn output_code(program: &Program, interp: &Interpreter) -> String {
    let mut assembled = String::new();
    assemble_expr(&mut assembled, &Expr::Block(program.block.clone()), interp);
    assembled
}

fn assemble_expr(assembled: &mut String, expr: &Expr, interp: &Interpreter) {
    match expr {
        Expr::Block(block) => {
            for block_el in &block.0 {
                match block_el {
                    BlockEl::Expr(expr) => {
                        assemble_expr(assembled, expr, interp);
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

                assembled.push_str("\n");
            }

            if body.is_empty() {
                assembled.push_str("//");
                return;
            }

            let mut lines = body.split("\n").peekable();
            while let Some(line) = lines.next() {
                assembled.push_str("//");
                if !line.is_empty() {
                    assembled.push_str(" ");
                    assembled.push_str(line);
                }

                if let Some(_) = lines.peek() {
                    assembled.push_str("\n");
                }
            }
        }
        Expr::Assignment(Assignment { r#ref, expr }) => {
            assembled.push_str("let ");
            assemble_ref(r#ref, assembled);
            assembled.push_str(" = ");
            assemble_expr(assembled, expr, interp);
        }
        Expr::IntLiteral(n) => assembled.push_str(&n.to_string()),
        Expr::Ref(r#ref) => assemble_ref(r#ref, assembled),
        Expr::FunctionCall(FunctionCall { r#ref, args }) => {
            assemble_ref(r#ref, assembled);
            assembled.push_str("(");
            if let Some((last, init)) = args.split_last() {
                for arg in init {
                    assemble_expr(assembled, arg, interp);
                    assembled.push_str(", ");
                }
                assemble_expr(assembled, last, interp);
            }
            assembled.push_str(")");
        }
        e @ (Expr::While(While { cond, block }) | Expr::If(If { cond, block })) => {
            assembled.push_str(match e {
                Expr::While(_) => "while (",
                Expr::If(_) => "if (",
                _ => unreachable!(),
            });
            assemble_expr(assembled, cond, interp);
            assembled.push_str(") {\n");
            assemble_inner_block(assembled, block, interp);
            assembled.push_str("\n}");
        }
        Expr::FuncDef(FuncDef {
            name,
            arg_names,
            block,
        }) => {
            assembled.push_str("defn ");
            assembled.push_str(name);
            assembled.push_str("(");
            if let Some((last, init)) = arg_names.split_last() {
                for arg_name in init {
                    assembled.push_str(arg_name);
                    assembled.push_str(", ");
                }
                assembled.push_str(last);
            }
            assembled.push_str(") {\n");
            assemble_inner_block(assembled, block, interp);
            assembled.push_str("\n}");
        }
        Expr::ListLiteral(list) => {
            assembled.push_str("[");
            if let Some((last, init)) = list.split_last() {
                for item in init {
                    assemble_expr(assembled, item, interp);
                    assembled.push_str(", ");
                }
                assemble_expr(assembled, last, interp);
            }
            assembled.push_str("]");
        }
        Expr::BinOp(BinOp { op, lhs, rhs }) => {
            assemble_expr(assembled, lhs, interp);
            assembled.push_str(match op {
                Op::Add => " + ",
                Op::Sub => " - ",
                Op::Mul => " * ",
                Op::Div => " / ",
                Op::Eq => " == ",
                Op::Neq => " != ",
                Op::Lt => " < ",
                Op::Gt => " > ",
                Op::Lte => " <= ",
                Op::Gte => " >= ",
                Op::And => " && ",
                Op::Or => " || ",
            });
            assemble_expr(assembled, rhs, interp);
        }
        Expr::StringLiteral(s) => {
            write!(assembled, "{:?}", s.as_str()).unwrap();
        }
        Expr::ResultComment(id, expr) => {
            assemble_expr(assembled, expr, interp);
            assembled.push_str(" // #");
            let result_comments = interp.result_comments.borrow();
            if let Some(value) = result_comments.get(id) {
                let comment = wrapping::stringify(value);
                let lines = comment.lines().collect_vec();
                if let Some((first, rest)) = lines.split_first() {
                    assembled.push_str(first);
                    if !rest.is_empty() {
                        for line in rest {
                            assembled.push_str("\n");
                            assembled.push_str("// ");
                            assembled.push_str(line);
                        }
                    }
                }
            }
        }
    }
}

fn assemble_inner_block(assembled: &mut String, block: &Block, interp: &Interpreter) {
    let mut inner = String::new();
    assemble_expr(&mut inner, &Expr::Block(block.clone()), interp);
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
