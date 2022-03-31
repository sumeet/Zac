use crate::interp::Value;
use hyphenation::{Language, Load, Standard};
use itertools::Itertools;
use lazy_static::lazy_static;
use pretty::{Doc, RcDoc};
use textwrap::{indent, refill, Options, WordSplitter};

lazy_static! {
    static ref WORD_SPLITTER: WordSplitter = {
        let dictionary = Standard::from_embedded(Language::EnglishUS).unwrap();
        WordSplitter::Hyphenation(dictionary)
    };
}

pub(crate) fn rewrap(s: &str) -> String {
    let mut new_comment_string = String::new();

    let comment_root = dbg!(parse_comment(s));

    for (i, node) in comment_root.children.iter().enumerate() {
        match node {
            CommentNode::Paragraph(p) => {
                let refilled = refill_paragraph(&p.iter().join("\n"), COMMENT_COLUMN_WIDTH);
                if i > 0 {
                    new_comment_string.push_str(&format!("\n\n{}", refilled));
                } else {
                    new_comment_string.push_str(&format!("{}", refilled));
                }
            }
            CommentNode::Header(header) => {
                if i > 0 {
                    let prev = comment_root.children.get(i - 1);
                    if matches!(prev, Some(CommentNode::Paragraph(_))) {
                        new_comment_string.push_str("\n");
                    }
                    new_comment_string.push_str(&format!("\n{}:", header));
                } else {
                    new_comment_string.push_str(&format!("{}:", header));
                }
            }
            CommentNode::List(items) => {
                let prev = comment_root.children.get(i - 1);
                if matches!(prev, Some(CommentNode::Header(_))) {
                    new_comment_string.push_str("\n");
                }

                let items_one_line = items.iter().join("  ");
                let s = refill_paragraph(&items_one_line, COMMENT_COLUMN_WIDTH - (INDENT_SIZE + 1));
                new_comment_string.push_str(&indent(&s, &INDENT_SPACES));
            }
        }
    }
    new_comment_string
}

fn refill_paragraph(s: &str, width: usize) -> String {
    let options = Options::new(width).word_splitter(WORD_SPLITTER.clone());
    refill(s, options)
}

fn to_doc(val: &Value) -> RcDoc<()> {
    match val {
        Value::String(s) => RcDoc::as_string(s),
        Value::Map(m) => RcDoc::text("{")
            .append(
                RcDoc::intersperse(
                    m.iter().map(|(k, v)| {
                        RcDoc::intersperse(
                            [to_doc(k), RcDoc::text("=>"), to_doc(v)].into_iter(),
                            ":",
                        )
                        .group()
                    }),
                    Doc::line(),
                )
                .nest(1)
                .group(),
            )
            .append(RcDoc::text("}")),
        Value::Int(n) => RcDoc::as_string(n),
        Value::Function(_) => RcDoc::as_string("<function>"),
        Value::Bool(b) => RcDoc::as_string(b),
        Value::List(vals) => RcDoc::text("[")
            .append(
                RcDoc::intersperse(
                    vals.iter().map(to_doc),
                    RcDoc::text(",").append(Doc::line()),
                )
                .nest(1)
                .group(),
            )
            .append(RcDoc::text("]")),
    }
}

const COLUMN_WIDTH: usize = 75;
// 3 because `//` is 2 chars and ` ` is 1
const COMMENT_COLUMN_WIDTH: usize = COLUMN_WIDTH - 3;

pub fn stringify(val: &Value) -> String {
    let mut w = Vec::new();
    to_doc(val).render(COMMENT_COLUMN_WIDTH, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

#[derive(Debug, Clone)]
struct CommentRoot {
    children: Vec<CommentNode>,
}

#[derive(Debug, Clone)]
enum CommentNode {
    Paragraph(Vec<String>),
    Header(String),
    List(Vec<String>),
}

const INDENT_SIZE: usize = 2;

lazy_static! {
    static ref INDENT_SPACES: String = " ".repeat(INDENT_SIZE);
}

fn parse_comment(s: &str) -> CommentRoot {
    let mut root = CommentRoot {
        children: Vec::new(),
    };

    let lines = s.lines().map(|s| s.to_string()).collect_vec();
    dbg!(&lines);
    let mut i = 0;

    let mut words_acc = vec![];
    let mut paragraph_acc = vec![];

    while i < lines.len() {
        let line = &lines[i];

        if line.starts_with(INDENT_SPACES.as_str()) {
            words_acc.extend(line.split_whitespace());
            i += 1;
            continue;
        } else if !words_acc.is_empty() {
            root.children.push(CommentNode::List(
                words_acc.iter().map(|s| s.to_string()).collect(),
            ));
            words_acc.clear();
        }

        if line.ends_with(':') {
            root.children
                .push(CommentNode::Header(line[..line.len() - 1].to_string()));
            i += 1;
            continue;
        }

        if line == "" {
            if !paragraph_acc.is_empty() {
                let mut clear_paragraph_acc = vec![];
                std::mem::swap(&mut clear_paragraph_acc, &mut paragraph_acc);
                root.children
                    .push(CommentNode::Paragraph(clear_paragraph_acc));
            }
            i += 1;
            continue;
        }

        paragraph_acc.push(line.to_string());
        i += 1;
    }

    if !words_acc.is_empty() {
        root.children.push(CommentNode::List(
            words_acc.iter().map(|s| s.to_string()).collect(),
        ));
    }

    root
}
