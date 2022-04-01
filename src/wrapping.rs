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

    let comment_root = parse_comment(s);

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
            CommentNode::Pre(text) => {
                if i > 0 {
                    new_comment_string.push_str("\n");
                }
                new_comment_string.push_str(&format!("` {}", text));
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
    Pre(String),
}

const INDENT_SIZE: usize = 2;

lazy_static! {
    static ref INDENT_SPACES: String = " ".repeat(INDENT_SIZE);
}

struct CommentParser {
    root: CommentRoot,
    list_acc: Vec<String>,
    paragraph_acc: Vec<String>,
}

impl CommentParser {
    fn new() -> Self {
        Self {
            list_acc: vec![],
            paragraph_acc: vec![],
            root: CommentRoot { children: vec![] },
        }
    }

    fn push_node(&mut self, node: CommentNode) {
        if !matches!(node, CommentNode::Paragraph(_)) {
            self.flush_paragraph();
        }
        if !matches!(node, CommentNode::List(_)) {
            self.flush_list();
        }

        match node {
            CommentNode::Paragraph(p) => self.paragraph_acc.extend(p),
            CommentNode::Header(h) => self.root.children.push(CommentNode::Header(h)),
            CommentNode::List(l) => self.list_acc.extend(l),
            CommentNode::Pre(p) => self.root.children.push(CommentNode::Pre(p)),
        }
    }

    fn flush_all(&mut self) {
        self.flush_paragraph();
        self.flush_list();
    }

    fn flush_paragraph(&mut self) {
        if !self.paragraph_acc.is_empty() {
            let mut clear_paragraph_acc = vec![];
            std::mem::swap(&mut clear_paragraph_acc, &mut self.paragraph_acc);
            self.root
                .children
                .push(CommentNode::Paragraph(clear_paragraph_acc));
        }
    }

    fn flush_list(&mut self) {
        if !self.list_acc.is_empty() {
            let mut clear_list_acc = vec![];
            std::mem::swap(&mut clear_list_acc, &mut self.list_acc);
            self.root.children.push(CommentNode::List(clear_list_acc));
        }
    }

    fn parse(mut self, s: &str) -> CommentRoot {
        for line in s.lines() {
            if line.starts_with("` ") {
                self.push_node(CommentNode::Pre(line[2..].to_string()));
            } else if line.starts_with(INDENT_SPACES.as_str()) {
                self.push_node(CommentNode::List(
                    line.split_whitespace().map(|s| s.to_string()).collect(),
                ));
            } else if line.ends_with(':') {
                self.push_node(CommentNode::Header(line[..line.len() - 1].to_string()));
            } else if line == "" {
                self.flush_all();
            } else {
                self.push_node(CommentNode::Paragraph(vec![line.to_string()]));
            }
        }
        self.flush_all();
        self.root
    }
}

fn parse_comment(s: &str) -> CommentRoot {
    CommentParser::new().parse(s)
}
