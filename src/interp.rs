use anyhow::{anyhow, bail};
use dyn_partial_eq::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::parser;
use crate::parser::{Assignment, BinOp, Block, Comment, Expr, FunctionCall, If, Op, Ref, While};
use dyn_clone::DynClone;
use itertools::Itertools;
use lazy_static::lazy_static;
use pretty::{Doc, RcDoc};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::rc::Rc;
use std::str::from_utf8;
use std::sync::Mutex;

#[derive(Debug, Clone)]
pub struct Interpreter {
    scope: Rc<RefCell<Scope>>,
    comments: Rc<RefCell<HashMap<String, String>>>,
}

const BUILTIN_COMMENTS: &[&str; 3] = &["#help", "#example-function", "#data-types"];
pub fn builtin_comment(interpreter: &Interpreter, name: &str) -> Option<String> {
    match name {
        "help" => Some(generate_help_text(interpreter)),
        "example-function" => Some(
            r#"""\
defn fib(n) {
    let a = 1
    let b = 1
    let temp = 1
    let i = 0;
    while (i < n) {
        let temp = a + b
        let a = b
        let b = temp
        i = i + 1
    }
    a
}
#"""#
                .to_string(),
        ),
        _ => None,
    }
}

lazy_static! {
    static ref BUILTIN_CONSTANTS: Mutex<HashMap<String, Value>> = {
        let mut map = HashMap::new();
        map.insert("true".to_string(), Value::Bool(true));
        map.insert("false".to_string(), Value::Bool(false));
        Mutex::new(map)
    };
}

impl Interpreter {
    pub fn new() -> Self {
        let mut scope = Scope::new(None);
        scope.insert("set".into(), Value::Function(Box::new(SetBuiltin {})));
        scope.insert("add".into(), Value::Function(Box::new(AddBuiltin {})));
        scope.insert("mul".into(), Value::Function(Box::new(MulBuiltin {})));
        scope.insert("eq".into(), Value::Function(Box::new(EqBuiltin {})));
        scope.insert("lt".into(), Value::Function(Box::new(LtBuiltin {})));
        scope.insert("gt".into(), Value::Function(Box::new(GtBuiltin {})));
        scope.insert("not".into(), Value::Function(Box::new(NotBuiltin {})));
        scope.insert("and".into(), Value::Function(Box::new(AndBuiltin {})));
        scope.insert("or".into(), Value::Function(Box::new(OrBuiltin {})));
        scope.insert("print".into(), Value::Function(Box::new(PrintBuiltin {})));
        scope.insert("show".into(), Value::Function(Box::new(ShowBuiltin {})));
        scope.insert("chr".into(), Value::Function(Box::new(ChrBuiltin {})));
        scope.insert("cat".into(), Value::Function(Box::new(CatBuiltin {})));
        BUILTIN_CONSTANTS.lock().unwrap().iter().for_each(|(k, v)| {
            scope.insert(k.clone(), v.clone());
        });

        Self {
            scope: Rc::new(RefCell::new(scope)),
            comments: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn new_scope(&self) -> Self {
        let new_scope = Scope::new(Some(Rc::clone(&self.scope)));
        let mut new_interp = self.clone();
        new_interp.scope = Rc::new(RefCell::new(new_scope));
        new_interp
    }

    pub fn comments(&self) -> Vec<(String, String)> {
        self.comments
            .borrow()
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    pub fn add_comment(&mut self, comment: &Comment) -> anyhow::Result<()> {
        if let Some(name) = &comment.name {
            let mut comments = self.comments.borrow_mut();
            if comments.contains_key(name) {
                bail!("duplicate comment: {}", name);
            }
            comments.insert(name.into(), comment.body.clone());
        }
        Ok(())
    }

    pub fn interp(&mut self, expr: &Expr) -> anyhow::Result<Value> {
        let val = match expr {
            Expr::Block(block) => {
                let mut exprs = block.exprs();
                let first = exprs.next().ok_or(anyhow!("a block can't be empty"))?;
                let mut res = self.interp(first)?;
                for expr in exprs {
                    res = self.interp(expr)?;
                }
                res
            }
            Expr::Comment(Comment { name: _, body }) => Value::String(body.into()),
            Expr::Assignment(Assignment { r#ref, expr }) => {
                let val = self.interp(expr)?;
                match r#ref {
                    Ref::CommentRef(comment_name) => {
                        let mut comments = self.comments.borrow_mut();
                        let comment = comments.get_mut(comment_name).ok_or_else(|| {
                            anyhow!("couldn't find comment with name {}", comment_name)
                        })?;
                        *comment = stringify(&val);
                    }
                    Ref::VarRef(name) => {
                        self.scope.borrow_mut().insert(name.into(), val.clone());
                    }
                }
                val
            }
            Expr::IntLiteral(n) => Value::Int(*n),
            Expr::Ref(r#ref) => self.get_ref(r#ref)?,
            // XXX:
            // this is lols but we'll use func call syntax to index into strings and maps
            // (don't have lists yet)
            Expr::FunctionCall(FunctionCall { r#ref, args }) => {
                let var = self.get_ref(r#ref)?;
                let args = args
                    .iter()
                    .map(|e| self.interp(e))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                match var {
                    Value::Function(func) => func.call(self, &args)?,
                    Value::String(s) => {
                        let index = get_arg(&args, 0)?.as_num()?;
                        if index < 0 {
                            Value::Bool(false)
                        } else {
                            s.chars()
                                .nth(index as usize)
                                .map(|c| Value::String(c.into()))
                                .unwrap_or(Value::Bool(false))
                        }
                    }
                    Value::Map(map) => {
                        let key = get_arg(&args, 0)?;
                        map.get(key).cloned().unwrap_or(Value::Bool(false))
                    }
                    Value::Bool(_) | Value::Int(_) => {
                        bail!("tried to call a {:?}", var)
                    }
                    Value::List(vals) => {
                        let index = get_arg(&args, 0)?.as_num()?;
                        vals.get(index as usize)
                            .cloned()
                            .unwrap_or(Value::Bool(false))
                    }
                }
            }
            Expr::While(While { cond, block }) => {
                // TODO: need to make aa new scope for a new block
                let mut count = 0;
                while self.interp(cond)?.as_bool()? {
                    self.interp(&Expr::Block(block.clone()))?;
                    count += 1;
                }
                Value::Int(count)
            }
            Expr::If(If { cond, block }) => {
                // TODO: need to make aa new scope for a new block
                let b = self.interp(cond)?.as_bool()?;
                if b {
                    self.interp(&Expr::Block(block.clone()))?;
                }
                Value::Bool(b)
            }
            Expr::FuncDef(func_def) => {
                let val = Value::Function(Box::new(FuncDef::from_expr(func_def.clone())));
                self.scope
                    .borrow_mut()
                    .insert(func_def.name.clone(), val.clone());
                val
            }
            Expr::ListLiteral(exprs) => Value::List(
                exprs
                    .iter()
                    .map(|expr| self.interp(expr))
                    .collect::<anyhow::Result<Vec<_>>>()?,
            ),
            Expr::BinOp(BinOp { op, lhs, rhs }) => self.eval_bin_op(lhs, *op, rhs)?,
        };
        Ok(val)
    }

    fn eval_bin_op(&mut self, lhs: &Box<Expr>, op: Op, rhs: &Box<Expr>) -> anyhow::Result<Value> {
        Ok(match op {
            Op::Add => {
                let lhs = self.interp(lhs)?;
                let rhs = self.interp(rhs)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l + r),
                    (Value::String(l), Value::String(r)) => Value::String(l + &r),
                    (Value::List(l), Value::List(r)) => {
                        Value::List(l.into_iter().chain(r).collect())
                    }
                    (Value::Map(l), Value::Map(r)) => Value::Map(l.into_iter().chain(r).collect()),
                    (Value::Bool(l), Value::Bool(r)) => Value::Bool(l || r),
                    (l, r) => bail!("can't add {:?} and {:?}", l, r),
                }
            }
            Op::Sub => todo!(),
            Op::Div => todo!(),
            Op::Mul => todo!(),
            Op::Eq => todo!(),
            Op::Neq => todo!(),
            Op::Gte => todo!(),
            Op::Gt => todo!(),
            Op::Lte => todo!(),
            Op::Lt => todo!(),
            Op::And => todo!(),
            Op::Or => todo!(),
        })
    }

    // TODO: this should probably be a refcell
    fn get_ref(&self, r#ref: &Ref) -> anyhow::Result<Value> {
        match r#ref {
            Ref::CommentRef(name) => {
                let comment_body = self
                    .comments
                    .borrow()
                    .get(name)
                    .ok_or_else(|| anyhow!("undefined comment {}", name))?
                    .clone();
                Ok(Value::String(comment_body))
            }
            Ref::VarRef(name) => self
                .scope
                .borrow()
                .get(name)
                .ok_or_else(|| anyhow!("undefined name {}", name))
                .map(|val| val.clone()),
        }
    }
}

#[derive(Debug)]
struct Scope {
    prev: Option<Rc<RefCell<Scope>>>,
    this: BTreeMap<String, Value>,
}

impl Scope {
    fn new(prev: Option<Rc<RefCell<Scope>>>) -> Self {
        Self {
            prev,
            this: Default::default(),
        }
    }

    pub fn insert(&mut self, name: String, val: Value) {
        self.this.insert(name, val);
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        if let Some(val) = self.this.get(name) {
            return Some(val.clone());
        }

        self.prev
            .as_ref()
            .and_then(|scope| scope.borrow().get(name))
    }
}

#[dyn_partial_eq]
pub trait Function: Debug + DynClone + Send {
    fn call(&self, interp: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value>;
}

dyn_clone::clone_trait_object!(Function);

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    String(String),
    Map(BTreeMap<Value, Value>),
    Int(i128),
    Function(Box<dyn Function>),
    Bool(bool),
    List(Vec<Value>),
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

const PRETTY_PRINT_COLUMN_WIDTH: usize = 75;

fn stringify(val: &Value) -> String {
    let mut w = Vec::new();
    to_doc(val)
        .render(PRETTY_PRINT_COLUMN_WIDTH, &mut w)
        .unwrap();
    String::from_utf8(w).unwrap()
}

impl Eq for Value {}

impl PartialOrd<Self> for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a.partial_cmp(b),
            (Value::String(a), Value::String(b)) => a.partial_cmp(b),
            (Value::Bool(a), Value::Bool(b)) => a.partial_cmp(b),
            (Value::List(a), Value::List(b)) => a.partial_cmp(b),
            (Value::Map(a), Value::Map(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a.cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::List(a), Value::List(b)) => a.cmp(b),
            (Value::Map(a), Value::Map(b)) => a.cmp(b),
            _ => Ordering::Less,
        }
    }
}

#[derive(Debug, Clone, PartialEq, DynPartialEq)]
struct FuncDef {
    block: Block,
    arg_names: Vec<String>,
}

impl FuncDef {
    fn from_expr(func_def: parser::FuncDef) -> Self {
        Self {
            block: func_def.block,
            arg_names: func_def.arg_names,
        }
    }
}

impl Function for FuncDef {
    fn call(&self, interp: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let mut new_interp = interp.new_scope();
        for (name, val) in self.arg_names.iter().zip(args) {
            new_interp
                .scope
                .borrow_mut()
                .insert(name.to_owned(), val.clone());
        }
        new_interp.interp(&Expr::Block(self.block.clone()))
    }
}

impl Value {
    fn as_func(&self) -> anyhow::Result<&dyn Function> {
        match self {
            Value::Function(f) => Ok(f.as_ref()),
            otherwise => bail!("{:?} is not a function", otherwise),
        }
    }

    fn as_num(&self) -> anyhow::Result<i128> {
        match self {
            Value::Int(i) => Ok(*i),
            otherwise => bail!("{:?} is not an integer", otherwise),
        }
    }

    fn as_bool(&self) -> anyhow::Result<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            otherwise => bail!("{:?} is not a bool", otherwise),
        }
    }

    fn as_str(&self) -> anyhow::Result<&str> {
        match self {
            Value::String(s) => Ok(s),
            otherwise => bail!("{:?} is not a String", otherwise),
        }
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct SetBuiltin {}
impl Function for SetBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let str = get_arg(args, 0)?.as_str()?;
        let index = get_arg(args, 1)?.as_num()?;
        let new = get_arg(args, 2)?.as_str()?;
        let (left, right) = str.split_at(index as usize);
        Ok(Value::String(format!("{}{}{}", left, new, &right[1..])))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct AddBuiltin {}
impl Function for AddBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_num()?;
        let rhs = get_arg(args, 1)?.as_num()?;
        Ok(Value::Int(lhs + rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct MulBuiltin {}
impl Function for MulBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_num()?;
        let rhs = get_arg(args, 1)?.as_num()?;
        Ok(Value::Int(lhs * rhs))
    }
}

fn get_arg(args: &[Value], n: usize) -> anyhow::Result<&Value> {
    args.get(n).ok_or_else(|| {
        anyhow!(
            "not enough arguments, was looking for {} but only {} were provided",
            n,
            args.len()
        )
    })
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct EqBuiltin {}
impl Function for EqBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?;
        let rhs = get_arg(args, 1)?;
        Ok(Value::Bool(lhs == rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct GtBuiltin {}
impl Function for GtBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_num()?;
        let rhs = get_arg(args, 1)?.as_num()?;
        Ok(Value::Bool(lhs > rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct LtBuiltin {}
impl Function for LtBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_num()?;
        let rhs = get_arg(args, 1)?.as_num()?;
        //println!("{:?} < {:?}", lhs, rhs);
        Ok(Value::Bool(lhs < rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct NotBuiltin {}
impl Function for NotBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?.as_bool()?;
        Ok(Value::Bool(!val))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct AndBuiltin {}
impl Function for AndBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_bool()?;
        let rhs = get_arg(args, 1)?.as_bool()?;
        Ok(Value::Bool(lhs && rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct OrBuiltin {}
impl Function for OrBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_bool()?;
        let rhs = get_arg(args, 1)?.as_bool()?;
        Ok(Value::Bool(lhs || rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct PrintBuiltin {}
impl Function for PrintBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?;
        println!("{:?}", val);
        Ok(val.clone())
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct CatBuiltin {}
impl Function for CatBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let mut acc = String::new();
        for arg in args {
            let str = arg.as_str()?;
            acc.push_str(str);
        }
        Ok(Value::String(acc))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct ChrBuiltin {}
impl Function for ChrBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?.as_num()?.to_le_bytes()[0];
        Ok(Value::String(from_utf8(&[val])?.to_string()))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct ShowBuiltin {}
impl Function for ShowBuiltin {
    fn call(&self, _: &mut Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?;
        Ok(Value::String(stringify(val)))
    }
}

const WELCOME_TEXT: &str = r#"Help for the Zac Programming Language (https://github.com/sumeet/Zac)

Define a comment with the first line set to an identifier (like #help) and it
will be a string usable inside of your program. You can read from it, and if
you write to it, the change will be reflected inside the source file."#;

fn generate_help_text(interp: &Interpreter) -> String {
    let mut function_names = vec![];
    let mut variable_names = vec![];
    for (name, builtin) in &interp.scope.borrow().this {
        if builtin.as_func().is_ok() {
            function_names.push(name.to_string());
        } else {
            variable_names.push(name.to_string())
        }
    }
    let mut comment_names = BTreeSet::new();
    for comment in BUILTIN_COMMENTS {
        comment_names.insert(comment.to_string());
    }
    for comment in interp.comments.borrow().keys() {
        comment_names.insert(format!("#{}", comment));
    }

    let mut txt = String::new();
    txt.push_str(WELCOME_TEXT);
    txt.push_str("\n\nBuiltin functions:\n");
    txt.push_str(&tableize(&function_names));
    txt.push_str("\nAvailable variables\n");
    txt.push_str(&tableize(&variable_names));
    txt.push_str("\nAvailable comments\n");
    txt.push_str(&tableize(&comment_names.into_iter().collect_vec()).to_string());
    txt.trim_end().into()
}

fn tableize(function_names: &[String]) -> String {
    format!("  {}", function_names.iter().join("  "))
}
