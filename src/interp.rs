use anyhow::{anyhow, bail};
use dyn_partial_eq::*;
use std::collections::{BTreeMap, HashMap};

use crate::parser::{Assignment, Comment, Expr, FunctionCall, If, Ref, While};
use dyn_clone::DynClone;
use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

#[derive(Debug)]
pub struct Interpreter {
    scope: Rc<RefCell<Scope>>,
    comments: HashMap<String, String>,
}

impl Interpreter {
    pub fn new() -> Self {
        let mut scope = Scope::new();
        let map = &mut scope.0;
        map.insert("add".into(), Value::Function(Box::new(AddBuiltin {})));
        map.insert("eq".into(), Value::Function(Box::new(EqBuiltin {})));
        map.insert("not".into(), Value::Function(Box::new(NotBuiltin {})));
        map.insert("print".into(), Value::Function(Box::new(PrintBuiltin {})));
        map.insert("show".into(), Value::Function(Box::new(ShowBuiltin {})));
        map.insert("cat".into(), Value::Function(Box::new(CatBuiltin {})));
        map.insert("true".into(), Value::Bool(true));
        map.insert("false".into(), Value::Bool(false));
        Self {
            scope: Rc::new(RefCell::new(scope)),
            comments: HashMap::new(),
        }
    }

    pub fn comments(&self) -> impl Iterator<Item = (&str, &str)> {
        self.comments.iter().map(|(k, v)| (k.as_str(), v.as_str()))
    }

    pub fn add_comment(&mut self, comment: &Comment) -> anyhow::Result<()> {
        if let Some(name) = &comment.name {
            if self.comments.contains_key(name) {
                bail!("duplicate comment: {}", name);
            }
            self.comments.insert(name.into(), comment.body.clone());
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
                        let comment = self.comments.get_mut(comment_name).ok_or_else(|| {
                            anyhow!("couldn't find comment with name {}", comment_name)
                        })?;
                        *comment = val.as_str()?.into();
                    }
                    Ref::VarRef(name) => {
                        self.scope.borrow_mut().0.insert(name.into(), val.clone());
                    }
                }
                val
            }
            Expr::IntLiteral(n) => Value::Int(*n),
            Expr::Ref(r#ref) => self.get_ref(r#ref)?,
            Expr::FunctionCall(FunctionCall { r#ref, args }) => {
                let var = self.get_ref(r#ref)?;
                let func = var.as_func()?;
                let args = args
                    .iter()
                    .map(|e| self.interp(e))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                func.call(self, &args)?
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
        };
        Ok(val)
    }

    // TODO: this should probably be a refcell
    fn get_ref(&self, r#ref: &Ref) -> anyhow::Result<Value> {
        match r#ref {
            Ref::CommentRef(name) => {
                let comment_body = self
                    .comments
                    .get(name)
                    .ok_or_else(|| anyhow!("undefined comment {}", name))?;
                Ok(Value::String(comment_body.clone()))
            }
            Ref::VarRef(name) => self
                .scope
                .borrow()
                .0
                .get(name)
                .ok_or_else(|| anyhow!("undefined name {}", name))
                .map(|val| val.clone()),
        }
    }
}

#[derive(Debug)]
struct Scope(BTreeMap<String, Value>);

impl Scope {
    fn new() -> Self {
        Self(BTreeMap::new())
    }
}

#[dyn_partial_eq]
pub trait Function: Debug + DynClone {
    fn call(&self, interp: &Interpreter, args: &[Value]) -> anyhow::Result<Value>;
}

dyn_clone::clone_trait_object!(Function);

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    String(String),
    Map(BTreeMap<Value, Value>),
    Int(i128),
    Function(Box<dyn Function>),
    Bool(bool),
}

impl Value {
    fn as_func(&self) -> anyhow::Result<&dyn Function> {
        match self {
            Value::Function(func) => Ok(func.as_ref()),
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
struct AddBuiltin {}
impl Function for AddBuiltin {
    fn call(&self, _: &Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?.as_num()?;
        let rhs = get_arg(args, 1)?.as_num()?;
        Ok(Value::Int(lhs + rhs))
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
    fn call(&self, _: &Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let lhs = get_arg(args, 0)?;
        let rhs = get_arg(args, 1)?;
        Ok(Value::Bool(lhs == rhs))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct NotBuiltin {}
impl Function for NotBuiltin {
    fn call(&self, _: &Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?.as_bool()?;
        Ok(Value::Bool(!val))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct PrintBuiltin {}
impl Function for PrintBuiltin {
    fn call(&self, _: &Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?;
        println!("{:?}", val);
        Ok(val.clone())
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct CatBuiltin {}
impl Function for CatBuiltin {
    fn call(&self, _: &Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let mut acc = String::new();
        for arg in args {
            let str = arg.as_str()?;
            acc.push_str(str);
        }
        Ok(Value::String(acc))
    }
}

#[derive(Debug, Clone, DynPartialEq, PartialEq)]
struct ShowBuiltin {}
impl Function for ShowBuiltin {
    fn call(&self, _: &Interpreter, args: &[Value]) -> anyhow::Result<Value> {
        let val = get_arg(args, 0)?;
        let s = match val {
            Value::String(s) => s.clone(),
            Value::Map(m) => format!("{:?}", m),
            Value::Int(n) => n.to_string(),
            Value::Function(_) => "<function>".to_string(),
            Value::Bool(true) => "true".to_string(),
            Value::Bool(false) => "false".to_string(),
        };
        Ok(Value::String(s))
    }
}
