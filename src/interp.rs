use anyhow::{anyhow, bail};
use dyn_partial_eq::*;
use std::collections::BTreeMap;

use crate::parser::{Assignment, Expr, FunctionCall};
use dyn_clone::DynClone;
use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

#[derive(Debug)]
pub struct Interpreter {
    scope: Rc<RefCell<Scope>>,
}

impl Interpreter {
    pub fn new() -> Self {
        let mut scope = Scope::new();
        scope
            .0
            .insert("add".into(), Value::Function(Box::new(AddBuiltin {})));
        scope
            .0
            .insert("eq".into(), Value::Function(Box::new(EqBuiltin {})));
        Self {
            scope: Rc::new(RefCell::new(scope)),
        }
    }

    pub fn interp(&self, expr: &Expr) -> anyhow::Result<Value> {
        let val = match expr {
            Expr::Comment(s) => Value::String(s.into()),
            Expr::Assignment(Assignment { name, expr }) => {
                let val = self.interp(expr)?;
                self.scope.borrow_mut().0.insert(name.into(), val.clone());
                val
            }
            Expr::IntLiteral(n) => Value::Int(*n),
            Expr::Ref(name) => self.get_ref(name)?,
            Expr::FunctionCall(FunctionCall { name, args }) => {
                let var = self.get_ref(name)?;
                let func = var.as_func()?;
                let args = args
                    .iter()
                    .map(|e| self.interp(e))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                func.call(self, &args)?
            }
        };
        Ok(val)
    }

    // TODO: this should probably be a refcell
    fn get_ref(&self, name: &str) -> anyhow::Result<Value> {
        self.scope
            .borrow()
            .0
            .get(name)
            .ok_or_else(|| anyhow!("undefined name {}", name))
            .map(|val| val.clone())
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
