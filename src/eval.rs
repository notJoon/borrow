use std::collections::HashMap;

use crate::ast::{Statement, Expression, BinaryOp};

pub struct Evaluator {
    global_env: HashMap<String, i32>,
    local_env: Vec<HashMap<String, i32>>,
}

impl Evaluator {
    pub fn new() -> Self {
        Evaluator { 
            global_env: HashMap::new(), 
            local_env: vec![HashMap::new()] 
        }
    }

    pub fn evaluate(&mut self, stmts: &[Statement]) -> Result<i32, String> {
        for stmt in stmts {
            self.evaluate_stmt(stmt)?;
        }

        Ok(0)
    }

    fn evaluate_stmt(&mut self, stmt: &Statement) -> Result<(), String> {
        match stmt {
            Statement::VariableDecl { name, value, .. } => {
                let value = match value {
                    Some(value) => self.evaluate_expr(value)?,
                    None => 0,
                };

                self.global_env.insert(name.clone(), value);

                Ok(())
            }
            Statement::FunctionDef { .. } => {
                // we are not evaluate function definition at runtime
                Ok(())
            }
            Statement::FunctionCall { .. } =>  {
                unimplemented!("Evaluator::evaluate_stmt: FunctionCall")
            }
            Statement::Scope(stmts) => {
                self.local_env.push(HashMap::new());

                for stmt in stmts {
                    self.evaluate_stmt(stmt)?;
                }

                self.local_env.pop();

                Ok(())
            }
            Statement::Return(expr) => {
                unimplemented!("Evaluator::evaluate_stmt: Return")
            }
        }
    }

    fn evaluate_expr(&self, expr: &Expression) -> Result<i32, String> {
        match expr {
            Expression::Ident(name) => {
                for env in self.local_env.iter().rev() {
                    if let Some(value) = env.get(name) {
                        return Ok(*value);
                    }
                }

                self.global_env.get(name).copied().ok_or(format!(
                    "undefined variable `{}` not found (evaluating expression)",
                    name
                ))
            }
            Expression::Number(value) => {
                Ok(*value)
            },
            Expression::BinaryOp { lhs, op, rhs } => {
                let lhs = self.evaluate_expr(lhs)?;
                let rhs = self.evaluate_expr(rhs)?;

                match op {
                    BinaryOp::Plus => Ok(lhs + rhs),
                    BinaryOp::Minus => Ok(lhs - rhs),
                    BinaryOp::Asterisk => Ok(lhs * rhs),
                    BinaryOp::Slash => Ok(lhs / rhs),
                }
            }
            _ => Err(format!("invalid or unsupported expression: {:?}", expr)),
        }
    }
}

#[cfg(test)]
mod eval_test {
    use super::*;

    #[test]
    fn test_variable_declaration() {
        let mut eval = Evaluator::new();

        // let x = 5;
        // let y = 10;
        let stmts = vec![
            Statement::VariableDecl { 
                name: "x".to_string(), 
                value: Some(Expression::Number(5)), 
                is_borrowed: false, 
            },
            Statement::VariableDecl { 
                name: "y".to_string(), 
                value: Some(Expression::Number(10)), 
                is_borrowed: false, 
            },
        ];

        let result = eval.evaluate(&stmts);

        assert_eq!(result, Ok(0));
        assert_eq!(eval.global_env.get("x"), Some(&5));
        assert_eq!(eval.global_env.get("y"), Some(&10));
    }

    #[test]
    fn test_eval_add() {
        let mut eval = Evaluator::new();

        let stmts = vec![
            Statement::VariableDecl { 
                name: "x".to_string(), 
                value: Some(Expression::Number(5)),
                is_borrowed: false, 
            },
            Statement::VariableDecl { 
                name: "y".to_string(),
                value: Some(Expression::BinaryOp { 
                    lhs: Box::new(Expression::Ident("x".to_string())),
                    op: BinaryOp::Plus, 
                    rhs: Box::new(Expression::Number(10)), 
                }), 
                is_borrowed: false,
            }
        ];

        let result = eval.evaluate(&stmts);

        assert_eq!(result, Ok(0));
        assert_eq!(eval.global_env.get("x"), Some(&5));
        assert_eq!(eval.global_env.get("y"), Some(&15));
    }
}