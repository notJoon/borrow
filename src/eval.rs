use std::collections::HashMap;

use crate::ast::{BinaryOp, Expression, Statement};

/// The `Evaluator` struct will store the state of the program during evaluation.
///
/// This includes the global env, which keeps track of all the global variables,
/// and the local env stack, which keeps track of all the local variables.
pub struct Evaluator<'a> {
    /// The global env maps variable names to their values
    global_env: HashMap<String, i32>,
    /// A stack of local envs for nested scopes
    local_env: Vec<HashMap<String, i32>>,
    /// The function env maps function names to their arguments and body
    functions: HashMap<String, (Vec<(String, bool)>, &'a Vec<Statement>)>,
}

impl<'a> Evaluator<'a> {
    /// The constructor initializes an evaluator
    /// with an empty global environment and one empty local environment.
    pub fn new() -> Self {
        Evaluator {
            global_env: HashMap::new(),
            local_env: vec![HashMap::new()],
            functions: HashMap::new(),
        }
    }

    /// The evaluate method takes a list of statements (the program),
    /// and evaluates each statement in turn.
    ///
    /// It returns the value of the last statement if exists.
    pub fn evaluate(&mut self, stmts: &'a[Statement]) -> Result<Option<i32>, String> {
        for stmt in stmts {
            self.evaluate_stmt(stmt)?;
        }

        Ok(Some(0)) // return `0` after successfully evaluating all statements
    }

    /// `evaluate_stmt` evaluates a single statement.
    ///
    /// It dispatches to the appropriate handler method based on the type of statement.
    fn evaluate_stmt(&mut self, stmt: &'a Statement) -> Result<Option<i32>, String> {
        match stmt {
            // For variable declarations, evaluate the value (if any), then insert it into the current scope.
            Statement::VariableDecl { name, value, .. } => {
                let value = match value {
                    Some(value) => self.evaluate_expr(value)?,
                    None => 0, // default value is `0`
                };

                self.insert_global(name.clone(), value);

                Ok(None)
            }
            Statement::FunctionDef { name, args, body } => {
                self.functions.insert(name.clone(), (args.clone().unwrap(), body));

                Ok(None)
            }
            // For scope statements, create a new local environment, evaluate all statements
            // within the scope, then discard the local environment.
            Statement::Scope(stmts) => {
                self.local_env.push(HashMap::new()); // Create a new local environment.

                for stmt in stmts {
                    self.evaluate_stmt(stmt)?;
                }

                self.local_env.pop(); // Discard the local environment after exiting the scope.

                Ok(None)
            }
            Statement::Return(expr) => {
                let value = match expr {
                    Some(expr) => self.evaluate_expr(expr)?,
                    None => 0
                };

                Err(format!("return value: {:?}", value))
            }
            Statement::Expr(expr) => {
                self.evaluate_expr(expr)?;

                Ok(None)
            }
        }
    }

    // `evaluate_expr` evaluates an expression and returns its value.
    // It handles identifiers, numbers, and binary operations.
    fn evaluate_expr(&self, expr: &Expression) -> Result<i32, String> {
        match expr {
            // For identifiers, look them up in the current scope, then in the global scope.
            Expression::Ident(name) => {
                for env in self.local_env.iter().rev() {
                    if let Some(value) = env.get(name) {
                        return Ok(*value);
                    }
                }

                // If the identifier is not found in any local scope, look it up in the global scope.
                self.global_env.get(name).copied().ok_or(format!(
                    "undefined variable `{}` not found (evaluating expression)",
                    name
                ))
            }
            // Numbers are returned as is.
            Expression::Number(value) => Ok(*value),
            // Binary operations are evaluated by recursively evaluating the left and right sides,
            // then applying the operator to the results.
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

    fn evaluate_function_call(&mut self, name: &String, args: &'a [Expression]) -> Result<Option<i32>, String> {
        if let Some((params, body)) = self.functions.get(name) {
            if params.len() != args.len() {
                return Err(format!("Wrong number of arguments for function {name}, expected {}, got {}", params.len(), args.len()));
            }

            self.local_env.push(HashMap::new());

            for ((param_name, _), arg) in params.iter().zip(args) {
                let arg_value = self.evaluate_expr(arg)?;
                self.local_env.last_mut().unwrap().insert(param_name.clone(), arg_value);
            }

            let mut ret_result = None;
            for stmt in *body {
                match self.evaluate_stmt(stmt)? {
                    Some(value) => {
                        ret_result = Some(value);
                        break;
                    }
                    _ => {}
                }
            }

            self.local_env.pop();

            return Ok(ret_result);
        }

        Err(format!("Function `{}` not found", name))
    }

    /// insert_global inserts a new variable into the global environment.
    fn insert_global(&mut self, name: String, value: i32) -> Option<i32> {
        self.global_env.insert(name, value)
    }
}

#[cfg(test)]
mod eval_test {
    use super::*;
    use crate::{lexer::Lexer, token::TokenType, parser::Parser};

    fn setup(input: &str) -> Vec<TokenType> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().expect("Failed to tokenize");

        tokens
    }

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

        assert_eq!(result, Ok(Some(0)));
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
            },
        ];

        let result = eval.evaluate(&stmts);

        assert_eq!(result, Ok(Some(0)));
        assert_eq!(eval.global_env.get("x"), Some(&5));
        assert_eq!(eval.global_env.get("y"), Some(&15));
    }

    #[test]
    fn test_function_definition_and_call() {
        let mut eval = Evaluator::new();

        let input = r#"
            function add(x, y) {
                return x + y;
            }

            let result = add(5, 10);
        "#;

        let tokens = setup(input);

        println!("tokens: {:?}", tokens);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        let result = eval.evaluate(&stmts);

        assert_eq!(result, Ok(Some(0)));
        assert_eq!(eval.global_env.get("result"), Some(&15));
    }
}
