use std::collections::HashMap;

use crate::{
    ast::{Expression, Statement},
    errors::BorrowError,
};

type BorrowResult = Result<(), BorrowError>;

/// The `BorrowChecker` struct is used to keep track of the state of borrows.
pub struct BorrowChecker<'a> {
    borrows: Vec<HashMap<&'a str, BorrowState>>,
}

/// The `BorrowState` enum represents the state of a borrow.
/// It is used by the `BorrowChecker` to keep track of the borrow state.
#[derive(Debug, PartialEq)]
pub enum BorrowState {
    Uninitialized,
    Initialized,
    Borrowed,
    ImmutBorrowed,
}

impl<'a> BorrowChecker<'a> {
    /// `new` method creates a new `BorrowChecker` instance.
    ///
    /// It initializes the `BorrowChecker` with an empty hashmap.
    /// The hashmap will be used to keep track of the borrows and their states.
    pub fn new() -> Self {
        BorrowChecker {
            borrows: vec![HashMap::new()],
        }
    }
    /// `check` method will receive a statement and dispatch
    /// to the appropriate specific check method based on the `ast::Statement` variant.
    pub fn check(&mut self, stmts: &'a [Statement]) -> BorrowResult {
        match stmts {
            [] => Ok(()),
            [stmt, rest @ ..] => {
                self.check_statement(stmt)?;
                self.check(rest)
            }
        }
    }

    fn check_statement(&mut self, stmt: &'a Statement) -> BorrowResult {
        match stmt {
            Statement::VariableDecl {
                name,
                value,
                is_borrowed,
            } => self.check_variable_decl(name, value, *is_borrowed),
            Statement::FunctionDef { name, args, body } => {
                self.check_function_def(name, args, body)
            }
            Statement::Scope(stmts) => self.check_scope(stmts),
            Statement::Return(expr) => self.check_return(expr),
            Statement::Expr(expr) => self.check_expression(expr),
        }
    }
    /// `check_variable_decl` method checks a variable declaration, like `let x = 5;` or `let b = &a`.
    ///
    /// It needs to ensure that if the variable is being assigned a reference,
    /// the referenced variable isn't already borrowed mutably.
    fn check_variable_decl(
        &mut self,
        name: &'a str,
        value: &'a Option<Expression>,
        is_borrowed: bool,
    ) -> BorrowResult {
        match (is_borrowed, value) {
            (true, Some(Expression::Reference(ref ident))) => {
                if let Some(state) = self.get_borrow(ident) {
                    match state {
                        BorrowState::Borrowed | BorrowState::ImmutBorrowed => {
                            return Err(BorrowError::BorrowedMutable(ident.to_string()));
                        }
                        BorrowState::Uninitialized => {
                            return Err(BorrowError::DeclaredWithoutInitialValue(
                                ident.to_string(),
                            ));
                        }
                        _ => {}
                    }

                    self.insert_borrow(name, BorrowState::ImmutBorrowed);
                    self.insert_borrow(name, BorrowState::Initialized);

                    return Ok(());
                }

                Err(BorrowError::VariableNotDefined(ident.to_string()))
            }
            (true, _) => Err(BorrowError::VariableNotInitialized(name.to_string())),
            (false, Some(expr)) => {
                self.check_expression(expr)?;
                self.insert_borrow(name, BorrowState::Initialized);

                Ok(())
            }
            (false, None) => Err(BorrowError::DeclaredWithoutInitialValue(name.to_string())),
        }
    }

    fn check_borrowed_variable(
        &mut self,
        name: &'a str,
        value: &'a Option<Expression>,
    ) -> BorrowResult {
        if let Some(Expression::Ident(ref ident)) = value {
            if let Some(state) = self.get_borrow(ident) {
                if state == &BorrowState::Borrowed {
                    return Err(BorrowError::InvalidBorrowMutablyBorrowed(ident.to_string()));
                }

                self.insert_borrow(name, BorrowState::ImmutBorrowed);
                return Ok(());
            }

            return Err(BorrowError::VariableNotDefined(ident.to_string()));
        }

        Err(BorrowError::InvalidBorrow(name.to_string()))
    }

    fn check_value_expr(&mut self, value: &'a Option<Expression>) -> BorrowResult {
        if let Some(expr) = value {
            return self.check_expression(expr);
        }

        Ok(())
    }
    /// `check_function_def` checks a function definition.
    ///
    /// It should validate that the function params aren't violating
    /// any borrow rules.
    /// It should also call `BorrowChecker::check` on the function body,
    /// to ensure that function body is also valid.
    fn check_function_def(
        &mut self,
        _name: &'a str,
        args: &'a Option<Vec<(String, bool)>>,
        body: &'a [Statement],
    ) -> BorrowResult {
        self.borrows.push(HashMap::new());

        // check args if exists
        if let Some(args) = args {
            for (arg, is_borrowed) in args {
                if *is_borrowed {
                    self.borrow_imm(arg)?;
                }

                self.declare(arg.as_str())?;
            }
        }

        // check body of function
        let result = self.check(body);

        // release borrows
        self.borrows.pop();

        result
    }

    fn declare(&mut self, var: &'a str) -> BorrowResult {
        if let Some(scope) = self.borrows.last_mut() {
            if scope.contains_key(var) {
                return Err(BorrowError::VariableDeclaredDuplicate(var.to_string()));
            }

            scope.insert(var, BorrowState::Uninitialized);

            return Ok(());
        }

        Err(BorrowError::NoScopeAvailable(var.to_string()))
    }
    /// `check_function_call` checks a function call.
    ///
    /// It should ensure that the args passed to the function aren't
    /// violating any borrow rules.
    fn check_function_call(&mut self, _name: &str, args: &'a Vec<Expression>) -> BorrowResult {
        for arg in args {
            self.check_expression(arg)?;

            if let Expression::Ident(ident) = arg {
                if let Some(BorrowState::Borrowed) = self.get_borrow(ident) {
                    return Err(BorrowError::BorrowedMutable(ident.to_string()));
                }
            }
        }

        Ok(())
    }
    /// `check_scope` checks a scope(block of statement inside `{}`).
    ///
    /// It should call `BorrowChecker::check` on each statement inside the scope.
    fn check_scope(&mut self, body: &'a [Statement]) -> BorrowResult {
        self.borrows.push(HashMap::new());

        let result = self.check(body);

        if let Some(scope_borrows) = self.borrows.pop() {
            for borrowed in scope_borrows.keys() {
                self.free(borrowed);
            }
        }

        result
    }
    /// `check_expression` checks an expression.
    ///
    /// This is where most of the borrow checking logic will be.
    /// it should handle checking identifiers, literals and operators,
    /// ensuring that any identifiers are borrowed references, they aren't being
    /// used in a way that would violate the borrow rules.
    fn check_expression(&mut self, expr: &'a Expression) -> BorrowResult {
        match expr {
            // if the expression is a reference, check if the variable is already borrowed
            Expression::Reference(var) => {
                let borrow = self.get_borrow(var);

                if let Some(BorrowState::Borrowed) = borrow {
                    return Err(BorrowError::BorrowedMutable(var.to_string()));
                }
            }

            // if the expression is a binary operation, check the lhs and rhs
            Expression::BinaryOp { lhs, op: _, rhs } => {
                self.check_expression(lhs)?;
                self.check_expression(rhs)?;
            }

            // if the expression is an identifier, check if the variable is already borrowed
            Expression::Ident(ident) => {
                if self.get_borrow(ident).is_none() {
                    return Err(BorrowError::VariableNotInitialized(ident.to_string()));
                }
            }

            _ => {}
        }

        Ok(())
    }

    fn check_return(&mut self, expr: &'a Option<Expression>) -> BorrowResult {
        if let Some(expression) = expr {
            return self.check_expression(expression);
        }

        Ok(())
    }
    /// `borrow_mut` method should handle the logic of immutably borrowing a variable.
    ///
    /// It should ensure that the variable isn't already borrowed mutably, and then
    /// make it as immutably borrowed in the `BorrowChecker`.
    fn borrow_mut(&mut self, name: &'a str) -> BorrowResult {
        let state = self.get_borrow(name);
        if state.is_none() || state == Some(&BorrowState::Initialized) {
            self.insert_borrow(name, BorrowState::Borrowed);
            return Ok(());
        }

        Err(BorrowError::CannotBorrowMutable(name.to_string()))
    }
    /// `borrow_imm` method should handle the logic of mutably borrowing a variable.
    ///
    /// It should ensure that the variable isn't already borrowed, and then
    /// make it as mutably borrowed in the `BorrowChecker`.
    fn borrow_imm(&mut self, name: &'a str) -> BorrowResult {
        let state = self.get_borrow(name);
        if state.is_none() || state == Some(&BorrowState::Initialized) {
            self.insert_borrow(name, BorrowState::ImmutBorrowed);
            return Ok(());
        }

        Err(BorrowError::CannotBorrowImmutable(name.to_string()))
    }
    /// `free` method should handle the logic of releasing a borrow
    /// when a variable goes out of scope.
    ///
    /// It should remove the variable from the `BorrowChecker`.
    fn free(&mut self, var: &'a str) -> Option<BorrowState> {
        if !self.is_borrow_contains_key(var) {
            return None;
        }

        self.remove_borrow(var)
    }

    /// helper functions

    fn get_borrow(&mut self, var: &'a str) -> Option<&BorrowState> {
        self.borrows.last_mut().unwrap().get(var)
    }

    fn insert_borrow(&mut self, var: &'a str, state: BorrowState) -> Option<BorrowState> {
        self.borrows.last_mut().unwrap().insert(var, state)
    }

    fn remove_borrow(&mut self, var: &'a str) -> Option<BorrowState> {
        self.borrows.last_mut().unwrap().remove(var)
    }

    fn is_borrow_contains_key(&mut self, var: &'a str) -> bool {
        self.borrows.last_mut().unwrap().contains_key(var)
    }
}

#[cfg(test)]
mod borrow_tests {
    use crate::{lexer::Lexer, parser::Parser};

    use super::*;

    fn setup(input: &str) -> Vec<Statement> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().expect("Failed to tokenize");

        let mut parser = Parser::new(&tokens);

        parser.parse()
    }

    #[test]
    fn test_check_variable_decl() {
        let mut checker = BorrowChecker::new();

        let input = r#"let a = 10;"#;
        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));

        let input = r#"let a = &b;"#;
        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(
            result,
            Err(BorrowError::VariableNotDefined("b".to_string()))
        );
    }

    #[test]
    fn test_check_variable_decl_undeclared_borrow_as_parsed_form() {
        let mut checker = BorrowChecker::new();

        // let b = &a;
        let stmts = vec![Statement::VariableDecl {
            name: "b".to_string(),
            value: Some(Expression::Reference("a".to_string())),
            is_borrowed: true,
        }];

        assert!(checker.check(&stmts).is_err());
    }

    #[test]
    fn test_check_variable_decl_is_valid() {
        let input = r#"
            let a = 10;
            let b = &a;
        "#;

        let mut checker = BorrowChecker::new();

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_check_variable_decl_uninitialized() {
        let input = r#"let a;"#;

        let mut checker = BorrowChecker::new();

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(
            result,
            Err(BorrowError::DeclaredWithoutInitialValue("a".to_string()))
        );
    }

    #[test]
    fn test_check_variable_decl_with_chain_reference() {
        let input = r#"
            let a = 10;
            let b = &a;
            let c = &b;
        "#;

        let mut checker = BorrowChecker::new();

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_nested_scope_borrow_checking() {
        let mut checker = BorrowChecker::new();

        // let a = 10;
        //  {
        //    let b = &a;
        //  }
        // let c = &a;
        let stmts = vec![
            Statement::VariableDecl {
                name: "a".to_string(),
                value: Some(Expression::Number(10)),
                is_borrowed: false,
            },
            Statement::Scope(vec![Statement::VariableDecl {
                name: "b".to_string(),
                value: Some(Expression::Reference("a".to_string())),
                is_borrowed: true,
            }]),
            Statement::VariableDecl {
                name: "c".to_string(),
                value: Some(Expression::Reference("a".to_string())),
                is_borrowed: true,
            },
        ];

        assert_eq!(checker.check(&stmts), Ok(()));
    }

    #[test]
    fn test_nested_scope_with_multiple_borrows_throw_error() {
        let mut checker = BorrowChecker::new();

        let input = r#"
            let x = 5;
            {
                let y = &x;
                let z = &x;
            }
        "#;

        let result = setup(input);
        let result = checker.check(&result);

        let stmts = vec![
            Statement::VariableDecl {
                name: "x".to_string(),
                value: Some(Expression::Number(5)),
                is_borrowed: false,
            },
            Statement::Scope(vec![
                Statement::VariableDecl {
                    name: "y".to_string(),
                    value: Some(Expression::Reference("x".to_string())),
                    is_borrowed: true,
                },
                Statement::VariableDecl {
                    name: "z".to_string(),
                    value: Some(Expression::Reference("x".to_string())),
                    is_borrowed: true,
                },
            ]),
        ];

        assert_eq!(result, Err(BorrowError::BorrowedMutable("x".to_string())));
    }

    #[test]
    fn test_nested_scope_with_mut_borrow_and_use_in_same_scope() {
        let mut checker = BorrowChecker::new();
        let stmts = vec![
            Statement::VariableDecl {
                name: "x".to_string(),
                value: Some(Expression::Number(5)),
                is_borrowed: false,
            },
            Statement::Scope(vec![
                Statement::VariableDecl {
                    name: "y".to_string(),
                    value: Some(Expression::Reference("x".to_string())),
                    is_borrowed: true,
                },
                Statement::Expr(Expression::Ident("x".to_string())),
            ]),
        ];
        assert_eq!(
            checker.check(&stmts),
            Err(BorrowError::InvalidBorrowMutablyBorrowed("x".to_string())),
        );
    }

    #[test]
    fn test_nested_scope_with_uninitialized_variable() {
        let mut checker = BorrowChecker::new();
        let stmts = vec![
            Statement::VariableDecl {
                name: "x".to_string(),
                value: None,
                is_borrowed: false,
            },
            Statement::Scope(vec![Statement::VariableDecl {
                name: "y".to_string(),
                value: Some(Expression::Reference("x".to_string())),
                is_borrowed: true,
            }]),
        ];
        assert_eq!(
            checker.check(&stmts),
            Err(BorrowError::DeclaredWithoutInitialValue("x".to_string())),
        );
    }
}
