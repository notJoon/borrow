use std::collections::HashMap;

use crate::ast::{Expression, Statement};

type BorrowResult = Result<(), String>;

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
            Statement::FunctionCall { name, args } => self.check_function_call(name, args),
            Statement::Scope(stmts) => self.check_scope(stmts),
            _ => Ok(()), // for other types of statements, we do nothing for now
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
            (true, Some(Expression::Ident(ref ident))) => {
                if let Some(state) = self.get_borrow(ident) {
                    match state {
                        BorrowState::Borrowed => {
                            return Err(format!(
                                "Cannot borrow `{ident}` as it is currently being mutably borrowed"
                            ));
                        }
                        BorrowState::Uninitialized => {
                            return Err(format!("Variable `{ident}` is not initialized"));
                        }
                        _ => {}
                    }

                    self.insert_borrow(name, BorrowState::ImmutBorrowed);
                    return Ok(());
                }

                return Err(format!("Variable `{ident}` is not initialized"));
            }

            // TODO
            (true, _) => return Err(format!("Variable `{name}` is not initialized")),

            // when the variable is not borrowed, check the value is initialized
            // and insert the variable into the borrow checker
            (false, expr) => {
                if let Some(expr) = expr {
                    return self.check_expression(expr);
                }

                self.insert_borrow(name, BorrowState::Initialized);

                Ok(())
            }
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
                    return Err(format!("Cannot borrow {ident} as it is currently being mutably borrowed"));
                }

                self.insert_borrow(name, BorrowState::ImmutBorrowed);
                return Ok(());
            } else {
                return Err(format!("Variable {ident} is not initialized"));
            }
        }

        Err(format!("Invalid borrow of {name}"))
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
        args: &'a Option<Vec<String>>,
        body: &'a [Statement],
    ) -> BorrowResult {
        self.borrows.push(HashMap::new());

        // check args if exists
        if let Some(args) = args {
            for arg in args {
                self.borrow_imm(arg)?;
            }
        }

        // check body of function
        let result = self.check(body);

        // release borrows
        self.borrows.pop();

        result
    }
    /// `check_function_call` checks a function call.
    ///
    /// It should ensure that the args passed to the function aren't
    /// violating any borrow rules.
    fn check_function_call(&mut self, _name: &str, args: &'a Vec<Expression>) -> BorrowResult {
        for arg in args {
            self.check_expression(arg)?;
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
        if let Expression::Reference(var) = expr {
            let borrow = self.get_borrow(var);

            if let Some(BorrowState::Borrowed) = borrow {
                return Err(format!("Cannot borrow {var} as immutable"));
            }
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

        Err(format!("Cannot borrow {name} as mutable"))
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

        Err(format!("Cannot borrow {name} as immutable"))
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
    use crate::{lexer::Lexer, parser::Parser, token::TokenType};

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

        assert_eq!(result, Err("Variable `a` is not initialized".to_string()));
    }
}
