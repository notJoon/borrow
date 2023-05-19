// TODO: Borrow checker

use std::{collections::HashMap, hash::Hash};

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
    pub fn check(&mut self, stmts: &[Statement]) -> BorrowResult {
        match stmts {
            [] => Ok(()),
            [stmt, rest @ ..] => {
                self.check_statement(stmt)?;
                self.check(rest)
            }
        }
    }

    fn check_statement(&mut self, stmts: &Statement) -> BorrowResult {
        unimplemented!("check_statement")
    }
    /// `check_variable_decl` method checks a variable declaration, like `let x = 5;` or `let b = &a`.
    /// 
    /// It needs to ensure that if the variable is being assigned a reference,
    /// the referenced variable isn't already borrowed mutably.
    fn check_variable_decl(
        &mut self,
        var: &'a str,
        is_borrowed: bool,
    ) -> BorrowResult {
        if is_borrowed {
            self.borrow_mut(var)
        } else {
            self.borrow_imm(var)
        }
    }
    /// `check_function_def` checks a function definition.
    ///
    /// It should validate that the function params aren't violating
    /// any borrow rules.
    /// It should also call `BorrowChecker::check` on the function body,
    /// to ensure that function body is also valid.
    fn check_function_def(
        &mut self,
        args: &'a Option<Vec<String>>,
        body: &[Statement],
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
    fn check_function_call(&mut self, args: &'a [Option<Expression>]) -> BorrowResult {
        for arg in args {
            if let Some(Expression::Reference(var)) = arg {
                let borrow = self.get_borrow(var);

                if let Some(BorrowState::Borrowed) = borrow {
                    return Err(format!("Variable {var} is already borrowed"));
                }
            }
        }

        Ok(())
    }
    /// `check_scope` checks a scope(block of statement inside `{}`).
    ///
    /// It should call `BorrowChecker::check` on each statement inside the scope.
    fn check_scope(&mut self, body: &[Statement]) -> BorrowResult {
        self.borrows.push(HashMap::new());

        let result = self.check(body);

        match self.borrows.pop() {
            Some(borrows) => {
                borrows.keys().for_each(|var| self.free(var));
            }
            None => {
                panic!("BorrowChecker::check_scope: self.borrows.pop() is None");
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
    fn borrow_mut(&mut self, var: &'a str) -> BorrowResult {
        let last_borrow = self.borrows.last().unwrap();

        if !last_borrow
            .values()
            .any(|state| *state == BorrowState::Borrowed)
        {
            self.insert_borrow(var, BorrowState::Borrowed);
            Ok(())
        } else {
            Err(format!("Cannot borrow {var} as mutable"))
        }
    }
    /// `borrow_imm` method should handle the logic of mutably borrowing a variable.
    ///
    /// It should ensure that the variable isn't already borrowed, and then
    /// make it as mutably borrowed in the `BorrowChecker`.
    fn borrow_imm(&mut self, var: &'a str) -> BorrowResult {
        let last_borrow = self.borrows.last().unwrap();

        if !last_borrow
            .values()
            .any(|state| *state == BorrowState::Borrowed)
        {
            self.insert_borrow(var, BorrowState::Borrowed);
            Ok(())
        } else {
            Err(format!("Cannot borrow {var} as immutable"))
        }
    }
    /// `free` method should handle the logic of releasing a borrow
    /// when a variable goes out of scope.
    ///
    /// It should remove the variable from the `BorrowChecker`.
    fn free(&mut self, var: &'a str) -> () {
        if self.is_borrow_contains_key(var) {
            self.borrows.last_mut().unwrap().remove(var);
        }
    }

    /// helper functions

    fn get_borrow(&mut self, var: &'a str) -> Option<&BorrowState> {
        self.borrows.last_mut().unwrap().get(var)
    }

    fn insert_borrow(&mut self, var: &'a str, state: BorrowState) -> () {
        self.borrows.last_mut().unwrap().insert(var, state);
    }

    fn is_borrow_contains_key(&mut self, var: &'a str) -> bool {
        self.borrows.last_mut().unwrap().contains_key(var)
    }
}

#[cfg(test)]
mod borrow_tests {
    use crate::{lexer::Lexer, parser::Parser, token::TokenType};

    use super::*;

    fn setup(input: &str) -> Vec<TokenType> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().expect("Failed to tokenize");

        tokens
    }

    macro_rules! assert_valid {
        ($input: expr) => {
            let tokens = setup($input);
            let mut parser = Parser::new(&tokens);

            let stmts = parser.parse();
            let mut checker = BorrowChecker::new();

            assert!(checker.check(&stmts).is_ok());
        };
    }

    macro_rules! assert_invalid {
        ($input: expr) => {
            let tokens = setup($input);
            let mut parser = Parser::new(&tokens);

            let stmts = parser.parse();
            let mut checker = BorrowChecker::new();

            assert!(checker.check(&stmts).is_err());
        };
    }

    #[test]
    fn test_valid_borrow() {
        let input = r#"
            let a = 5;
            let b = &a;
            let c = a + 1;
        "#;

        assert_valid!(input);
    }

    #[test]
    fn test_invalid_borrow() {
        let input = r#"
            let a = 6;
            let b = &a;
            a = 6;
        "#;

        assert_invalid!(input);
    }

    #[test]
    fn test_valid_borrow_scope() {
        let input = r#"
            let a = 5;
            {
                let b = &a;
            }
            a = 6;
        "#;

        assert_valid!(input);
    }

    #[test]
    fn test_invalid_borrow_scope() {
        let input = r#"
            let a = 5;
            let b = &a;
            {
                a = 6;
            }
        "#;

        assert_invalid!(input);
    }
}
