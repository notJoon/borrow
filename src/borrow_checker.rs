use std::collections::HashMap;

use crate::{
    ast::{Expression, Statement},
    errors::{BorrowError, CheckError}, lifetime::Scope,
};

type BorrowResult = Result<(), BorrowError>;
type CheckResult = Result<(), CheckError>;

/// The `BorrowChecker` struct is used to keep track of the state of borrows.
pub struct BorrowChecker<'a> {
    scope: Scope<'a>,
    borrows: Vec<HashMap<&'a str, BorrowState>>,
}

// TODO BorrowChecker's scope does not update its scope_id. should be fixed.

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
            scope: Scope::new(None),
            borrows: vec![HashMap::new()],
        }
    }
    /// `check` method will receive a statement and dispatch
    /// to the appropriate specific check method based on the `ast::Statement` variant.
    pub fn check(&mut self, stmts: &'a [Statement]) -> CheckResult {
        match stmts {
            [] => Ok(()),
            [stmt, rest @ ..] => {
                let _ = self.check_statement(stmt);

                // Check rules for all variables in the current scope
                for name in self.scope.variables.keys() {
                    self.check_rules(name, self.scope.id);
                }

                self.check(rest)
            }
        }
    }

    fn check_statement(&mut self, stmt: &'a Statement) -> CheckResult {
        match stmt {
            Statement::VariableDecl {
                name,
                value,
                is_borrowed,
            } => self.check_variable_decl(name, value, *is_borrowed),
            Statement::FunctionDef { name, args, body } => {
                self.allocate_scope(|s| s.check_function_def(name, args, body))
            }
            Statement::Scope(stmts) => self.allocate_scope(|s| s.check(stmts)),
            Statement::Return(expr) => self.check_return(expr),
            Statement::Expr(expr) => self.check_expression(expr),
        }
    }
    /// check borrow and lifetime rules for each given variable name.
    fn check_rules(&self, name: &'a str, id: usize) {
        self.scope.check_lifetime(name, id).unwrap();
        self.scope.check_borrow_rules(name).unwrap();
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
    ) -> CheckResult {
        match (is_borrowed, value) {
            (true, Some(Expression::Reference(ref ident))) => {
                if let Some(state) = self.get_borrow(ident) {
                    match state {
                        // [NOTE] 2023-06-15
                        // This line used to checks `BorrowState::Borrowed` or `BorrowState::ImmutBorrowed` state.
                        // but, we allows to have multiple immutable borrows of the same variable.
                        // so, modified it to check only `Borrowed` state.
                        BorrowState::Borrowed => {
                            return Err(CheckError::Borrow(
                                BorrowError::BorrowedMutable(
                                ident.into(),
                            )))
                        }
                        // [NOTE] 2023-06-16
                        // Allow to declare a variable without initial value.
                        // but it must panic when the reference is not initialized.
                        BorrowState::Uninitialized => {
                            return Err(CheckError::Borrow(
                                BorrowError::DeclaredWithoutInitialValue(
                                ident.into(),
                            )))
                        }
                        _ => {}
                    }
                    // [NOTE] 2023-06-15
                    // `BorrowState::ImmutBorrowed` and `BorrowState::Initialized` into the borrows hashmap
                    // for the same variable name. This could cause potential issue like overwrite the borrow state.
                    self.insert_borrow(name, BorrowState::ImmutBorrowed);

                    return Ok(());
                }

                // Err(BorrowError::VariableNotDefined(ident.into()))
                return Err(CheckError::Borrow(
                    BorrowError::VariableNotDefined(ident.into()),
                ))
            }
            (true, _) => Err(CheckError::Borrow(
                BorrowError::VariableNotInitialized(name.into())
            )),
            (false, Some(expr)) => {
                let _ = self.check_expression(expr);
                self.insert_borrow(name, BorrowState::Initialized);

                Ok(())
            }
            (false, None) => Err(CheckError::Borrow(
                BorrowError::DeclaredWithoutInitialValue(name.into())
            )),
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
                    return Err(BorrowError::InvalidBorrowMutablyBorrowed(ident.into()));
                }

                self.insert_borrow(name, BorrowState::ImmutBorrowed);
                return Ok(());
            }

            return Err(BorrowError::VariableNotDefined(ident.into()));
        }

        Err(BorrowError::InvalidBorrow(name.into()))
    }

    fn check_value_expr(&mut self, value: &'a Option<Expression>) -> CheckResult {
        if let Some(expr) = value {
            return self.check_expression(expr);
        }

        Ok(())
    }

    fn check_function_def(
        &mut self,
        _name: &'a str,
        args: &'a Option<Vec<(String, bool)>>,
        body: &'a [Statement],
    ) -> CheckResult {
        self.borrows.push(HashMap::new());

        // check args if exists
        if let Some(args) = args {
            for (arg, is_borrowed) in args {
                // Insert each argument into the current scope as an initialized variable
                self.insert_borrow(arg, BorrowState::Initialized);

                if *is_borrowed {
                    match self.borrow_imm(arg) {
                        Ok(_) => {}
                        // Err(err) => return Err(CheckError::Borrow()),
                        Err(_) => return Err(CheckError::Borrow(
                            BorrowError::CannotBorrowImmutable(arg.into()),
                        )),
                    }
                }
            }
        }

        // check body of function
        let result = match self.check(body) {
            Ok(_) => Ok(()),
            Err(err) => panic!("Error: {:?}", err)
        };

        // release borrows
        self.borrows.pop();

        result
    }

    fn declare(&mut self, var: &'a str) -> BorrowResult {
        if let Some(scope) = self.borrows.last_mut() {
            if scope.contains_key(var) {
                return Err(BorrowError::VariableDeclaredDuplicate(var.into()));
            }

            scope.insert(var, BorrowState::Uninitialized);
            return Ok(());
        }

        Err(BorrowError::NoScopeAvailable(var.into()))
    }
    /// `check_function_call` checks a function call.
    ///
    /// It should ensure that the args passed to the function aren't
    /// violating any borrow rules.
    fn check_function_call(&mut self, _name: &str, args: &'a Vec<Expression>) -> BorrowResult {
        for arg in args {
            let _ = self.check_expression(arg);

            if let Expression::Ident(ident) = arg {
                if let Some(BorrowState::Borrowed) = self.get_borrow(ident) {
                    return Err(BorrowError::BorrowedMutable(ident.into()));
                }
            }
        }

        Ok(())
    }
    /// `check_expression` checks an expression.
    ///
    /// This is where most of the borrow checking logic will be.
    /// it should handle checking identifiers, literals and operators,
    /// ensuring that any identifiers are borrowed references, they aren't being
    /// used in a way that would violate the borrow rules.
    fn check_expression(&mut self, expr: &'a Expression) -> CheckResult {
        match expr {
            // if the expression is a reference, check if the variable is already borrowed
            Expression::Reference(var) => {
                let borrow = self.get_borrow(var);

                if let Some(BorrowState::Borrowed) = borrow {
                    return Err(CheckError::Borrow(
                        BorrowError::BorrowedMutable(var.into()),
                    ));
                }
            }

            // if the expression is a binary operation, check the lhs and rhs
            Expression::BinaryOp { lhs, op: _, rhs } => {
                self.check_expression(lhs)?;
                self.check_expression(rhs)?;
            }

            // if the expression is an identifier, check if the variable's borrow and its lifetime
            Expression::Ident(ident) => {
                self.check_rules(ident, self.scope.id);

                if self.get_borrow(ident).is_none() {
                    return Err(CheckError::Borrow(
                        BorrowError::VariableNotInitialized(ident.into()),
                    ));
                }
            }

            _ => {}
        }

        Ok(())
    }

    fn check_return(&mut self, expr: &'a Option<Expression>) -> CheckResult {
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

        Err(BorrowError::CannotBorrowMutable(name.into()))
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

        Err(BorrowError::CannotBorrowImmutable(name.into()))
    }

    fn get_borrow(&mut self, var: &'a str) -> Option<&BorrowState> {
        for scope in self.borrows.iter().rev() {
            if let Some(state) = scope.get(var) {
                return Some(state);
            }
        }

        None
    }

    fn insert_borrow(&mut self, var: &'a str, state: BorrowState) -> Option<BorrowState> {
        if let Some(scope) = self.borrows.last_mut() {
            return scope.insert(var, state);
        }

        None
    }

    fn remove_borrow(&mut self, var: &'a str) -> Option<BorrowState> {
        self.borrows.last_mut().unwrap().remove(var)
    }

    fn is_borrow_contains_key(&mut self, var: &'a str) -> bool {
        self.borrows.last_mut().unwrap().contains_key(var)
    }

    /// This function helps to manage the scope of borrow checking.
    /// It accepts a closure `action` which is executed within a new scope.
    /// The function automatically handles the scope entering and exiting
    /// by pushing a new `HashMap` to `self.borrows` and popping it after `action` execution.
    ///
    /// # Arguments
    ///
    /// * `action` - A closure that encapsulates the actions to be performed within the new scope.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the closure.
    /// * `T` - The output type of the closure.
    fn allocate_scope<F, T>(&mut self, action: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        // enter new scope
        self.borrows.push(HashMap::new());

        // apply action within the scope
        let result = action(self);

        // exit scope
        self.borrows.pop();

        result
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
    fn test_check_variable_declaration() {
        let mut checker = BorrowChecker::new();

        let input = r#"let a = 10;"#;
        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));

        let input = r#"let a;"#;
        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_check_variable_declaration_undeclared_borrow_as_parsed_form() {
        let mut checker = BorrowChecker::new();

        // let b = &a;
        let stmts = vec![Statement::VariableDecl {
            name: "b".into(),
            value: Some(Expression::Reference("a".into())),
            is_borrowed: true,
        }];

        assert_eq!(
            checker.check(&stmts),
            Err(CheckError::Borrow(
                BorrowError::VariableNotDefined("a".into())
            ))
        );
    }

    #[test]
    fn test_check_variable_declaration_is_valid() {
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
    fn test_check_variable_declaration_uninitialized() {
        let input = r#"let a;"#;

        let mut checker = BorrowChecker::new();

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(
            result,
            Ok(())
        );
    }

    #[test]
    #[should_panic = "variable `a` has no initial value"]
    fn test_reference_uninitialized_variable() {
        let input = r#"
            let a;
            let b = &a;
        "#;

        let mut checker = BorrowChecker::new();

        let result = setup(input);

        assert_eq!(
            checker.check(&result),
            Err(CheckError::Borrow(
                BorrowError::VariableNotInitialized("a".into())
            ))
        );
    }

    #[test]
    #[should_panic = "variable `x` has no initial value"]
    fn test_nested_scope_with_uninitialized_variable() {
        let mut checker = BorrowChecker::new();
        let stmts = vec![
            Statement::VariableDecl {
                name: "x".into(),
                value: None,
                is_borrowed: false,
            },
            Statement::Scope(vec![Statement::VariableDecl {
                name: "y".into(),
                value: Some(Expression::Reference("x".into())),
                is_borrowed: true,
            }]),
        ];

        assert_eq!(
            checker.check(&stmts),
            Err(CheckError::Borrow(
                BorrowError::DeclaredWithoutInitialValue("x".into())
            )),
        );
    }

    #[test]
    fn test_check_variable_declaration_with_chain_reference() {
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

        let input = r#"
        let a = 10;
        {
            let b = &a;
        }
        let c = &a;"#;

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    #[should_panic = "variable `b` is not defined in the current scope"]
    fn test_invalid_reference_in_nested_scope() {
        let mut checker = BorrowChecker::new();

        let input = r#"
        let a = 10;
        {
            let b = &a;
        }
        let c = &b;"#;

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Err(CheckError::Borrow(
            BorrowError::VariableNotDefined("b".into())
        )));
    }

    #[test]
    fn test_nested_scope_with_multiple_borrows() {
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

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn check_deep_nested_scope_borrow() {
        let mut checker = BorrowChecker::new();

        let input = r#"
            let x = 5;
            {
                let y = &x;
                {
                    let z = &y;
                }
            }
        "#;

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    #[should_panic = "variable `z` is not defined in the referenced scope"]
    fn check_invalid_deep_nested_scope_borrow() {
        let mut checker = BorrowChecker::new();

        let input = r#"
            let x = 5;
            {
                let y = &x;
                {
                    let z = &y;
                }

                let w = &z;
            }
        "#;

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Err(CheckError::Borrow(
            BorrowError::VariableNotDefined("z".into())
        )));
    }

    #[test]
    fn test_variable_shadowing() {
        let mut checker = BorrowChecker::new();

        let input = r#"
            let x = 5;
            let x = 10;
        "#;

        let result = setup(input);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_duplicated_variable_name_in_different_scope() {
        let mut checker = BorrowChecker::new();

        let input = r#"
            let x = 5;
            {
                let x = 10;
            }
        "#;

        let result = setup(input);
        let result = checker.check(&result);

        // println!("{:#?}", checker.scope);

        assert_eq!(result, Ok(()));
    }

    #[test]
    // I think, lifetime checker does not recognize the function's parameter as an variable.
    fn check_borrow_in_function_decl() {
        let mut checker = BorrowChecker::new();

        let input = r#"
        function foo(a) {
            let b = &a;

            return b;
        }
        "#;

        let result = setup(input);
        println!("{:#?}", result);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn check_borrow_multiple_function_decl() {
        let mut checker = BorrowChecker::new();

        let input = r#"
            function foo(a) {
                let b = &a;
            }

            function bar(a) {
                let b = &a;
                let c = foo(&b);
            }

            function baz(a, b) {
                let c = foo(&a);
                let d = bar(&b);
            }

            let x = 5;
            let y = 10;

            foo(&x);
            bar(&y);
            baz(foo(&x), bar(&y));
        "#;

        let result = setup(input);
        println!("{:#?}", result);
        let result = checker.check(&result);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_inference_borrows_function_and_variable_shadowing_case() {
        let input = r#"
            function foo(a, b) {
                let c = a + b;
                {
                    let result = 0;

                    let d;
                    let d = &c;
                    let d = d + 10;
                    
                    let result = d + 10;

                    return result;
                }

                let f = &c;
            }

            let x = 5;
            let y = 10;
            let z = foo(x, y);

            {
                let a = &x;
                let b = &y;
                let c = &z;

                {
                    function bar(a, b, c) {
                        let d = &a;
                        let e = &b;
                        let f = &c;

                        return d + e + f;
                    }

                    let d = &a;
                    let e = &b;
                    let f = &c;
                }

                let g = &a;
            }

            let h = &x;
        "#;

        let mut checker = BorrowChecker::new();
        let result = setup(input);

        assert_eq!(checker.check(&result), Ok(()));
    }
}

#[cfg(test)]
mod lifetime_tests {
    use crate::{lexer::Lexer, parser::Parser};

    use super::*;

    fn setup(input: &str) -> Vec<Statement> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().expect("Failed to tokenize");

        let mut parser = Parser::new(&tokens);

        parser.parse()
    }

    #[test]
    #[should_panic = "short lifetime"]
    fn test_short_lifetime() {
        unimplemented!("short lifetime");
    }
}