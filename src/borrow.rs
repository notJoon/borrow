// TODO: Borrow checker

use std::collections::HashMap;

use crate::ast::Statement;

/// The `BorrowChecker` struct is used to keep track of the state of borrows.
/// 
/// It analyzes the AST (Abstract Syntax Tree) and tracks all active borrows.
/// The borrow information is stored in a `BorrowChecker` with a hashmap(`std::collections::HashMap`),
/// which keeps track of the borrows and their states.
pub struct BorrowChecker {
    borrows: HashMap<String, BorrowState>,
}

/// The `BorrowState` enum represents the state of a borrow.
/// It is used by the `BorrowChecker` to keep track of the borrow state.
pub enum BorrowState {
    /// Represents an immutable borrow. If a variable is borrowed immutably,
    /// it can be borrowed any number of times, but it cannot be borrowed mutably
    /// until all immutable borrows go out of scope.
    Immutable,
    /// Represents a mutable borrow. If a variable is borrowed mutably,
    /// it cannot be borrowed again, neither immutably nor mutably,
    /// until the mutable borrow goes out of scope.
    Mutable,
}

impl BorrowChecker {
    /// `new` method creates a new `BorrowChecker` instance.
    /// 
    /// It initializes the `BorrowChecker` with an empty hashmap.
    /// The hashmap will be used to keep track of the borrows and their states.
    pub fn new() -> Self {
        BorrowChecker {
            borrows: HashMap::new(),
        }
    }
    /// `check` method will receive a statement and dispatch
    /// to the appropriate specific check method based on the `ast::Statement` variant.
    pub fn check(&mut self, stmt: &Statement) -> Result<(), String> {
        unimplemented!("TODO: Implement BorrowChecker::check()")
    }
    /// `check_variable_decl` method checks a variable declaration, like `let x = 5;` or `let b = &a`.
    /// 
    /// it needs to ensure that if the variable is being assigned a reference,
    /// the referenced variable isn't already borrowed mutably.
    fn check_variable_decl(&mut self) {
        unimplemented!()
    }
    /// `check_function_def` checks a function definition.
    /// 
    /// It should validate that the function params aren't violating
    /// any borrow rules.
    /// It should also call `BorrowChecker::check` on the function body, 
    /// to ensure that function body is also valid.
    fn check_function_def(&mut self) {
        unimplemented!()
    }
    /// `check_function_call` checks a function call.
    /// 
    /// It should ensure that the args passed to the function aren't
    /// violating any borrow rules.
    fn check_function_call(&mut self) {
        unimplemented!()
    }
    /// `check_scope` checks a scope(block of statement inside `{}`).
    /// 
    /// It should call `BorrowChecker::check` on each statement inside the scope.
    fn check_scope(&mut self) {
        unimplemented!()
    }
    /// `check_expression` checks an expression.
    /// 
    /// This is where most of the borrow checking logic will be.
    /// it should handle checking identifiers, literals and operators,
    /// ensuring that f any identifiers are borrowed references, they aren't being
    /// used in a way that would violate the borrow rules.
    fn check_expression(&mut self) {
        unimplemented!()
    }
    /// `borrow_mut` method should handle the logic of immutably borrowing a variable.
    /// 
    /// It should ensure that the variable isn't already borrowed mutably, and then
    /// make it as immutably borrowed in the `BorrowChecker`.
    fn borrow_mut(&mut self) {
        unimplemented!()
    }
    /// `borrow_imm` method should handle the logic of mutably borrowing a variable.
    /// 
    /// It should ensure that the variable isn't already borrowed, and then
    /// make it as mutably borrowed in the `BorrowChecker`.
    fn borrow_imm(&mut self) {
        unimplemented!()
    }
    /// `release_borrow` method should handle the logic of releasing a borrow 
    /// when a variable goes out of scope.
    /// 
    /// It should remove the variable from the `BorrowChecker`.
    fn release_borrow(&mut self) {
        unimplemented!()
    }
}

#[cfg(test)]
mod borrow_tests {
    fn test() {
        todo!("TODO: Implement borrow tests");
    }
}