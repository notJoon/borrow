use std::collections::BTreeMap;

use crate::borrow_checker::BorrowState;

pub struct Variable {
    state: BorrowState,
    lifetime: Option<usize>,
}

pub struct Scope<'a> {
    borrows: BTreeMap<&'a str, BorrowState>,
    borrowed_vars: Vec<&'a str>,
}

impl Variable {
    /// Creates a new `Variable` instance.
    pub fn new(is_borrowed: bool) -> Result<Self, String> {
        if is_borrowed {
            return Err(format!("Variable is not declared without and initial value"));
        }

        Ok(Self {
            state: BorrowState::Uninitialized,
            lifetime: None,
        })
    }
}

impl<'a> Scope<'a> {
    /// Creates a new `scope` instance.
    pub fn new() -> Self {
        Self {
            borrows: BTreeMap::new(),
            borrowed_vars: Vec::new(),
        }
    }

    /// Check if the scope contains a variable.
    pub fn contains_val(&self, var: &'a str) -> bool {
        self.borrows.contains_key(var)
    }

    /// Insert a variable and borrow state into the scope.
    pub fn insert(&mut self, var: &'a str, state: BorrowState) {
        self.borrows.insert(var, state);

        if let BorrowState::Borrowed(_) | BorrowState::ImmutBorrowed(_) = state {
            self.borrowed_vars.push(var);
        }
    }
}