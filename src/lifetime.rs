use std::collections::BTreeMap;

use crate::borrow_checker::BorrowState;

pub struct Variable {
    state: BorrowState,
}

pub struct Scope<'a> {
    variables: BTreeMap<&'a str, Variable>,
}

impl Variable {
    /// Creates a new `Variable` instance.
    pub fn new(is_borrowed: bool) -> Result<Self, String> {
        Ok(Self {
            state: BorrowState::Uninitialized,
        })
    }
}

impl<'a> Scope<'a> {
    /// Creates a new `scope` instance.
    pub fn new() -> Self {
        Self {
            variables: BTreeMap::new(),
        }
    }

    /// Check if the scope contains a variable.
    pub fn contains_val(&self, var: &'a str) -> bool {
        self.variables.contains_key(var)
    }

    /// Insert a variable and borrow state into the scope.
    pub fn insert(&mut self, var: &'a str, state: BorrowState) {
        let variable = Variable { state };

        self.variables.insert(var, variable);
    }

    /// Compute the borrowed variables in the scope
    pub fn borrowed_vars(&self) -> Vec<&'a str> {
        self.variables
            .iter()
            .filter_map(|(&var, variable)| {
                match variable.state {
                    BorrowState::Borrowed(_) | BorrowState::ImmutBorrowed(_) => Some(var),
                    _ => None,
                }
            })
            .collect()
    }
}