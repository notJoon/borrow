use std::collections::BTreeMap;

use crate::borrow_checker::BorrowState;

/// A variable in the scope.
/// 
/// It makes the `Scope` more flexible rather than directly using `BorrowState`.
pub struct Variable {
    state: BorrowState,
}

/// `Scope` is a collection of variables.
/// 
/// It is used to track the variables in the current scope.
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

    pub fn get_state(&self) -> &BorrowState {
        &self.state
    }

    pub fn set_state(&mut self, state: BorrowState) {
        self.state = state;
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

    pub fn get_state(&self, var: &'a str) -> Option<&BorrowState> {
        self.variables
            .get(var)
            .map(|v| v.get_state())
    }

    pub fn set_state(&mut self, var: &'a str, state: BorrowState) {
        if let Some(variable) = self.variables.get_mut(var) {
            variable.set_state(state);
        }
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