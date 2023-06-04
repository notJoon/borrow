use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::borrow_checker::BorrowState;
use crate::errors::LifetimeError;

/// Automatically generate a unique scope `id`.
static SCOPE_ID: AtomicUsize = AtomicUsize::new(0);

/// Generate a unique scope `id`.
fn next_scope_id() -> usize {
    SCOPE_ID.fetch_add(1, Ordering::SeqCst)
}

/// A variable in the scope.
///
/// It makes the `Scope` more flexible rather than directly using `BorrowState`.
pub struct Variable {
    state: BorrowState,
    scope_id: usize,
}

/// `Scope` is a collection of variables.
///
/// It is used to track the variables in the current scope.
pub struct Scope<'a> {
    id: usize,
    variables: BTreeMap<&'a str, Variable>,
    parent: Option<&'a Scope<'a>>,
}

impl Variable {
    /// Creates a new `Variable` instance.
    pub fn new(state: BorrowState, scope_id: usize) -> Self {
        Self { state, scope_id }
    }

    pub fn get_state(&self) -> &BorrowState {
        &self.state
    }

    pub fn set_state(&mut self, state: BorrowState) {
        self.state = state;
    }

    pub fn get_scope_id(&self) -> usize {
        self.scope_id
    }

    pub fn set_scope_id(&mut self, scope_id: usize) {
        self.scope_id = scope_id;
    }
}

impl<'a> Scope<'a> {
    /// Creates a new `scope` instance.
    pub fn new() -> Self {
        Self {
            id: next_scope_id(),
            variables: BTreeMap::new(),
            parent: None,
        }
    }

    /// Check if the scope contains a variable.
    pub fn contains_val(&self, var: &'a str) -> bool {
        self.variables.contains_key(var)
    }

    /// Insert a variable and borrow state into the scope.
    pub fn insert(&'a mut self, var: &'a str, state: BorrowState) -> Result<(), LifetimeError> {
        if self.contains_val(var) {
            return Err(LifetimeError::VariableAlreadyExists(var.to_string()));
        }

        self.variables.insert(var, Variable::new(state, self.id));
        Ok(())
    }

    pub fn get_state(&self, var: &'a str) -> Option<&BorrowState> {
        self.variables.get(var).map(|v| v.get_state())
    }

    pub fn set_state(&mut self, var: &'a str, state: BorrowState) {
        if let Some(variable) = self.variables.get_mut(var) {
            variable.set_state(state);
        }
    }

    pub fn check_lifetime(& self, var: &'a str, borrow_id: usize) -> Result<(), LifetimeError> {
        let variable = self.get_variable(var)?;

        if borrow_id < variable.scope_id {
            return Err(LifetimeError::LifetimeTooShort(var.to_string()));
        }

        Ok(())
    }

    pub fn check_borrow_rules(&self, var: &'a str) -> Result<(), LifetimeError> {
        let variable = self.get_variable(var)?;

        match variable.state {
            BorrowState::Borrowed => Err(LifetimeError::BorrowedMutable(var.to_string())),
            _ => Ok(()),
        }
    }

    fn get_variable(&self, var: &'a str) -> Result<&Variable, LifetimeError> {
        self.variables
            .get(var)
            .ok_or(LifetimeError::VariableNotFound(var.to_string()))
    }
}
