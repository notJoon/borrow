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

#[derive(Debug)]
/// A variable in the scope.
pub struct Variable {
    /// The current borrow state of the variable.
    state: BorrowState,
    /// The scope `id` of the variable.
    scope_id: usize,
    /// Whether the variable is allocated or not.
    is_allocated: bool,
}

impl Variable {
    /// Creates a new `Variable` instance with given `state` and `scope_id`.
    ///
    /// The `is_allocated` field is set to `true` if the `state` is not `Uninitialized`.
    pub fn new(state: BorrowState, scope_id: usize) -> Self {
        let is_allocated = state != BorrowState::Uninitialized;

        Self {
            state,
            scope_id,
            is_allocated,
        }
    }

    /// Returns the current borrow state of the variable.
    fn get_state(&self) -> &BorrowState {
        &self.state
    }

    /// Sets the state of the variable.
    ///
    /// The `is_allocated` field is updated based on the new `state`.
    fn set_state(&mut self, state: BorrowState) {
        self.is_allocated = state != BorrowState::Uninitialized;
        self.state = state;
    }

    /// Returns the current memory allocation status of the variable.
    fn is_allocated(&self) -> bool {
        self.is_allocated
    }
}

#[derive(Debug)]
/// `Scope` is a collection of variables.
pub struct Scope<'a> {
    /// The scope `id` of the scope.
    pub id: usize,
    /// The variables in the scope.
    pub variables: BTreeMap<&'a str, Variable>,
    /// The parent scope. `None` if the scope is the root scope.
    pub parent: Option<&'a Scope<'a>>,
}

impl<'a> Scope<'a> {
    /// Creates a new `scope` instance with the given `parent` scope.
    ///
    /// The ID is automatically generated.
    pub fn new(parent: Option<&'a Scope<'a>>) -> Self {
        Self {
            id: next_scope_id(),
            variables: BTreeMap::new(),
            parent,
        }
    }

    /// Check if the scope or any of its parent scopes contains a variable.
    fn contains_val(&self, var: &'a str) -> bool {
        // Check if the current scope contains the variable.
        if self.variables.contains_key(var) {
            return true;
        }

        // Check if the parent scope contains the variable.
        if let Some(parent) = self.parent {
            return parent.contains_val(var);
        }

        false
    }

    /// Insert a variable\ with the given `state` into the scope.
    ///
    /// The variable is allocated memory if its state is not `Uninitialized`.
    fn insert(&mut self, var: &'a str, state: BorrowState) {
        self.variables.insert(var, Variable::new(state, self.id));
    }

    /// Returns the state of a variable in the scope or any of its parent scopes.
    fn get_state(&self, var: &'a str) -> Option<&BorrowState> {
        self.variables.get(var).map(|v| v.get_state())
    }

    /// Sets the state of a variable in the scope.
    ///
    /// The variable's memory allocation is updated based on the new state.
    fn set_state(&mut self, var: &'a str, state: BorrowState) {
        if let Some(variable) = self.variables.get_mut(var) {
            variable.is_allocated = state != BorrowState::Uninitialized;
            variable.set_state(state);
        }
    }

    /// Returns whether a variable in the scope or any of its parent scopes is allocated.
    fn is_allocated(&self, var: &'a str) -> Option<bool> {
        self.variables.get(var).map(|v| v.is_allocated())
    }

    /// Checks the lifetime of a variable in the scope or any of its parent scopes.
    ///
    /// if the variable's lifetime is too short, an error is returned.
    pub fn check_lifetime(&self, var: &'a str, borrow_id: usize) -> Result<(), LifetimeError> {
        let variable = self.get_variable(var)?;

        if let BorrowState::Uninitialized = variable.state {
            return Ok(());
        }

        if borrow_id < variable.scope_id || !variable.is_allocated() {
            return Err(LifetimeError::LifetimeTooShort(var.to_string()));
        }

        if let Some(parent) = self.parent {
            if parent.check_lifetime(var, borrow_id).is_err() {
                return Err(LifetimeError::LifetimeTooShort(var.to_string()));
            }
        }

        Ok(())
    }

    /// Checks the borrow rules of a variable in the scope or any of its parent scopes.
    ///
    /// if the variable is borrowed mutably, an error is returned.
    pub fn check_borrow_rules(&self, var: &'a str) -> Result<(), LifetimeError> {
        let variable = self.get_variable(var)?;

        match variable.state {
            BorrowState::Borrowed | BorrowState::ImmutBorrowed => {
                Err(LifetimeError::BorrowedMutable(var.to_string()))
            }
            _ => Ok(()),
        }
    }

    /// Returns a reference to a variable in the scope or any of its parent scopes.
    ///
    /// If the variable is not found, an error is returned.
    pub fn get_variable(&self, var: &'a str) -> Result<&Variable, LifetimeError> {
        if let Some(variable) = self.variables.get(var) {
            return Ok(variable);
        }

        if let Some(parent) = self.parent {
            return parent.get_variable(var);
        }

        Err(LifetimeError::VariableNotFound(var.to_string()))
    }
}

#[cfg(test)]
mod lifetime_test {
    use super::*;

    #[test]
    fn test_variable_state_and_allocation() {
        let mut variable = Variable::new(BorrowState::Uninitialized, 0);
        assert_eq!(variable.get_state(), &BorrowState::Uninitialized);
        assert_eq!(variable.is_allocated(), false);

        variable.set_state(BorrowState::Borrowed);
        assert_eq!(variable.get_state(), &BorrowState::Borrowed);
        assert_eq!(variable.is_allocated(), true);
    }

    #[test]
    fn test_scope_insert_and_get_state() {
        let mut scope = Scope::new(None);

        scope.insert("x", BorrowState::Uninitialized);
        scope.insert("y", BorrowState::Uninitialized);

        assert_eq!(scope.get_state("x"), Some(&BorrowState::Uninitialized));
        assert_eq!(scope.get_state("y"), Some(&BorrowState::Uninitialized));
        assert_eq!(scope.get_state("z"), None);
    }

    #[test]
    fn test_scope_get_state_and_empty_deallocation() {
        let mut scope = Scope::new(None);

        scope.insert("x", BorrowState::Uninitialized);
        scope.set_state("x", BorrowState::Borrowed);
        assert_eq!(scope.get_state("x"), Some(&BorrowState::Borrowed));

        scope.set_state("x", BorrowState::Uninitialized);
        assert_eq!(scope.get_state("x"), Some(&BorrowState::Uninitialized));
        // Assuming that setting a variable's state to `Uninitialized` deallocates its memory.
        assert_eq!(scope.is_allocated("x"), Some(false));

        scope.set_state("y", BorrowState::Borrowed);
        assert_eq!(scope.get_state("y"), None);
    }

    #[test]
    fn test_scope_check_lifetime() {
        let mut scope = Scope::new(None);

        scope.insert("x", BorrowState::Uninitialized);
        assert!(scope.check_lifetime("x", 0).is_ok());

        scope.set_state("x", BorrowState::Borrowed);
        assert!(scope.check_lifetime("x", 0).is_err());

        scope.set_state("x", BorrowState::Uninitialized);
        assert!(scope.check_lifetime("x", 0).is_ok());
    }

    #[test]
    fn test_scope_check_borrow_rules() {
        let mut scope = Scope::new(None);

        scope.insert("x", BorrowState::Uninitialized);
        assert!(scope.check_borrow_rules("x").is_ok());

        scope.set_state("x", BorrowState::Borrowed);
        assert!(scope.check_borrow_rules("x").is_err());

        scope.set_state("x", BorrowState::Uninitialized);
        assert!(scope.check_borrow_rules("x").is_ok());
    }

    #[test]
    fn test_lifetime_in_nested_scope() {
        let mut parent_scope = Scope::new(None);
        assert_eq!(parent_scope.id, 0);
        parent_scope.insert("x", BorrowState::Uninitialized);

        // ---
            let mut child_scope = Scope::new(Some(&parent_scope));
            assert_eq!(child_scope.id, 1);
            child_scope.insert("y", BorrowState::Uninitialized);

            // ---
                let mut child_child_scope = Scope::new(Some(&child_scope));
                assert_eq!(child_child_scope.id, 2);
                child_child_scope.insert("z", BorrowState::Uninitialized);
                assert!(child_child_scope.contains_val("x"));
                assert!(child_child_scope.contains_val("y"));
                assert!(child_child_scope.contains_val("z"));
            // ---
            assert_eq!(child_scope.id, 1);
            assert!(child_scope.contains_val("x"));
            assert!(child_scope.contains_val("y"));
            assert!(!child_scope.contains_val("z"));
        // ---
        assert_eq!(parent_scope.id, 0);
        assert!(parent_scope.contains_val("x"));
        assert!(!parent_scope.contains_val("y"));
        assert!(!parent_scope.contains_val("z"));
    }
}
