use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::borrow_checker::BorrowState;
use crate::errors::LifetimeError;

/* TODO
    1. Define the concept of memory allocation and deallocation and implement it.
    2. Modify the `Variable` struct. should include new information fields.
    3. Update the `Scope` methods. may need to be updated to take into account
        the new memory allocatio field of the `Variable` struct.
    4. Update the lifetime checks. `check_lifetime` method needs to be updated to check
        that a variable's lifetime starts with the allocation and continues until the
        memory place allocated for that variable's name no longer represents value of that
*/

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
    is_allocated: bool,
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
        let is_allocated = state != BorrowState::Uninitialized;

        Self { 
            state, 
            scope_id, 
            is_allocated,
        }
    }

    pub fn get_state(&self) -> &BorrowState {
        &self.state
    }

    pub fn set_state(&mut self, state: BorrowState) {
        self.is_allocated = state != BorrowState::Uninitialized;
        self.state = state;
    }

    pub fn is_allocated(&self) -> bool {
        self.is_allocated
    }
}

impl<'a> Scope<'a> {
    /// Creates a new `scope` instance.
    pub fn new(parent: Option<&'a Scope<'a>>) -> Self {
        Self {
            id: next_scope_id(),
            variables: BTreeMap::new(),
            parent,
        }
    }

    /// Check if the scope or any of its parent scopes contains a variable.
    pub fn contains_val(&self, var: &'a str) -> bool {
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

    /// Insert a variable and borrow state into the scope.
    pub fn insert(&mut self, var: &'a str, state: BorrowState) {
        self.variables.insert(var, Variable::new(state, self.id));
    }

    pub fn get_state(&self, var: &'a str) -> Option<&BorrowState> {
        self.variables.get(var).map(|v| v.get_state())
    }

    pub fn set_state(&mut self, var: &'a str, state: BorrowState) {
        if let Some(variable) = self.variables.get_mut(var) {
            variable.is_allocated = state != BorrowState::Uninitialized;
            variable.set_state(state);
        }
    }

    pub fn is_allocated(&self, var: &'a str) -> Option<bool> {
        self.variables.get(var).map(|v| v.is_allocated())
    }

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

    pub fn check_borrow_rules(&self, var: &'a str) -> Result<(), LifetimeError> {
        let variable = self.get_variable(var)?;

        match variable.state {
            BorrowState::Borrowed | BorrowState::ImmutBorrowed => {
                Err(LifetimeError::BorrowedMutable(var.to_string()))
            }
            _ => Ok(()),
        }
    }

    fn get_variable(&self, var: &'a str) -> Result<&Variable, LifetimeError> {
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
        parent_scope.insert("x", BorrowState::Uninitialized);

        {
            let mut child_scope = Scope::new(Some(&parent_scope));
            child_scope.insert("y", BorrowState::Uninitialized);

            {
                let mut child_child_scope = Scope::new(Some(&child_scope));
                child_child_scope.insert("z", BorrowState::Uninitialized);

                assert!(child_child_scope.contains_val("x"));
                assert!(child_child_scope.contains_val("y"));
                assert!(child_child_scope.contains_val("z"));
            }

            assert!(child_scope.contains_val("x"));
            assert!(child_scope.contains_val("y"));
            assert!(!child_scope.contains_val("z"));
        }

        assert!(parent_scope.contains_val("x"));
        assert!(!parent_scope.contains_val("y"));
        assert!(!parent_scope.contains_val("z"));
    }
}
