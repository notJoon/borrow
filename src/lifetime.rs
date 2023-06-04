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
}

impl<'a> Scope<'a> {
    /// Creates a new `scope` instance.
    pub fn new(parent: Option<&'a Scope<'a>>) -> Self {
        Self {
            id: next_scope_id(),
            variables: BTreeMap::new(),
            parent: parent,
        }
    }

    /// Check if the scope contains a variable.
    pub fn contains_val(&self, var: &'a str) -> bool {
        self.variables.contains_key(var)
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
            variable.set_state(state);
        }
    }

    pub fn check_lifetime(&self, var: &'a str, borrow_id: usize) -> Result<(), LifetimeError> {
        let variable = self.get_variable(var)?;

        if let BorrowState::Uninitialized = variable.state {
            return Ok(());
        }

        if borrow_id < variable.scope_id {
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
    fn test_variable_state() {
        let mut variable = Variable::new(BorrowState::Uninitialized, 0);
        assert_eq!(variable.get_state(), &BorrowState::Uninitialized);

        variable.set_state(BorrowState::Borrowed);
        assert_eq!(variable.get_state(), &BorrowState::Borrowed);
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
    fn test_scope_set_state() {
        let mut scope = Scope::new(None);
        scope.insert("x", BorrowState::Uninitialized);

        scope.set_state("x", BorrowState::Borrowed);
        assert_eq!(scope.get_state("x"), Some(&BorrowState::Borrowed));

        scope.set_state("y", BorrowState::Borrowed);
        assert_eq!(scope.get_state("y"), None);
    }

    #[test]
    // FIXME 
    fn test_scope_check_lifetime() {
        let parent = Scope::new(None);
        let mut scope = Scope::new(Some(&parent));

        scope.insert("x", BorrowState::Uninitialized);   

        assert_eq!(scope.check_lifetime("x", 0), Ok(()));
        assert_eq!(scope.check_lifetime("x", 1), Err(LifetimeError::LifetimeTooShort("x".to_string())));
    }

    #[test]
    fn test_scope_check_borrow_rule() {
        let mut scope = Scope::new(None);
        scope.insert("x", BorrowState::Uninitialized);

        assert_eq!(scope.check_borrow_rules("x"), Ok(()));

        scope.set_state("x", BorrowState::Borrowed);
        assert_eq!(
            scope.check_borrow_rules("x"), 
            Err(LifetimeError::BorrowedMutable("x".to_string())
        ));
    }
}
