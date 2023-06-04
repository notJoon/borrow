#[derive(PartialEq, Eq, Clone)]
pub enum LifetimeError {
    VariableNotFound(String),
    VariableAlreadyExists(String),
    BorrowedMutable(String),
    BorrowedImmut(String),
    LifetimeTooShort(String),
}

impl std::fmt::Display for LifetimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            LifetimeError::VariableNotFound(var) => {
                write!(f, "Cannot borrow variable {var} not found")
            }
            LifetimeError::VariableAlreadyExists(var) => write!(
                f,
                "Cannot borrow variable {var} because it already exists in the current scope"
            ),
            LifetimeError::BorrowedMutable(var) => write!(
                f,
                "Cannot borrow variable {var} because it is already borrowed mutably`"
            ),
            LifetimeError::BorrowedImmut(var) => write!(
                f,
                "Cannot borrow variable {var} because it is already borrowed immutably`"
            ),
            LifetimeError::LifetimeTooShort(var) => write!(
                f,
                "Cannot borrow variable {var} because it does not live long enough`"
            ),
        }
    }
}

impl std::fmt::Debug for LifetimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LifetimeError::VariableNotFound(var) => write!(f, "VariableNotFound: {var}"),
            LifetimeError::VariableAlreadyExists(var) => write!(f, "VariableAlreadyExists: {var}"),
            LifetimeError::BorrowedMutable(var) => write!(f, "BorrowedMutable: {var}"),
            LifetimeError::BorrowedImmut(var) => write!(f, "BorrowedImmut: {var}"),
            LifetimeError::LifetimeTooShort(var) => write!(f, "LifetimeTooShort: {var}"),
        }
    }
}

impl std::error::Error for LifetimeError {}
