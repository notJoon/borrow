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

#[derive(PartialEq, Eq, Clone)]
pub enum BorrowError {
    BorrowedMutable(String),
    BorrowedImmut(String),
    DeclaredWithoutInitialValue(String),
    VariableNotDefined(String),
    VariableNotInitialized(String),
    VariableDeclaredDuplicate(String),
    VariableNotInScope(String),
    InvalidBorrowMutablyBorrowed(String),
    InvalidBorrow(String),
    NoScopeAvailable(String),
    CannotBorrowMutable(String),
    CannotBorrowImmutable(String),
}

impl std::fmt::Display for BorrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BorrowError::BorrowedMutable(var) => write!(
                f,
                "Cannot borrow {var} as it is currently being mutably borrowed"
            ),
            BorrowError::BorrowedImmut(var) => write!(
                f,
                "Cannot borrow {var} as it is currently being immutably borrowed"
            ),
            BorrowError::DeclaredWithoutInitialValue(var) => {
                write!(f, "Variable {var} is declared without an initial value")
            }
            BorrowError::VariableNotDefined(var) => {
                write!(f, "Variable {var} is not defined in the current scope")
            }
            BorrowError::VariableNotInitialized(var) => {
                write!(f, "Variable {var} is not initialized")
            }
            BorrowError::VariableDeclaredDuplicate(var) => {
                write!(f, "Variable {var} is already declared in the current scope")
            }
            BorrowError::VariableNotInScope(var) => {
                write!(f, "Variable {var} is not in scope")
            }
            BorrowError::InvalidBorrowMutablyBorrowed(var) => write!(
                f,
                "Cannot borrow {var}. It is currently being mutably borrowed"
            ),
            BorrowError::InvalidBorrow(var) => write!(f, "Invalid borrow of {var}"),
            BorrowError::NoScopeAvailable(var) => {
                write!(f, "No scope available for variable of {var}")
            }
            BorrowError::CannotBorrowMutable(var) => write!(f, "Cannot borrow {var} as mutable"),
            BorrowError::CannotBorrowImmutable(var) => {
                write!(f, "Cannot borrow {var} as immutable")
            }
        }
    }
}

impl std::fmt::Debug for BorrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BorrowError::BorrowedMutable(var) => write!(f, "BorrowedMutable: {var}"),
            BorrowError::BorrowedImmut(var) => write!(f, "BorrowedImmut: {var}"),
            BorrowError::DeclaredWithoutInitialValue(var) => {
                write!(f, "DeclaredWithoutInitialValue: {var}")
            }
            BorrowError::VariableNotDefined(var) => write!(f, "VariableNotDefined: {var}"),
            BorrowError::VariableNotInitialized(var) => write!(f, "VariableNotInitialized: {var}"),
            BorrowError::VariableDeclaredDuplicate(var) => {
                write!(f, "VariableDeclaredDuplicate: {var}")
            }
            BorrowError::VariableNotInScope(var) => write!(f, "VariableNotInScope: {var}"),
            BorrowError::InvalidBorrowMutablyBorrowed(var) => {
                write!(f, "InvalidBorrowMutablyBorrowed: {var}")
            }
            BorrowError::InvalidBorrow(var) => write!(f, "InvalidBorrow: {var}"),
            BorrowError::NoScopeAvailable(var) => write!(f, "NoScopeAvailable: {var}"),
            BorrowError::CannotBorrowMutable(var) => write!(f, "CannotBorrowMutable: {var}"),
            BorrowError::CannotBorrowImmutable(var) => write!(f, "CannotBorrowImmutable: {var}"),
        }
    }
}

impl std::error::Error for BorrowError {}

#[derive(PartialEq, Eq, Clone)]
pub enum OwnerGraphError {
    MultipleOwners(String),
}

impl std::fmt::Debug for OwnerGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnerGraphError::MultipleOwners(variable) => {
                write!(f, "Variable {variable} has multiple owners")
            }
        }
    }
}

impl std::fmt::Display for OwnerGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnerGraphError::MultipleOwners(variable) => {
                write!(f, "Variable {variable} has multiple owners")
            }
        }
    }
}

impl std::error::Error for OwnerGraphError {}