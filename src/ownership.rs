use std::collections::BTreeMap;

use crate::{
    ast::{Expression, Statement},
    errors::OwnerGraphError,
};

/// A structure representing an ownership graph.
/// The `collections::BTreeMap` preserves the insertion order of the keys.
#[derive(Debug, PartialEq, Eq, Clone)]
struct OwnershipGraph {
    /// The `graph` field represents the relationship
    /// between the owner and the variables that it owns.
    ///
    /// The `key` is a variable that is borrowing, and the `value`
    /// is a vector of variables that are borrowed by the key.
    graph: BTreeMap<String, Vec<String>>,
}

impl OwnershipGraph {
    /// `OwnershipGraph::new()` construction of an empty `OwnershipGraph`.
    pub fn new() -> Self {
        Self {
            graph: BTreeMap::new(),
        }
    }

    /// `OwnershipGraph::add_owner()` adds a new node(`owner`) to the graph.
    ///
    /// A node is added when a new variable is declared.
    pub fn add_owner(&mut self, owner: &str, variable: &str) {
        let entry = self.graph.entry(owner.into()).or_insert_with(Vec::new);

        if !entry.contains(&variable.into()) {
            entry.push(variable.into());
        }
    }

    /// `OwnershipGraph::add_borrower()` adds an edge between nodes in the graph.
    ///
    /// An edge is added when a variable borrows from another variable.
    pub fn add_borrower(&mut self, owner: &str, borrower: &str) {
        if let Some(borrowers) = self.graph.get_mut(owner) {
            if !borrowers.contains(&borrower.into()) {
                borrowers.push(borrower.into());
            }
        }
    }

    /// `OwnershipGraph::remove_owner()` removes a node(`owner`) from the graph.
    ///
    /// A node is removed when a variable is out of scope.
    pub fn remove_owner(&mut self, owner: &str, variable: &str) {
        if let Some(owners) = self.graph.get_mut(owner) {
            owners.retain(|x| x != variable);
        }
    }

    /// `OwnershipGraph::remove_borrower()` removes an edge between nodes in the graph.
    ///
    /// An edge is removed when a variable is out of scope.
    pub fn remove_borrower(&mut self, owner: &str, borrower: &str) {
        if let Some(borrowers) = self.graph.get_mut(owner) {
            borrowers.retain(|x| x != borrower);
        }
    }
}

impl Default for OwnershipGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// `build_ownership_graph()` builds an ownership graph from a list of statements.
///
/// It iterates through the list of statements (AST generated from the parser) and processes variable
/// declarations and borrow expressions.
fn build_ownership_graph(stmts: &[Statement]) -> Result<OwnershipGraph, OwnerGraphError> {
    const GLOBAL: &str = "global_var";
    let mut graph = OwnershipGraph::default();
    let mut current_owner = GLOBAL.into();

    for stmt in stmts {
        match stmt {
            Statement::VariableDecl {
                name,
                is_borrowed,
                value,
            } => {
                if *is_borrowed {
                    if let Some(Expression::Reference(ref_var)) = value {
                        current_owner = ref_var.to_owned();
                        graph.add_borrower(&current_owner, name);
                    }
                } else {
                    current_owner = GLOBAL.into();
                }
                graph.add_owner(&current_owner, name);
            }
            Statement::Scope(scope) => {
                let prev_owner = current_owner.to_owned();
                let mut declared_in_scope = vec![];

                for inner_stmt in scope {
                    if let Statement::VariableDecl {
                        name,
                        value,
                        is_borrowed,
                    } = inner_stmt
                    {
                        declared_in_scope.push(name.to_owned());

                        if *is_borrowed {
                            if let Some(Expression::Reference(ref_var)) = value {
                                current_owner = ref_var.to_owned();
                                graph.add_borrower(&current_owner, name);
                            }
                        }

                        graph.add_owner(&prev_owner, name);
                        current_owner = name.into();
                    }
                }

                for var in declared_in_scope {
                    graph.remove_owner(&prev_owner, &var);
                    current_owner = prev_owner.to_owned();
                }
            }

            _ => {}
        }
    }

    for (variable, owners) in &graph.graph {
        if owners.len() > 1 {
            for owner in owners {
                if owner == variable {
                    return Err(OwnerGraphError::MultipleOwners(variable.clone()));
                }
            }
        }
    }

    Ok(graph)
}

#[cfg(test)]
mod ownership_graph_tests {
    use super::*;
    use crate::{lexer::Lexer, parser::Parser};

    fn setup(input: &str) -> Vec<Statement> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().expect("Failed to tokenize");

        let mut parser = Parser::new(&tokens);

        parser.parse()
    }

    #[test]
    fn test_non_violate_borrowing_rule() {
        // let a = 42;
        // let b = &a;
        // let c = &a;
        // let d = &b;
        let stmts = vec![
            Statement::VariableDecl {
                name: "a".into(),
                is_borrowed: false,
                value: Some(Expression::Number(42)),
            },
            Statement::VariableDecl {
                name: "b".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("a".into())),
            },
            Statement::VariableDecl {
                name: "c".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("a".into())),
            },
            Statement::VariableDecl {
                name: "d".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("b".into())),
            },
        ];

        let graph = build_ownership_graph(&stmts).unwrap();

        println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("global_var".into(), vec!["a".into()]),
                    ("a".into(), vec!["b".into(), "c".into()]),
                    ("b".into(), vec!["d".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }

    #[test]
    fn test_multiple_reference_and_normal_allocation() {
        // let a = 42;
        // let b = &a;
        // let c = &a;
        // let d = &b;
        // let e = 10;
        let stmts = vec![
            Statement::VariableDecl {
                name: "a".into(),
                is_borrowed: false,
                value: Some(Expression::Number(42)),
            },
            Statement::VariableDecl {
                name: "b".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("a".into())),
            },
            Statement::VariableDecl {
                name: "c".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("a".into())),
            },
            Statement::VariableDecl {
                name: "d".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("b".into())),
            },
            Statement::VariableDecl {
                name: "e".into(),
                is_borrowed: false,
                value: Some(Expression::Number(10)),
            },
        ];
        let graph = build_ownership_graph(&stmts).unwrap();

        println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("global_var".into(), vec!["a".into(), "e".into()]),
                    ("a".into(), vec!["b".into(), "c".into()]),
                    ("b".into(), vec!["d".into()]),
                ]
                .into_iter()
                .collect(),
            }
        )
    }

    #[test]
    fn test_include_the_borrowing_of_other_variable() {
        // let x;
        // let y = &x;
        // let z = &y;
        let stmts = vec![
            Statement::VariableDecl {
                name: "x".into(),
                is_borrowed: false,
                value: None,
            },
            Statement::VariableDecl {
                name: "y".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("x".into())),
            },
            Statement::VariableDecl {
                name: "z".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("y".into())),
            },
        ];
        let graph = build_ownership_graph(&stmts).unwrap();

        println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("global_var".into(), vec!["x".into()]),
                    ("x".into(), vec!["y".into()]),
                    ("y".into(), vec!["z".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }

    #[test]
    #[ignore = "should handle the scope correctly"]
    fn test_ownership_graph_with_scope() {
        // let x = 10;
        // {
        //     let y = &x;
        //}
        let stmts = vec![
            Statement::VariableDecl {
                name: "x".into(),
                is_borrowed: false,
                value: Some(Expression::Number(10)),
            },
            Statement::Scope(vec![Statement::VariableDecl {
                name: "y".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("x".into())),
            }]),
        ];

        let graph = build_ownership_graph(&stmts).unwrap();

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("global_var".into(), vec!["x".into()]),
                    ("x".into(), vec!["y".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }

    #[test]
    #[ignore = "should handle the scope correctly"]
    fn test_ownership_graph_referenced_both_inside_and_outside() {
        // let x;
        // {
        //     let y = &x;
        // }
        // let z = &x;
        let stmts = vec![
            Statement::VariableDecl {
                name: "x".into(),
                is_borrowed: false,
                value: None,
            },
            Statement::Scope(vec![Statement::VariableDecl {
                name: "y".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("x".into())),
            }]),
            Statement::VariableDecl {
                name: "z".into(),
                is_borrowed: true,
                value: Some(Expression::Reference("x".into())),
            },
        ];

        let graph = build_ownership_graph(&stmts).unwrap();

        println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("global_var".into(), vec!["x".into()]),
                    // I'm not sure
                    ("x".into(), vec!["y".into(), "z".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }

    #[test]
    #[ignore = "todo"]
    fn test_complex_ownership_inference() {
        let input = r#"
            function foo(a, b) {
                let c = a + b;
                {
                    let result = 0;
                    let d = &c;
                    
                    result = d + 10;

                    return result;
                }

                let f = &c;
            }

            let x = 5;
            let y = 10;
            let z = foo(x, y);

            {
                let a = &x;
                let b = &y;
                let c = &z;

                {
                    function bar(a, b, c) {
                        let d = &a;
                        let e = &b;
                        let f = &c;

                        return d + e + f;
                    }

                    let d = &a;
                    let e = &b;
                    let f = &c;
                }

                let g = &a;
            }

            let h = &x;
        "#;

        let stmts = setup(input);
        let graph = build_ownership_graph(&stmts).unwrap();

        println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    (
                        "global_var".into(),
                        vec!["x".into(), "y".into(), "z".into()]
                    ),
                    (
                        "x".into(),
                        vec!["a".into(), "d".into(), "g".into(), "h".into()]
                    ),
                    ("y".into(), vec!["b".into(), "e".into()]),
                    ("z".into(), vec!["c".into(), "f".into()]),
                    ("a".into(), vec!["d".into()]),
                    ("b".into(), vec!["e".into()]),
                    ("c".into(), vec!["f".into()]),
                    ("d".into(), vec!["g".into()]),
                    ("e".into(), vec!["g".into()]),
                    ("f".into(), vec!["g".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }
}
