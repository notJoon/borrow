use std::collections::BTreeMap;

use crate::{ast::{Statement, Expression}, errors::OwnerGraphError};

#[derive(Debug, PartialEq, Eq, Clone)]
struct OwnershipGraph {
    graph: BTreeMap<String, Vec<String>>,
}

impl OwnershipGraph {
    pub fn new() -> Self {
        Self {
            graph: BTreeMap::new(),
        }
    }

    pub fn add_owner(&mut self, owner: &str, variable: &str) {
        let entry = self.graph.entry(owner.to_string()).or_insert_with(Vec::new);
        if !entry.contains(&variable.to_string()) {
            entry.push(variable.to_string());
        }
    }

    pub fn add_borrower(&mut self, owner: &str, borrower: &str) {
        if let Some(borrowers) = self.graph.get_mut(owner) {
            if !borrowers.contains(&borrower.to_string()) {
                borrowers.push(borrower.to_string());
            }
        }
    }

    pub fn remove_owner(&mut self, owner: &str, variable: &str) {
        if let Some(owners) = self.graph.get_mut(owner) {
            owners.retain(|x| x != variable);
        }
    }

    pub fn remove_borrower(&mut self, owner: &str, borrower: &str) {
        if let Some(borrowers) = self.graph.get_mut(owner) {
            borrowers.retain(|x| x != borrower);
        }
    }
}

fn build_ownership_graph(stmts: &[Statement]) -> Result<OwnershipGraph, OwnerGraphError> {
    let mut graph = OwnershipGraph::new();
    let mut current_owner = "".to_string();

    for stmt in stmts {
        match stmt {
            Statement::VariableDecl { name, is_borrowed, value } => {
                if *is_borrowed {
                    if let Some(Expression::Reference(ref_var)) = value {
                        current_owner = ref_var.clone();
                        graph.add_borrower(&current_owner, name);
                        // current_owner = name.clone();
                    }
                }
                graph.add_owner(&current_owner, name);
                current_owner = name.clone();
            }
            Statement::Scope(scope) =>  {
                let prev_owner = current_owner.clone();
                let mut declared_in_scope = vec![];

                for inner_stmt in scope {
                    if let Statement::VariableDecl { name, value, is_borrowed } = inner_stmt {
                        declared_in_scope.push(name.clone());

                        if *is_borrowed {
                            if let Some(Expression::Reference(ref_var)) = value {
                                current_owner = ref_var.clone();
                                graph.add_borrower(&current_owner, name);
                                // current_owner = name.clone();
                            }
                        }

                        graph.add_owner(&prev_owner, name);
                        current_owner = name.clone();
                    }
                }

                for var in declared_in_scope {
                    graph.remove_owner(&prev_owner, &var);
                    current_owner = prev_owner.clone();
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

    #[test]
    fn test_non_violate_borrowing_rule() {
        let stmts = vec![
            Statement::VariableDecl {
                name: "a".into(),
                is_borrowed: false,
                value: None,
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
        ];
        let graph = build_ownership_graph(&stmts).unwrap();
        
        // println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("".into(), vec!["a".into()]),
                    ("a".into(), vec!["b".into(), "c".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }

    #[test]
    fn test_include_the_borrowing_of_other_variable() {
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

        // println!("{:?}", graph);

        assert_eq!(
            graph,
            OwnershipGraph {
                graph: vec![
                    ("".into(), vec!["x".into()]),
                    ("x".into(), vec!["y".into()]),
                    ("y".into(), vec!["z".into()]),
                ]
                .into_iter()
                .collect(),
            }
        );
    }
}