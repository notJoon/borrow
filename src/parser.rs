use crate::{ast::ASTNode, token::TokenType};

#[derive(Debug, Copy, Clone)]
pub struct Parser<'a> {
    tokens: &'a [TokenType],
    pos: usize,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [TokenType]) -> Self {
        Self { tokens, pos: 0 }
    }

    pub fn parse(&mut self) -> ASTNode {
        self.program()
    }

    fn program(&mut self) -> ASTNode {
        let mut nodes: Vec<ASTNode> = Vec::new();

        while self.pos < self.tokens.len() {
            nodes.push(self.statement());
        }

        ASTNode::Scope(nodes)
    }

    fn statement(&mut self) -> ASTNode {
        match self.current_token() {
            TokenType::Let => self.variable_decl(),
            TokenType::Fn => self.function_decl(),
            TokenType::Ident(name) => {
                let name = name.clone();
                if self.peek_next() == &TokenType::OpenParen {
                    self.consume(
                        TokenType::Ident(name.clone()), 
                        "Expected identifier"
                    );
                    let function_call = self.function_call(name.clone());
                    function_call
                } else {
                    panic!("Expected function call or variable declaration")
                }
            }
            _ => panic!("Expected function call or variable declaration")
        }
    }

    fn variable_decl(&mut self) -> ASTNode {
        self.consume(
            TokenType::Let, 
            "Expected 'let' keyword for variable declaration"
        );

        let name = match self.consume_next("Expected variable name after `let` keyword") {
            TokenType::Ident(name) => name,
            _ => panic!("Expected variable name after `let` keyword"),
        };

        self.consume(
            TokenType::Equals, 
            "Expected `=` after variable name"
        );

        let value = Box::new(self.expression());

        ASTNode::VariableDecl { name, value }
    }

    fn function_decl(&mut self) -> ASTNode {
        self.consume(
            TokenType::Fn,
            "Expected 'function' keyword for function declaration",
        );

        let name = match self.consume_next("Expected function name after `function` keyword") {
            TokenType::Ident(name) => name,
            _ => panic!("Expected function name after `function` keyword"),
        };

        self.consume(
            TokenType::OpenParen, 
            "Expected `(` after function name"
        );

        let mut params = Vec::new();

        while let TokenType::Ident(param) = self.current_token() {
            params.push(param.clone());

            if let TokenType::Comma = self.peek_next() {
                self.consume(
                    TokenType::Comma, 
                    "Expected `,` after function parameter");
            } else {
                break;
            }
        }

        self.consume(
            TokenType::CloseParen,
            "Expected `)` after function parameter",
        );

        let body = Box::new(self.scope());

        ASTNode::FunctionDecl { name, params, body }
    }

    fn function_call(&mut self, name: String) -> ASTNode {
        self.consume(
            TokenType::OpenParen,
            "Expected `(` after function name",
        );
        
        let mut args = Vec::new();

        while self.current_token() != &TokenType::CloseParen {
            args.push(self.expression());

            if let TokenType::Comma = self.current_token() {
                self.consume(
                    TokenType::Comma,
                    "Expected `,` after function argument",
                );
            } else {
                break;
            }
        }

        self.consume(
            TokenType::CloseParen,
            "Expected `)` after function argument",
        );
        
        ASTNode::FunctionCall { name, args }
    }

    fn expression(&mut self) -> ASTNode {
        match self.current_token() {
            TokenType::Number(n) => {
                let n = n.clone();
                self.consume(
                    TokenType::Number(n),
                    "Expected number literal",
                );
                ASTNode::Number(n)
            }
            TokenType::Ident(name) => {
                let name = name.clone();
                if self.peek_next() == &TokenType::OpenParen {
                    self.consume(
                        TokenType::Ident(name.clone()), 
                        "Expected identifier"
                    );
                    let function_call = self.function_call(name);
                    function_call
                } else {
                    ASTNode::Ident(name.clone())
                }
            }
            _ => panic!("Expected number literal or identifier")
        }
    }

    fn current_token(&self) -> &TokenType {
        &self.tokens[self.pos]
    }

    fn peek_next(&self) -> &TokenType {
        &self.tokens[self.pos + 1]
    }

    fn consume(&mut self, token: TokenType, error_msg: &str) {
        if *self.current_token() == token {
            self.pos += 1;
        } else {
            panic!("{error_msg}");
        }
    }

    fn consume_next(&mut self, error_msg: &str) -> TokenType {
        self.pos += 1;

        if self.pos < self.tokens.len() {
            self.current_token().clone()
        } else {
            panic!("{error_msg}")
        }
    }

    fn scope(&mut self) -> ASTNode {
        self.consume(
            TokenType::OpenBrace,
            "Expected `{` at the beginning of a scope",
        );

        let mut nodes = Vec::new();

        while *self.current_token() != TokenType::CloseBrace {
            nodes.push(self.statement());
        }

        self.consume(
            TokenType::CloseBrace, 
            "Expected `}` at the end of a scope"
        );

        ASTNode::Scope(nodes)
    }
}

#[cfg(test)]
mod parser_tests {
    use super::*;

    #[test]
    fn test_parse_variable_declaration() {
        // let x = 5
        let tokens = vec![
            TokenType::Let,
            TokenType::Ident("x".to_string()),
            TokenType::Equals,
            TokenType::Number(5),
        ];

        let mut parser = Parser::new(&tokens);
        let ast = parser.parse();

        assert_eq!(
            ast,
            ASTNode::Scope(vec![
                ASTNode::VariableDecl {
                    name: "x".to_string(),
                    value: Box::new(ASTNode::Number(5)),
                }
            ])
        );
    }

    #[test]
    fn test_parse_function_declaration() {
        // function f(x) { let y = x }
        let tokens = vec![
            TokenType::Fn,
            TokenType::Ident("f".to_string()),
            TokenType::OpenParen,
            TokenType::Ident("x".to_string()),
            TokenType::CloseParen,
            TokenType::OpenBrace,
            TokenType::Let,
            TokenType::Ident("y".to_string()),
            TokenType::Equals,
            TokenType::Ident("x".to_string()),
            TokenType::CloseBrace,
        ];

        let mut parser = Parser::new(&tokens);
        let ast = parser.parse();

        assert_eq!(
            ast,
            ASTNode::Scope(vec![
                ASTNode::FunctionDecl {
                    name: "f".to_string(),
                    params: vec!["x".to_string()],
                    body: Box::new(ASTNode::Scope(vec![
                        ASTNode::VariableDecl {
                            name: "y".to_string(),
                            value: Box::new(ASTNode::Ident("x".to_string())),
                        }
                    ])),
                }
            ])
        );
    }

    #[test]
    fn test_parse_function_call() {
        // f(5)
        let tokens = vec![
            TokenType::Ident("f".to_string()),
            TokenType::OpenParen,
            TokenType::Number(5),
            TokenType::CloseParen,
        ];

        let mut parser = Parser::new(&tokens);
        let ast = parser.parse();

        assert_eq!(
            ast,
            ASTNode::Scope(vec![
                ASTNode::FunctionCall {
                    name: "f".to_string(),
                    args: vec![ASTNode::Number(5)],
                }
            ])
        );
    }
}