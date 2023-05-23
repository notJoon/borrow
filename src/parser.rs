use crate::{
    ast::{BinaryOp, Expression, Statement},
    token::TokenType,
};

/// `Parser` struct is used to parse tokens into statements.
///
/// It takes a slice of tokens as an argument.
pub struct Parser<'a> {
    tokens: &'a [TokenType],
    pos: usize,
}

impl<'a> Parser<'a> {
    /// `new` method is used to create a new parser.
    ///
    /// It takes a slice of tokens as an argument and returns a new parser.
    ///     
    /// # Example
    ///
    /// ```
    /// use parser::Parser;
    /// use token::TokenType;
    ///
    /// let tokens = vec![
    ///     TokenType::Let,
    ///     TokenType::Ident("x".to_string()),
    ///     TokenType::Equals,
    ///     TokenType::Number(10)
    /// ];
    ///
    /// let parser = Parser::new(&tokens);
    /// ```
    pub fn new(tokens: &'a [TokenType]) -> Self {
        Parser { tokens, pos: 0 }
    }

    /// `parse` method is used to parse the tokens into statements.
    ///
    /// It returns a vector of statements.
    ///
    /// # Example
    ///
    /// ```
    /// use parser::Parser;
    /// use token::TokenType;
    ///
    /// let tokens = vec![
    ///    TokenType::Let,
    ///   TokenType::Ident("x".to_string()),
    ///    TokenType::Equals,
    ///   TokenType::Number(10),
    /// ];
    ///
    /// let mut parser = Parser::new(&tokens);
    /// let stmts = parser.parse();
    /// ```
    pub fn parse(&mut self) -> Vec<Statement> {
        let mut stmts = Vec::new();

        while !self.is_at_end() {
            stmts.push(self.statement());
        }

        stmts
    }

    /// `statement` method is used to parse a statement.
    ///
    /// A statement can be a function definition, a variable definition, a function call, or a scope.
    fn statement(&mut self) -> Statement {
        match self.peek() {
            Some(TokenType::Fn) => self.function_definition(),
            Some(TokenType::Let) => self.variable_declaration(),
            Some(TokenType::Ident(_)) => self.function_call(),
            Some(TokenType::OpenBrace) => self.scope(),
            _ => panic!("Unexpected token: {:?}", self.peek()),
        }
    }

    fn variable_declaration(&mut self) -> Statement {
        self.expect(TokenType::Let, "Expected 'let'");

        let name = self.expect_identifier("Expected variable name");
        let value = if let Some(TokenType::Equals) = self.peek() {
            self.advance();
            Some(self.expression())
        } else {
            None
        };

        let is_borrowed = matches!(value, Some(Expression::Reference(_)));

        self.expect(TokenType::Semicolon, "Expected ';'");

        Statement::VariableDecl {
            name,
            value,
            is_borrowed,
        }
    }

    fn function_definition(&mut self) -> Statement {
        self.expect(TokenType::Fn, "Expected 'function'");

        let name = self.expect_identifier("Expected function name");
        self.expect(TokenType::OpenParen, "Expected '('");

        // store the function arguments in a vector
        let mut args = Vec::new();

        // If there is at least one identifier token, it is an argument name
        while let Some(token) = self.peek() {
            match token {
                TokenType::Ident(_) => {
                    args.push(self.expect_identifier("Expected argument name"));
                }
                TokenType::Ampersand => {
                    // consume the `&`
                    self.advance();

                    let arg_name = format!("&{}", self.expect_identifier("Expected argument name"));
                    args.push(arg_name);
                }
                _ => break,
            }

            // continue processing comma-separated arguments
            if let Some(TokenType::Comma) = self.peek() {
                // consume the comma
                self.advance(); 
            }
        }

        self.expect(TokenType::CloseParen, "Expected ')'");

        // Process the body of the function, which is a scope
        let body = match self.scope() {
            Statement::Scope(stmts) => stmts,
            _ => panic!("Expected scope"),
        };

        Statement::FunctionDef {
            name,
            args: if args.is_empty() { None } else { Some(args) },
            body,
        }
    }

    /// `function_call` method handles function calls.
    ///
    /// It takes mut self as an argument and returns a statement.
    fn function_call(&mut self) -> Statement {
        let name = self.expect_identifier("Expected function name");
        self.expect(TokenType::OpenParen, "Expected '('");

        let mut args = Vec::new();
        while let Some(token) = self.peek() {
            if matches!(token, TokenType::CloseParen) {
                break;
            }

            args.push(self.expression());

            // consume comma, if there are multiple arguments
            if let Some(TokenType::Comma) = self.peek() {
                self.advance();
            }
        }

        self.expect(TokenType::CloseParen, "Expected ')'");
        self.expect(TokenType::Semicolon, "Expected ';'");

        Statement::FunctionCall { name, args }
    }

    /// `scope` method handles scopes.
    ///
    /// It takes `mut self` as an argument and returns a statement.
    fn scope(&mut self) -> Statement {
        self.expect(TokenType::OpenBrace, "Expected '{'");

        let mut stmts = Vec::new();

        // process statements until we reach the end of the scope(`}`)
        while let Some(token) = self.peek() {
            if matches!(token, TokenType::CloseBrace) {
                break;
            }

            stmts.push(self.statement());
        }

        self.expect(TokenType::CloseBrace, "Expected '}'");

        // create a new scope statement with the collected statements.
        Statement::Scope(stmts)
    }

    fn expression(&mut self) -> Expression {
        let mut expr = self.primary();

        // process binary operators and references(`&`)
        while let Some(token) = self.peek() {
            match token {
                TokenType::Plus | TokenType::Minus | TokenType::Asterisk | TokenType::Slash => {
                    let op = self.consume_operator();
                    let right = self.primary();

                    // create a new binary operation expression
                    expr = Expression::BinaryOp {
                        lhs: Box::new(expr),
                        op,
                        rhs: Box::new(right),
                    };
                }
                _ => break,
            }
        }

        expr
    }

    fn consume_operator(&mut self) -> BinaryOp {
        let token = self.advance();

        match token {
            Some(TokenType::Plus) => BinaryOp::Plus,
            Some(TokenType::Minus) => BinaryOp::Minus,
            Some(TokenType::Asterisk) => BinaryOp::Asterisk,
            Some(TokenType::Slash) => BinaryOp::Slash,
            _ => panic!("Unexpected token: {token:?}"),
        }
    }

    fn primary(&mut self) -> Expression {
        let token = self.advance();

        match token {
            Some(TokenType::Ident(name)) => Expression::Ident(name.clone()),
            Some(TokenType::Number(value)) => Expression::Number(*value),
            Some(TokenType::Ampersand) => {
                let var_name = match self.advance() {
                    Some(TokenType::Ident(name)) => name.clone(),
                    _ => panic!("Expected identifier after `&`"),
                };

                Expression::Reference(var_name.clone())
            }
            _ => panic!("Unexpected token: {token:?}"),
        }
    }

    /// `identifier` method is used to parse an identifier.
    fn identifier(&mut self) -> Expression {
        let name = self.expect_identifier("Expected identifier");

        Expression::Ident(name)
    }

    /// `expect_identifier` method is used to parse an identifier.
    ///
    /// It returns the name of the identifier.
    fn expect_identifier(&mut self, msg: &str) -> String {
        match self.advance() {
            Some(TokenType::Ident(name)) => name.clone(),
            _ => panic!("{msg}"),
        }
    }

    /// `is_at_end` method is used to check if the parser has reached the end of the tokens.
    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    /// `advance` method is used to move the parser forward by one token.
    fn advance(&mut self) -> Option<&TokenType> {
        let token = self.tokens.get(self.pos);
        self.pos += 1;

        token
    }

    /// `peek` method is used to get the current token without moving the parser forward.
    fn peek(&self) -> Option<&TokenType> {
        if self.is_at_end() {
            None
        } else {
            Some(&self.tokens[self.pos])
        }
    }

    /// `expect` method is used to check if the current token is the expected token.
    fn expect(&mut self, token: TokenType, msg: &str) -> () {
        if Some(&token) != self.peek() {
            panic!("{msg}");
        }

        self.advance();
    }
}

#[cfg(test)]
mod parser_test {
    use super::*;
    use crate::lexer::Lexer;

    fn setup(input: &str) -> Vec<TokenType> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().expect("Failed to tokenize");

        tokens
    }

    #[test]
    fn test_basic_math_operation() {
        let input = r#"let x = 5 + 10 - 4;"#;
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::VariableDecl {
                name: "x".to_string(),
                value: Some(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Number(5)),
                        op: BinaryOp::Plus,
                        rhs: Box::new(Expression::Number(10)),
                    }),
                    op: BinaryOp::Minus,
                    rhs: Box::new(Expression::Number(4)),
                }),
                is_borrowed: false,
            }]
        )
    }

    #[test]
    fn test_parse_variable() {
        let input = "let x = 10;";
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::VariableDecl {
                name: "x".to_string(),
                value: Some(Expression::Number(10)),
                is_borrowed: false,
            }]
        );
    }

    #[test]
    #[ignore = "todo"]
    fn test_function_declaration() {
        let input = r#"
            fn foo(x) {
                
            }
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: Some(vec!["x".to_string(), "y".to_string()]),
                body: vec![
                    Statement::VariableDecl {
                        name: "z".to_string(),
                        value: Some(Expression::Ident("x".to_string())),
                        is_borrowed: false,
                    },
                    Statement::VariableDecl {
                        name: "a".to_string(),
                        value: Some(Expression::Ident("y".to_string())),
                        is_borrowed: false,
                    },
                ],
            }]
        );
    }

    #[test]
    fn test_function_call_one_argument() {
        let input = r#"foo(5);"#;
        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionCall {
                name: "foo".to_string(),
                args: vec![Expression::Number(5)],
            }]
        );
    }

    #[test]
    fn test_function_call_multiple_args() {
        let input = r#"foo(5, 10, 15);"#;
        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionCall {
                name: "foo".to_string(),
                args: vec![
                    Expression::Number(5),
                    Expression::Number(10),
                    Expression::Number(15),
                ],
            }]
        );
    }

    #[test]
    fn test_scope() {
        let input = r#"
            {
                let x = 5;
                let y = 10;
            }
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::Scope(vec![
                Statement::VariableDecl {
                    name: "x".to_string(),
                    value: Some(Expression::Number(5)),
                    is_borrowed: false,
                },
                Statement::VariableDecl {
                    name: "y".to_string(),
                    value: Some(Expression::Number(10)),
                    is_borrowed: false,
                },
            ])]
        )
    }

    #[test]
    fn parse_reference_variable() {
        // let foo = &bar;
        let tokens = vec![
            TokenType::Let,
            TokenType::Ident("foo".to_string()),
            TokenType::Equals,
            TokenType::Ampersand,
            TokenType::Ident("bar".to_string()),
            TokenType::Semicolon,
        ];

        let mut parser = Parser::new(&tokens);
        let statements = parser.parse();

        assert_eq!(statements.len(), 1);
        match &statements[0] {
            Statement::VariableDecl { name, value, is_borrowed } => {
                assert_eq!(name, "foo");
                assert_eq!(is_borrowed, &true);
                match value {
                    Some(Expression::Reference(name)) => assert_eq!(name, "bar"),
                    _ => panic!("Expected reference expression"),
                }
            }
            _ => panic!("Expected variable declaration"),
        }
    }

    #[test]
    fn parse_function_definition_with_reference_argument() {
        // fn foo(&bar) {}
        let tokens = vec![
            TokenType::Fn,
            TokenType::Ident("foo".to_string()),
            TokenType::OpenParen,
            TokenType::Ampersand,
            TokenType::Ident("bar".to_string()),
            TokenType::CloseParen,
            TokenType::OpenBrace,
            TokenType::CloseBrace,
        ];

        let mut parser = Parser::new(&tokens);
        let statements = parser.parse();

        assert_eq!(statements.len(), 1);
        match &statements[0] {
            Statement::FunctionDef { name, args, .. } => {
                assert_eq!(name, "foo");
                assert!(args.is_some());
                assert_eq!(args.as_ref().unwrap().len(), 1);
                assert_eq!(args.as_ref().unwrap()[0], "&bar");
            },
            _ => panic!("Expected function definition"),
        }
    }

    #[test]
    fn parse_function_call_with_reference_argument() {
        // foo(&bar);
        let tokens = vec![
            TokenType::Ident("foo".to_string()),
            TokenType::OpenParen,
            TokenType::Ampersand,
            TokenType::Ident("bar".to_string()),
            TokenType::CloseParen,
            TokenType::Semicolon,
        ];

        let mut parser = Parser::new(&tokens);
        let statements = parser.parse();

        assert_eq!(statements.len(), 1);
        match &statements[0] {
            Statement::FunctionCall { name, args } => {
                assert_eq!(name, "foo");
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expression::Reference(name) => assert_eq!(name, "bar"),
                    _ => panic!("Expected reference expression"),
                }
            },
            _ => panic!("Expected function call"),
        }
    }
}
