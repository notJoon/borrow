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
    pub fn new(tokens: &'a [TokenType]) -> Self {
        Parser { tokens, pos: 0 }
    }

    /// `parse` method is used to parse the tokens into statements.
    ///
    /// It returns a vector of statements.
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
            Some(TokenType::Return) => self.return_statement(),
            Some(TokenType::Ident(_)) => {
                // Check if we have an identifier followed by an opening parenthesis. If so, treat it as a function call.
                if let Some(TokenType::OpenParen) = self.peek_next() {
                    let name = if let Some(TokenType::Ident(ident)) = self.peek() {
                        ident.clone()
                    } else {
                        panic!("Expected identifier");
                    };
    
                    self.advance(); // Consume the identifier
                    let fc = self.function_call(Some(&TokenType::Ident(name)));

                    self.expect(TokenType::Semicolon, "Expected ';'").unwrap();
    
                    return Statement::Expr(fc);
                }
    
                // handle as variable
                self.variable_declaration()
            },
            Some(TokenType::OpenBrace) => self.scope(),
            _ => panic!("Unexpected token: {:?}", self.peek()),
        }
    }

    fn variable_declaration(&mut self) -> Statement {
        self.expect(TokenType::Let, "Expected 'let'").unwrap();

        let name = self.expect_identifier("Expected variable name");

        // must handle the case where the variable is given a function call
        let value = self.get_variable_value();

        let is_borrowed = matches!(value, Some(Expression::Reference(_)));

        self.expect(TokenType::Semicolon, "Expected ';'").unwrap();

        Statement::VariableDecl {
            name,
            value,
            is_borrowed,
        }
    }

    fn get_variable_value(&mut self) -> Option<Expression> {
        if let Some(TokenType::Equals) = self.peek() {
            self.advance();

            return Some(self.expression());
        }

        None
    }

    /// Parse the definition of a function.
    fn function_definition(&mut self) -> Statement {
        self.expect(TokenType::Fn, "Expected 'function' keyword").unwrap();

        let name = self.expect_identifier("Expected function name");
        self.expect(TokenType::OpenParen, "Expected '('").unwrap();

        let args = self.parse_function_arguments();

        self.expect(TokenType::CloseParen, "Expected ')'").unwrap();

        let body = self.parse_function_body();

        Statement::FunctionDef {
            name,
            args: if args.is_empty() { None } else { Some(args) },
            body,
        }
    }

    /// Parse the function arguments.
    ///
    /// returns a vector of tuples containing the name of the argument and reference status.
    fn parse_function_arguments(&mut self) -> Vec<(String, bool)> {
        let mut args = Vec::new();

        while let Some(token) = self.peek() {
            if matches!(token, TokenType::CloseParen) {
                break;
            }

            let is_ref = self.parse_argument_reference();

            let arg_name = self.expect_identifier("Expected argument name in function definition");

            if self.is_shadowing(&args, &arg_name) {
                panic!("Argument '{arg_name}' is already defined");
            }

            args.push((arg_name, is_ref));

            // consume comma, if there are multiple arguments
            if let Some(TokenType::Comma) = self.peek() {
                self.advance();
            }
        }

        args
    }

    /// Pase an argument reference, consumes the `&` token if exists.
    ///
    /// returns the reference status of the argument.
    fn parse_argument_reference(&mut self) -> bool {
        if !self.is_ref() {
            return false;
        }

        self.advance();

        true
    }

    fn is_ref(&mut self) -> bool {
        matches!(self.peek(), Some(TokenType::Ampersand))
    }

    fn parse_function_body(&mut self) -> Vec<Statement> {
        match self.scope() {
            Statement::Scope(stmts) => stmts,
            _ => panic!("Expected function body"),
        }
    }

    /// checks if te argument name already exists in the list of arguments.
    fn is_shadowing(&mut self, args: &[(String, bool)], arg_name: &str) -> bool {
        args.iter().any(|(name, _)| name == arg_name)
    }

    /// `function_call` method handles function calls.
    fn function_call(&mut self, token: Option<&TokenType>) -> Expression {
        let name = match token {
            Some(TokenType::Ident(name)) => name.clone(),
            _ => self.expect_identifier("Expected function name. got '{token:?}' instead."),
        };

        self.expect(TokenType::OpenParen, "Expected '('").unwrap();

        let mut args = Vec::new();

        if let Some(peek) = self.peek() {
            if peek != &TokenType::CloseParen {
                loop {
                    // args.push(self.expression());
                    if let Some(expr) = self.maybe_function_call(None) {
                        args.push(expr);
                    } else {
                        args.push(self.expression());
                    }

                    match self.peek() {
                        Some(TokenType::Comma) => { self.advance(); }
                        Some(TokenType::CloseParen) => break,
                        _ => panic!("Expected ',' or ')'")
                    }
                }
            }
        }

        self.expect(TokenType::CloseParen, "Expected ')'").unwrap();
        // self.expect(TokenType::Semicolon, "Expected ';'");

        // [UPDATE: 2023-05-31]
        // In the context of expressions, function calls are treated as expressions 
        // rather than standalone statements because they produce a value.
        // So, we need to return an expression instead of a statement.
        Expression::FunctionCall { 
            name: Box::new(Expression::Ident(name)), 
            args
        }
    }

    fn maybe_function_call(&mut self, token: Option<&TokenType>) -> Option<Expression> {
        if matches!(self.peek(), Some(TokenType::OpenParen)) {
            // don't consume here, let function_call handle it
            return Some(self.function_call(token));
        }

        None
    }

    fn return_statement(&mut self) -> Statement {
        self.expect(TokenType::Return, "Expected 'return'").unwrap();

        let expr = matches!(self.peek(), Some(TokenType::Semicolon))
            .then(|| None)
            .unwrap_or_else(|| Some(self.expression()));

        self.expect(TokenType::Semicolon, "Expected ';'").unwrap();

        Statement::Return(expr)
    }

    /// `scope` method handles scopes.
    ///
    /// It takes `mut self` as an argument and returns a statement.
    fn scope(&mut self) -> Statement {
        self.expect(TokenType::OpenBrace, "Expected '{'").unwrap();

        let mut stmts = Vec::new();

        // process statements until we reach the end of the scope(`}`)
        while let Some(token) = self.peek() {
            if matches!(token, TokenType::CloseBrace) {
                break;
            }

            stmts.push(self.statement());
        }

        self.expect(TokenType::CloseBrace, "Expected '}'").unwrap();

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

    fn primary(& mut self) -> Expression {
        match self.peek().cloned() {
            Some(TokenType::Ident(_)) => {
                let token = self.peek().cloned();
    
                self.advance();     // consume the identifier
    
                if let Some(expr) = self.maybe_function_call(token.as_ref()) {
                    return expr;
                }
    
                match token {
                    Some(TokenType::Ident(name)) => Expression::Ident(name),
                    _ => panic!("Unexpected token: {:?}", token),
                }
            }
            Some(TokenType::Number(val)) => {
                self.advance();     // consume the number
    
                Expression::Number(val)
            }
            Some(TokenType::Ampersand) => {
                self.advance();     // consume the `&` token
    
                let name = self.expect_identifier("Expected identifier");
    
                Expression::Reference(name)
            }
            _ => panic!("Unexpected token: {:?}", self.peek())
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
            _ => {
                let prev_token = self.peek_prev().unwrap();
                panic!("{msg}, got {prev_token:?} instead of identifier")
            },
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
        if !self.is_at_end() {
            return Some(&self.tokens[self.pos]);
        }

        None
    }

    fn peek_next(&self) -> Option<&TokenType> {
        self.tokens.get(self.pos + 1)
    }

    fn peek_prev(&self) -> Option<&TokenType> {
        self.tokens.get(self.pos - 1)
    }

    /// `expect` method is used to check if the current token is the expected token.
    fn expect(&mut self, token: TokenType, msg: &str) -> Result<(), String> {
        if Some(&token) != self.peek() {
            panic!("{msg}, got {token:?} instead");
        }

        self.advance();

        Ok(())
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
    fn test_function_declaration() {
        let input = r#"function foo() {}"#;
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: None,
                body: vec![],
            }]
        );
    }

    #[test]
    fn test_function_definition_with_ref_arg() {
        let input = r#"function foo(&x) {}"#;
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: Some(vec![("x".to_string(), true)]),
                body: vec![],
            }]
        );
    }

    #[test]
    fn test_function_declaration_multiple_params_with_no_ref_parameter() {
        let input = r#"function foo(x, y, z) {}"#;
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: Some(vec![
                    ("x".to_string(), false),
                    ("y".to_string(), false),
                    ("z".to_string(), false),
                ]),
                body: Vec::new(),
            }]
        );
    }

    #[test]
    fn test_function_declaration_multiple_params_with_ref_parameter() {
        let input = r#"function foo(x, y, &z) {}"#;
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: Some(vec![
                    ("x".to_string(), false),
                    ("y".to_string(), false),
                    ("z".to_string(), true),
                ]),
                body: Vec::new(),
            }]
        );
    }

    #[test]
    fn test_function_declaration_no_param_and_have_function_body() {
        let input = r#"function foo() { let x = 10; }"#;
        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: None,
                body: vec![Statement::VariableDecl {
                    name: "x".to_string(),
                    value: Some(Expression::Number(10)),
                    is_borrowed: false,
                }],
            }]
        );
    }

    #[test]
    fn test_function_declaration_multiple_params_and_function_body() {
        let input = r#"
            function foo(x, y, z) { 
                let a = 10; 
                let b = 20; 
            }
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: Some(vec![
                    ("x".to_string(), false),
                    ("y".to_string(), false),
                    ("z".to_string(), false)
                ]),
                body: vec![
                    Statement::VariableDecl {
                        name: "a".to_string(),
                        value: Some(Expression::Number(10)),
                        is_borrowed: false,
                    },
                    Statement::VariableDecl {
                        name: "b".to_string(),
                        value: Some(Expression::Number(20)),
                        is_borrowed: false,
                    },
                ],
            }]
        );
    }

    #[test]
    fn test_function_declaration_that_contains_reference() {
        let input = r#"
            function foo(x) { 
                let a = 10; 
                let b = &a;
                let c = &x; 
            }
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: Some(vec![("x".to_string(), false),]),
                body: vec![
                    Statement::VariableDecl {
                        name: "a".to_string(),
                        value: Some(Expression::Number(10)),
                        is_borrowed: false,
                    },
                    Statement::VariableDecl {
                        name: "b".to_string(),
                        value: Some(Expression::Reference("a".to_string())),
                        is_borrowed: true,
                    },
                    Statement::VariableDecl {
                        name: "c".to_string(),
                        value: Some(Expression::Reference("x".to_string())),
                        is_borrowed: true,
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
            vec![Statement::Expr(Expression::FunctionCall {
                name: Box::new(Expression::Ident("foo".to_string())),
                args: vec![Expression::Number(5)],
            })]
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
            vec![Statement::Expr(Expression::FunctionCall {
                name: Box::new(Expression::Ident("foo".to_string())),
                args: vec![
                    Expression::Number(5),
                    Expression::Number(10),
                    Expression::Number(15),
                ],
            })]
        );
    }

    #[test]
    fn test_adding_number_to_function_without_arguments() {
        let input = r#"let a = foo() + 1;"#;
        let tokens = setup(input);

        // println!("{:?}", tokens);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![
                Statement::VariableDecl {
                    name: "a".to_string(),
                    value: Some(Expression::BinaryOp {
                        lhs: Box::new(Expression::FunctionCall {
                            name: Box::new(Expression::Ident("foo".to_string())),
                            args: vec![],
                        }),
                        op: BinaryOp::Plus,
                        rhs: Box::new(Expression::Number(1)),
                    }),
                    is_borrowed: false,
                },
            ]
        )
    }

    #[test]
    fn test_adding_number_to_function_with_single_argument() {
        let input = r#"let a = foo(5) + 1;"#;

        let tokens = setup(input);

        println!("{:?}", tokens);

        let mut parser = Parser::new(&tokens);

        let stmts = parser.parse();


        assert_eq!(
            stmts,
            vec![
                Statement::VariableDecl {
                    name: "a".to_string(),
                    value: Some(Expression::BinaryOp {
                        lhs: Box::new(Expression::FunctionCall {
                            name: Box::new(Expression::Ident("foo".to_string())),
                            args: vec![Expression::Number(5)],
                        }),
                        op: BinaryOp::Plus,
                        rhs: Box::new(Expression::Number(1)),
                    }),
                    is_borrowed: false,
                },
            ]
        )
    }

    #[test]
    fn test_adding_two_functions_with_arguments() {
        let input = r#"let a = foo(3, 4) + bar(5);"#;

        let tokens = setup(input);

        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![
                Statement::VariableDecl {
                    name: "a".to_string(),
                    value: Some(Expression::BinaryOp {
                        lhs: Box::new(Expression::FunctionCall {
                            name: Box::new(Expression::Ident("foo".to_string())),
                            args: vec![Expression::Number(3), Expression::Number(4)],
                        }),
                        op: BinaryOp::Plus,
                        rhs: Box::new(Expression::FunctionCall {
                            name: Box::new(Expression::Ident("bar".to_string())),
                            args: vec![Expression::Number(5)],
                        }),
                    }),
                    is_borrowed: false,
                },
            ]
        )
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
    fn test_parse_reference_and_allocate_new_variable() {
        let input = r#"
            let a = 10;
            let b = &a;
            let c = &b;
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![
                Statement::VariableDecl {
                    name: "a".to_string(),
                    value: Some(Expression::Number(10)),
                    is_borrowed: false,
                },
                Statement::VariableDecl {
                    name: "b".to_string(),
                    value: Some(Expression::Reference("a".to_string())),
                    is_borrowed: true,
                },
                Statement::VariableDecl {
                    name: "c".to_string(),
                    value: Some(Expression::Reference("b".to_string())),
                    is_borrowed: true,
                },
            ]
        )
    }

    #[test]
    fn test_initialize_variable_invalid_way() {
        let input = r#"let a;"#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![Statement::VariableDecl {
                name: "a".to_string(),
                value: None,
                is_borrowed: false,
            }]
        )
    }

    #[test]
    fn test_variable_pass_uninitialized_reference_value() {
        let input = r#"let a = &b;"#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.parse(),
            vec![Statement::VariableDecl {
                name: "a".to_string(),
                value: Some(Expression::Reference("b".to_string())),
                is_borrowed: true,
            }]
        )
    }

    #[test]
    fn test_pass_invalid_declare_to_new_parameter() {
        let input = r#"
            let a;
            let b = &a;
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![
                Statement::VariableDecl {
                    name: "a".to_string(),
                    value: None,
                    is_borrowed: false,
                },
                Statement::VariableDecl {
                    name: "b".to_string(),
                    value: Some(Expression::Reference("a".to_string())),
                    is_borrowed: true,
                },
            ]
        )
    }

    #[test]
    fn test_initialize_variable_and_update_its_value() {
        let input = r#"
            let a = 10;
            let b = a + 5;
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);
        let stmts = parser.parse();

        assert_eq!(
            stmts,
            vec![
                Statement::VariableDecl {
                    name: "a".to_string(),
                    value: Some(Expression::Number(10)),
                    is_borrowed: false,
                },
                Statement::VariableDecl {
                    name: "b".to_string(),
                    value: Some(Expression::BinaryOp {
                        lhs: Box::new(Expression::Ident("a".to_string())),
                        op: BinaryOp::Plus,
                        rhs: Box::new(Expression::Number(5)),
                    }),
                    is_borrowed: false,
                },
            ]
        )
    }

    #[test]
    fn test_parse_return_statement() {
        let input = r#"return 5;"#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.parse(),
            vec![Statement::Return(Some(Expression::Number(5)))]
        )
    }

    #[test]
    fn test_return_in_function_body() {
        let input = r#"
            function foo() {
                return 5;
            }
        "#;

        let tokens = setup(input);
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.parse(),
            vec![Statement::FunctionDef {
                name: "foo".to_string(),
                args: None,
                body: vec![Statement::Return(Some(Expression::Number(5)))],
            }]
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
            Statement::VariableDecl {
                name,
                value,
                is_borrowed,
            } => {
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
            Statement::Expr(Expression::FunctionCall { name, args }) => {
                match &**name {
                    Expression::Ident(name) => assert_eq!(name, "foo"),
                    _ => panic!("Expected identifier"),
                }

                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expression::Reference(name) => assert_eq!(name, "bar"),
                    _ => panic!("Expected reference expression"),
                }
            }
            _ => panic!("Expected function call"),
        }
    }
}
