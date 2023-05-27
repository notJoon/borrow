use crate::token::TokenType;

pub struct Lexer<'a> {
    input: &'a str,
    chars: std::str::Chars<'a>,
    current_char: Option<char>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        let mut chars = input.chars();
        let current_char = chars.next();

        Lexer {
            input,
            chars,
            current_char,
        }
    }

    pub fn next_token(&mut self) -> Option<TokenType> {
        while let Some(c) = self.current_char {
            if c.is_whitespace() {
                self.skip_whitespace();
                continue;
            }

            if c.is_alphabetic() {
                return Some(self.identifier());
            }

            if c.is_numeric() {
                return Some(self.number());
            }

            let token = match c {
                '=' => TokenType::Equals,
                '{' => TokenType::OpenBrace,
                '}' => TokenType::CloseBrace,
                '(' => TokenType::OpenParen,
                ')' => TokenType::CloseParen,
                ',' => TokenType::Comma,
                ';' => TokenType::Semicolon,
                '+' => TokenType::Plus,
                '-' => TokenType::Minus,
                '*' => TokenType::Asterisk,
                '/' => TokenType::Slash,
                '&' => TokenType::Ampersand,
                _ => panic!("Invalid character: {c}"),
            };

            self.current_char = self.chars.next();
            return Some(token);
        }

        None
    }

    pub fn tokenize(&mut self) -> Result<Vec<TokenType>, String> {
        let mut tokens = Vec::new();

        while let Some(token) = self.next_token() {
            tokens.push(token);
        }

        Ok(tokens)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.current_char {
            if !c.is_whitespace() {
                break;
            }

            self.current_char = self.chars.next();
        }
    }

    fn identifier(&mut self) -> TokenType {
        let mut value = String::new();

        while let Some(c) = self.current_char {
            if !c.is_alphabetic() {
                break;
            }

            value.push(c);
            self.current_char = self.chars.next();
        }

        match value.as_str() {
            "let" => TokenType::Let,
            "function" => TokenType::Fn,
            "return" => TokenType::Return,
            _ => TokenType::Ident(value),
        }
    }

    fn number(&mut self) -> TokenType {
        let mut value = String::new();

        while let Some(c) = self.current_char {
            if !c.is_numeric() {
                break;
            }

            value.push(c);
            self.current_char = self.chars.next();
        }

        TokenType::Number(value.parse().unwrap())
    }
}

#[cfg(test)]
mod lexer_tests {
    use super::*;

    macro_rules! assert_tokens {
        ($lexer:expr, $( $token:expr ), *) => {
            $(
                assert_eq!($lexer.next_token().unwrap(), $token);
            )*
            assert!($lexer.next_token().is_none());
        };
    }

    #[test]
    fn test_lexer() {
        let input = r#"let a = 5"#;
        let mut lexer = Lexer::new(input);

        assert_tokens!(
            lexer,
            TokenType::Let,
            TokenType::Ident("a".into()),
            TokenType::Equals,
            TokenType::Number(5)
        );
    }

    #[test]
    fn test_lexer_with_scope() {
        let input = r#"
            let a = 5 
            { 
                let b = a 
            }
        "#;
        let mut lexer = Lexer::new(input);

        assert_tokens!(
            lexer,
            TokenType::Let,
            TokenType::Ident("a".into()),
            TokenType::Equals,
            TokenType::Number(5),
            TokenType::OpenBrace,
            TokenType::Let,
            TokenType::Ident("b".into()),
            TokenType::Equals,
            TokenType::Ident("a".into()),
            TokenType::CloseBrace
        );
    }

    #[test]
    #[should_panic(expected = "Invalid character: @")]
    fn test_lexer_with_invalid_char() {
        let input = r#"let @ = 5"#;
        let mut lexer = Lexer::new(input);

        while let Some(_) = lexer.next_token() {}
    }

    #[test]
    fn test_return_keyword() {
        let input = r#"return 5;"#;

        let mut lexer = Lexer::new(input);

        assert_tokens!(
            lexer,
            TokenType::Return,
            TokenType::Number(5),
            TokenType::Semicolon
        );
    }
}
