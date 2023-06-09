#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenType {
    Let,
    Fn,
    Return,
    Ident(String),
    Equals,
    Number(i32),
    OpenBrace,
    CloseBrace,
    OpenParen,
    CloseParen,
    Comma,
    Semicolon,
    Plus,
    Minus,
    Slash,
    Asterisk,
    Ampersand,
}
