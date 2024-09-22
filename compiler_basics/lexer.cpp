#include <iostream>
#include <string>
#include <vector>
#include <cctype>

enum class TokenType {
    IDENTIFIER,
    NUMBER,
    PLUS,
    MINUS,
    MULTIPLY,
    DIVIDE,
    LPAREN,
    RPAREN,
    EQUALS,
    END_OF_FILE
};

struct Token {
    TokenType type;
    std::string value;
    Token(TokenType t, const std::string& v) : type(t), value(v) {}
};

class Lexer {
private:
    std::string input;
    size_t position;

public:
    Lexer(const std::string& source) : input(source), position(0) {}

    std::vector<Token> tokenize() {
        std::vector<Token> tokens;
        
        while (position < input.length()) {
            char current = input[position];

            if (std::isspace(current)) {
                position++;
            } else if (std::isalpha(current)) {
                // std::isalpha(int ch) is a function 
                //that checks whether a given character is an alphabetic character
                tokens.push_back(identifier());
            } else if (std::isdigit(current)) {
                tokens.push_back(number());
            } else {
                switch (current) {
                    case '+':tokens.push_back(Token(TokenType::PLUS, "+"));break;
                    case '-':tokens.push_back(Token(TokenType::MINUS, "-"));break;
                    case '*':tokens.push_back(Token(TokenType::MULTIPLY, "*"));break;
                    case '/':tokens.push_back(Token(TokenType::DIVIDE, "/"));break;
                    case '(':tokens.push_back(Token(TokenType::LPAREN, "(")); break;
                    case ')':tokens.push_back(Token(TokenType::RPAREN, ")"));break;
                    case '=':tokens.push_back(Token(TokenType::EQUALS, "="));break;
                    default:
                        std::cerr << "Unexpected character: " << current << std::endl;
                        break;
                }
                position++;
            }
        }

        tokens.push_back(Token(TokenType::END_OF_FILE, ""));
        return tokens;
    }

private:
    Token identifier() {
        size_t start = position;
        while (position < input.length() && (std::isalnum(input[position]) || input[position] == '_')) {
            position++;
        }
        return Token(TokenType::IDENTIFIER, input.substr(start, position - start));
    }

    Token number() {
        size_t start = position;
        while (position < input.length() && std::isdigit(input[position])) {
            position++;
        }
        return Token(TokenType::NUMBER, input.substr(start, position - start));
    }
};

int main() {
    std::string source = "x = 10 + 20 * (30 - 5)";
    Lexer lexer(source);
    std::vector<Token> tokens = lexer.tokenize();

    for (const auto& token : tokens) {
        std::cout << "Type: " << static_cast<int>(token.type) << ", Value: " << token.value << std::endl;
    }

    return 0;
}