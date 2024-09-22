#include <iostream>
#include <string>
#include <vector>
#include <cctype>
#include <memory>
#include <stdexcept>

enum class TokenType {
    IDENTIFIER,
    NUMBER,
    PLUS,
    MINUS,
    MULTIPLY,
    DIVIDE,
    LPAREN,
    RPAREN,
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
                tokens.push_back(identifier());
            } else if (std::isdigit(current)) {
                tokens.push_back(number());
            } else {
                switch (current) {
                    case '+': tokens.push_back(Token(TokenType::PLUS, "+")); break;
                    case '-': tokens.push_back(Token(TokenType::MINUS, "-")); break;
                    case '*': tokens.push_back(Token(TokenType::MULTIPLY, "*")); break;
                    case '/': tokens.push_back(Token(TokenType::DIVIDE, "/")); break;
                    case '(': tokens.push_back(Token(TokenType::LPAREN, "(")); break;
                    case ')': tokens.push_back(Token(TokenType::RPAREN, ")")); break;
                    default:
                        throw std::runtime_error("Unexpected character: " + std::string(1, current));
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

class ASTNode {
public:
    virtual ~ASTNode() = default;
    virtual void print(int indent = 0) const = 0;
};

class NumberNode : public ASTNode {
    double value;
public:
    NumberNode(double v) : value(v) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "Number: " << value << std::endl;
    }
};

class BinaryOpNode : public ASTNode {
    std::string op;
    std::unique_ptr<ASTNode> left;
    std::unique_ptr<ASTNode> right;
public:
    BinaryOpNode(const std::string& o, std::unique_ptr<ASTNode> l, std::unique_ptr<ASTNode> r)
        : op(o), left(std::move(l)), right(std::move(r)) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "BinaryOp: " << op << std::endl;
        left->print(indent + 2);
        right->print(indent + 2);
    }
};

class Parser {
    std::vector<Token> tokens;
    size_t current = 0;

public:
    Parser(const std::vector<Token>& t) : tokens(t) {}

    std::unique_ptr<ASTNode> parse() {
        return expression();
    }

private:
    std::unique_ptr<ASTNode> expression() {
        auto node = term();
        while (current < tokens.size() && (match(TokenType::PLUS) || match(TokenType::MINUS))) {
            std::string op = tokens[current - 1].value;
            auto right = term();
            node = std::make_unique<BinaryOpNode>(op, std::move(node), std::move(right));
        }
        return node;
    }

    std::unique_ptr<ASTNode> term() {
        auto node = factor();
        while (current < tokens.size() && (match(TokenType::MULTIPLY) || match(TokenType::DIVIDE))) {
            std::string op = tokens[current - 1].value;
            auto right = factor();
            node = std::make_unique<BinaryOpNode>(op, std::move(node), std::move(right));
        }
        return node;
    }

    std::unique_ptr<ASTNode> factor() {
        if (match(TokenType::NUMBER)) {
            return std::make_unique<NumberNode>(std::stod(tokens[current - 1].value));
        }
        if (match(TokenType::LPAREN)) {
            auto node = expression();
            consume(TokenType::RPAREN, "Expect ')' after expression.");
            return node;
        }
        throw std::runtime_error("Expect number or '('");
    }

    bool match(TokenType type) {
        if (current >= tokens.size()) return false;
        if (tokens[current].type == type) {
            current++;
            return true;
        }
        return false;
    }

    void consume(TokenType type, const std::string& message) {
        if (match(type)) return;
        throw std::runtime_error(message);
    }
};

int main() {
    std::string source = "3 + 4 * (2 - 1)";
    Lexer lexer(source);
    std::vector<Token> tokens = lexer.tokenize();

    std::cout << "Tokens:" << std::endl;
    for (const auto& token : tokens) {
        std::cout << "Type: " << static_cast<int>(token.type) << ", Value: " << token.value << std::endl;
    }

    Parser parser(tokens);
    auto ast = parser.parse();

    std::cout << "\nParse Tree:" << std::endl;
    ast->print();

    return 0;
}