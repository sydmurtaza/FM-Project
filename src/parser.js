// Parser class implementation
class Parser {
    constructor(input) {
        this.tokens = this.tokenize(input);
        this.pos = 0;
    }

    tokenize(input) {
        const tokenRegex = /\s*(:=|if|else|while|for|assert|range|[(){};,\[\]]|[<>]=?|==|[+\-*/]|\w+|\d+)/g;
        let tokens = [];
        let match;
        while ((match = tokenRegex.exec(input)) !== null) {
            tokens.push(match[0]);
        }
        return tokens;
    }

    peek() {
        return this.pos < this.tokens.length ? this.tokens[this.pos] : null;
    }

    consume(expected) {
        if (this.peek() === expected) {
            return this.tokens[this.pos++];
        }
        throw new Error(`Expected ${expected}, got ${this.peek()}`);
    }

    parseProgram() {
        const statements = [];
        while (this.peek() && this.peek() !== '}') {
            statements.push(this.parseStatement());
        }
        return { type: 'Program', statements };
    }

    parseStatement() {
        if (this.peek() === 'if') {
            return this.parseIfElse();
        } else if (this.peek() === 'while') {
            return this.parseWhile();
        } else if (this.peek() === 'for') {
            return this.parseFor();
        } else if (this.peek() === 'assert') {
            return this.parseAssert();
        } else {
            return this.parseAssignment();
        }
    }

    parseAssignment() {
        const target = this.peek();
        if (!/^[a-zA-Z][\w]*$/.test(target) && target !== '[') {
            throw new Error(`Invalid variable name: ${target}`);
        }
        if (target === '[') {
            this.consume('[');
            const array = this.consume(/^[a-zA-Z][\w]*$/);
            const index = this.parseExpression();
            this.consume(']');
            this.consume(':=');
            const value = this.parseExpression();
            this.consume(';');
            return { type: 'ArrayAssignment', array, index, value };
        }
        this.pos++;
        this.consume(':=');
        const value = this.parseExpression();
        this.consume(';');
        return { type: 'Assignment', target, value };
    }

    parseIfElse() {
        this.consume('if');
        this.consume('(');
        const condition = this.parseExpression();
        this.consume(')');
        this.consume('{');
        const thenBranch = this.parseProgram();
        this.consume('}');
        let elseBranch = null;
        if (this.peek() === 'else') {
            this.consume('else');
            this.consume('{');
            elseBranch = this.parseProgram();
            this.consume('}');
        }
        return { type: 'IfElse', condition, thenBranch, elseBranch };
    }

    parseWhile() {
        this.consume('while');
        this.consume('(');
        const condition = this.parseExpression();
        this.consume(')');
        this.consume('{');
        const body = this.parseProgram();
        this.consume('}');
        return { type: 'While', condition, body };
    }

    parseFor() {
        this.consume('for');
        this.consume('(');
        const init = this.parseAssignment();
        const condition = this.parseExpression();
        this.consume(';');
        const update = this.parseAssignment();
        this.consume(')');
        this.consume('{');
        const body = this.parseProgram();
        this.consume('}');
        return { type: 'For', init, condition, update, body };
    }

    parseAssert() {
        this.consume('assert');
        this.consume('(');
        if (this.peek() === 'for') {
            this.consume('for');
            this.consume('(');
            const varName = this.consume(/^[a-zA-Z][\w]*$/);
            this.consume('in');
            this.consume('range');
            this.consume('(');
            const rangeEnd = this.parseExpression();
            this.consume(')');
            this.consume(')');
            this.consume(':');
            const condition = this.parseExpression();
            this.consume(')');
            this.consume(';');
            return { type: 'ArrayAssert', varName, rangeEnd, condition };
        }
        const condition = this.parseExpression();
        this.consume(')');
        this.consume(';');
        return { type: 'Assert', condition };
    }

    parseExpression() {
        let left = this.parseTerm();
        while (['+', '-', '<', '>', '<=', '>=', '=='].includes(this.peek())) {
            const op = this.peek();
            this.pos++;
            const right = this.parseTerm();
            left = { type: 'Binary', op, left, right };
        }
        return left;
    }

    parseTerm() {
        const token = this.peek();
        if (/^\d+$/.test(token)) {
            this.pos++;
            return { type: 'Constant', value: parseInt(token) };
        } else if (/^[a-zA-Z][\w]*$/.test(token)) {
            this.pos++;
            return { type: 'Variable', name: token };
        } else if (token === '[') {
            this.consume('[');
            const array = this.consume(/^[a-zA-Z][\w]*$/);
            const index = this.parseExpression();
            this.consume(']');
            return { type: 'ArrayAccess', array, index };
        } else if (token === '(') {
            this.consume('(');
            const expr = this.parseExpression();
            this.consume(')');
            return expr;
        }
        throw new Error(`Invalid expression token: ${token}`);
    }
}

export default Parser;