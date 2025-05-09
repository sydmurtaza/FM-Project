// SMT Generator
class SMTGenerator {
    async verifyProgram(ssa, z3) {
        // Simple verification without Z3
        const smt = this.generateSMT(ssa, true);
        let result = 'Satisfiable';
        let examples = [];
        let counterexamples = [];

        // Simulate control flow for simple if-else
        const variables = new Map();
        let skip = false;
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assume') {
                // Evaluate the condition; if false, skip subsequent assignments until next Assume
                const cond = this.evaluateCondition(stmt.condition, variables);
                skip = !cond;
            } else if (skip) {
                continue;
            } else if (stmt.type === 'Assignment') {
                if (stmt.value.type === 'Constant') {
                    variables.set(stmt.target, stmt.value.value);
                } else if (stmt.value.type === 'Binary') {
                    let left, right;
                    if (stmt.value.left.type === 'Constant') {
                        left = stmt.value.left.value;
                    } else if (stmt.value.left.type === 'Variable') {
                        left = variables.get(stmt.value.left.name) ?? 0;
                    } else {
                        left = 0;
                    }
                    if (stmt.value.right.type === 'Constant') {
                        right = stmt.value.right.value;
                    } else if (stmt.value.right.type === 'Variable') {
                        right = variables.get(stmt.value.right.name) ?? 0;
                    } else {
                        right = 0;
                    }
                    let value;
                    switch (stmt.value.op) {
                        case '+': value = left + right; break;
                        case '-': value = left - right; break;
                        case '*': value = left * right; break;
                        case '/': value = right !== 0 ? left / right : 0; break;
                        default: value = 0;
                    }
                    variables.set(stmt.target, value);
                }
            }
        }

        // Check assertions
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assert') {
                const condition = this.evaluateCondition(stmt.condition, variables);
                if (!condition) {
                    result = 'Unsatisfiable';
                    counterexamples.push({
                        variables: Object.fromEntries(variables),
                        failedAssertion: this.exprToString(stmt.condition)
                    });
                    break;
                }
            }
        }

        if (result === 'Satisfiable') {
            examples.push({
                variables: Object.fromEntries(variables),
                description: 'Program execution with current variable values'
            });
        }

        return { result, examples, counterexamples, smt };
    }

    async checkEquivalence(ssa1, ssa2, z3) {
        // Simple equivalence check without Z3
        const smt = this.generateEquivalenceSMT(ssa1, ssa2);
        let result = 'Equivalent';
        let examples = [];
        let counterexamples = [];

        // Compare the final states of both programs
        const vars1 = this.extractVariables(ssa1);
        const vars2 = this.extractVariables(ssa2);

        if (vars1.size !== vars2.size) {
            result = 'Not Equivalent';
            counterexamples.push({
                program1: {
                    variables: Object.fromEntries(vars1),
                    description: 'Final state of Program 1'
                },
                program2: {
                    variables: Object.fromEntries(vars2),
                    description: 'Final state of Program 2'
                },
                difference: 'Different number of variables in final states'
            });
        } else {
            // Check if any variable values differ
            let hasDifference = false;
            const differences = [];
            for (const [key, value1] of vars1) {
                const value2 = vars2.get(key);
                if (value1 !== value2) {
                    hasDifference = true;
                    differences.push({
                        variable: key,
                        program1Value: value1,
                        program2Value: value2
                    });
                }
            }
            if (hasDifference) {
                result = 'Not Equivalent';
                counterexamples.push({
                    program1: {
                        variables: Object.fromEntries(vars1),
                        description: 'Final state of Program 1'
                    },
                    program2: {
                        variables: Object.fromEntries(vars2),
                        description: 'Final state of Program 2'
                    },
                    differences: differences
                });
            } else {
                examples.push({
                    description: 'Programs produce identical final states',
                    variables: Object.fromEntries(vars1)
                });
            }
        }

        return { result, examples, counterexamples, smt };
    }

    evaluateCondition(expr, variables) {
        if (!expr) return true;
        switch (expr.type) {
            case 'Constant':
                return expr.value !== 0;
            case 'Variable':
                return variables.get(expr.name) !== 0;
            case 'Binary':
                const left = this.evaluateCondition(expr.left, variables);
                const right = this.evaluateCondition(expr.right, variables);
                switch (expr.op) {
                    case '==': return left === right;
                    case '<': return left < right;
                    case '>': return left > right;
                    case '<=': return left <= right;
                    case '>=': return left >= right;
                    default: return true;
                }
            default:
                return true;
        }
    }

    extractVariables(ssa) {
        const variables = new Map();
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assignment') {
                if (stmt.value.type === 'Constant') {
                    variables.set(stmt.target, stmt.value.value);
                }
            }
        }
        return variables;
    }

    generateSMT(ssa, checkAssert) {
        let smt = '(set-logic QF_LIA)\n';
        const vars = new Set();
        
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assignment') this.collectVars(stmt.value, vars);
            if (stmt.type === 'ArrayAssignment') {
                this.collectVars(stmt.index, vars);
                this.collectVars(stmt.value, vars);
                vars.add(stmt.array);
            }
            if (stmt.type === 'Assert' || stmt.type === 'ArrayAssert' || stmt.type === 'Assume') {
                this.collectVars(stmt.condition, vars);
                if (stmt.type === 'ArrayAssert') this.collectVars(stmt.rangeEnd, vars);
            }
        }
        
        for (const phi of ssa.phiNodes) {
            vars.add(phi.target);
            phi.vars.forEach(v => vars.add(v));
        }

        vars.forEach(v => {
            if (v.startsWith('arr')) {
                smt += `(declare-fun ${v} () (Array Int Int))\n`;
            } else {
                smt += `(declare-const ${v} Int)\n`;
            }
        });

        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assignment') {
                smt += `(assert (= ${stmt.target} ${this.exprToSMT(stmt.value)}))\n`;
            } else if (stmt.type === 'ArrayAssignment') {
                smt += `(assert (= ${stmt.array} (store ${stmt.array} ${this.exprToSMT(stmt.index)} ${this.exprToSMT(stmt.value)})))\n`;
            } else if (stmt.type === 'Assert' && checkAssert) {
                smt += `(assert ${this.exprToSMT(stmt.condition)})\n`;
            } else if (stmt.type === 'Assume') {
                smt += `(assert ${this.exprToSMT(stmt.condition)})\n`;
            } else if (stmt.type === 'ArrayAssert' && checkAssert) {
                smt += `(assert (forall ((i Int)) (=> (and (>= i 0) (< i ${this.exprToSMT(stmt.rangeEnd)})) ${this.exprToSMT(stmt.condition, { [stmt.varName]: { type: 'Variable', name: 'i' } })})))\n`;
            }
        }

        for (const phi of ssa.phiNodes) {
            smt += `(assert (= ${phi.target} (ite ${this.exprToSMT(phi.condition)} ${phi.vars[0]} ${phi.vars[1]})))\n`;
        }

        smt += '(check-sat)\n(get-model)\n';
        return smt;
    }

    generateEquivalenceSMT(ssa1, ssa2) {
        let smt = '(set-logic QF_LIA)\n';
        const vars1 = new Set();
        const vars2 = new Set();
        
        for (const stmt of ssa1.statements) {
            if (stmt.type === 'Assignment') this.collectVars(stmt.value, vars1);
            if (stmt.type === 'ArrayAssignment') {
                this.collectVars(stmt.index, vars1);
                this.collectVars(stmt.value, vars1);
                vars1.add(stmt.array);
            }
        }
        
        for (const stmt of ssa2.statements) {
            if (stmt.type === 'Assignment') this.collectVars(stmt.value, vars2);
            if (stmt.type === 'ArrayAssignment') {
                this.collectVars(stmt.index, vars2);
                this.collectVars(stmt.value, vars2);
                vars2.add(stmt.array);
            }
        }

        const sharedVars = new Set([...vars1].filter(x => vars2.has(x)));
        const uniqueVars1 = new Set([...vars1].filter(x => !vars2.has(x)));
        const uniqueVars2 = new Set([...vars2].filter(x => !vars1.has(x)));

        [...sharedVars, ...uniqueVars1, ...uniqueVars2].forEach(v => {
            if (v.startsWith('arr')) {
                smt += `(declare-fun ${v} () (Array Int Int))\n`;
            } else {
                smt += `(declare-const ${v} Int)\n`;
            }
        });

        // Add constraints for both programs
        for (const stmt of ssa1.statements) {
            if (stmt.type === 'Assignment') {
                smt += `(assert (= ${stmt.target} ${this.exprToSMT(stmt.value)}))\n`;
            } else if (stmt.type === 'ArrayAssignment') {
                smt += `(assert (= ${stmt.array} (store ${stmt.array} ${this.exprToSMT(stmt.index)} ${this.exprToSMT(stmt.value)})))\n`;
            }
        }

        for (const stmt of ssa2.statements) {
            if (stmt.type === 'Assignment') {
                smt += `(assert (= ${stmt.target} ${this.exprToSMT(stmt.value)}))\n`;
            } else if (stmt.type === 'ArrayAssignment') {
                smt += `(assert (= ${stmt.array} (store ${stmt.array} ${this.exprToSMT(stmt.index)} ${this.exprToSMT(stmt.value)})))\n`;
            }
        }

        // Add phi node constraints
        for (const phi of ssa1.phiNodes.concat(ssa2.phiNodes)) {
            smt += `(assert (= ${phi.target} (ite ${this.exprToSMT(phi.condition)} ${phi.vars[0]} ${phi.vars[1]})))\n`;
        }

        // Add inequality assertion for shared variables
        const diffAssertions = [...sharedVars].map(v => {
            if (v.startsWith('arr')) {
                return `(exists ((i Int)) (and (>= i 0) (< i n) (not (= (select ${v} i) (select ${v} i)))))`;
            } else {
                return `(not (= ${v} ${v}))`;
            }
        }).join(' ');

        smt += `(assert (or ${diffAssertions}))\n`;
        smt += '(check-sat)\n(get-model)\n';
        return smt;
    }

    collectVars(expr, vars) {
        if (!expr) return;
        if (expr.type === 'Variable') vars.add(expr.name);
        if (expr.type === 'ArrayAccess') vars.add(expr.array);
        if (expr.type === 'Binary') {
            this.collectVars(expr.left, vars);
            this.collectVars(expr.right, vars);
        }
        if (expr.type === 'ArrayAccess') this.collectVars(expr.index, vars);
    }

    exprToSMT(expr, varMap = {}) {
        if (!expr) return '';
        switch (expr.type) {
            case 'Constant':
                return expr.value.toString();
            case 'Variable':
                return varMap[expr.name]?.name || expr.name;
            case 'ArrayAccess':
                return `(select ${expr.array} ${this.exprToSMT(expr.index)})`;
            case 'Binary':
                const left = this.exprToSMT(expr.left, varMap);
                const right = this.exprToSMT(expr.right, varMap);
                const op = expr.op === '==' ? '=' : expr.op;
                return `(${op} ${left} ${right})`;
            default:
                return '';
        }
    }

    extractModel(model, ssa) {
        const result = {};
        const vars = new Set();
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assignment') vars.add(stmt.target);
            if (stmt.type === 'ArrayAssignment') vars.add(stmt.array);
            if (stmt.type === 'Assert' || stmt.type === 'ArrayAssert' || stmt.type === 'Assume') {
                this.collectVars(stmt.condition, vars);
                if (stmt.type === 'ArrayAssert') this.collectVars(stmt.rangeEnd, vars);
            }
        }
        for (const phi of ssa.phiNodes) {
            vars.add(phi.target);
            phi.vars.forEach(v => vars.add(v));
        }
        vars.forEach(v => {
            const value = model.eval(v);
            if (value) {
                if (v.startsWith('arr')) {
                    result[v] = 'Array';
                } else {
                    result[v] = value.toString();
                }
            }
        });
        return result;
    }

    exprToString(expr) {
        if (!expr) return '';
        switch (expr.type) {
            case 'Constant':
                return expr.value.toString();
            case 'Variable':
                return expr.name;
            case 'Binary':
                return `(${this.exprToString(expr.left)} ${expr.op} ${this.exprToString(expr.right)})`;
            default:
                return JSON.stringify(expr);
        }
    }
}

// Make it available globally (guarded)
if (!window.SMTGenerator) window.SMTGenerator = SMTGenerator;