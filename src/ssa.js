// SSA Converter and Optimizer
class SSAConverter {
    constructor() {
        this.varVersions = new Map();
        this.phiNodes = [];
        this.statements = [];
    }

    getVersion(varName) {
        const count = this.varVersions.get(varName) || 0;
        this.varVersions.set(varName, count + 1);
        return `${varName}${count}`;
    }

    convertProgram(ast, unrollDepth) {
        this.statements = [];
        this.phiNodes = [];
        this.varVersions.clear();
        this.convertStatements(ast.statements, unrollDepth);
        return { statements: this.statements, phiNodes: this.phiNodes };
    }

    convertStatements(statements, unrollDepth) {
        for (const stmt of statements) {
            this.convertStatement(stmt, unrollDepth);
        }
    }

    convertStatement(stmt, unrollDepth) {
        switch (stmt.type) {
            case 'Assignment':
                const value = this.convertExpression(stmt.value);
                const newVar = this.getVersion(stmt.target);
                this.statements.push({ type: 'Assignment', target: newVar, value });
                break;
            case 'ArrayAssignment':
                const arrayValue = this.convertExpression(stmt.value);
                const index = this.convertExpression(stmt.index);
                const newArray = this.getVersion(stmt.array);
                this.statements.push({ type: 'ArrayAssignment', array: newArray, index, value: arrayValue });
                break;
            case 'IfElse':
                const condition = this.convertExpression(stmt.condition);
                const thenVars = new Map();
                const elseVars = new Map();
                const originalVersions = new Map(this.varVersions);
                this.convertStatements(stmt.thenBranch.statements, unrollDepth);
                stmt.thenBranch.statements.forEach(() => this.varVersions.forEach((v, k) => thenVars.set(k, `${k}${v-1}`)));
                this.varVersions = new Map(originalVersions);
                if (stmt.elseBranch) {
                    this.convertStatements(stmt.elseBranch.statements, unrollDepth);
                    stmt.elseBranch.statements.forEach(() => this.varVersions.forEach((v, k) => elseVars.set(k, `${k}${v-1}`)));
                }
                this.varVersions = new Map(originalVersions);
                for (const [varName] of originalVersions) {
                    const thenVar = thenVars.get(varName) || `${varName}${originalVersions.get(varName)}`;
                    const elseVar = elseVars.get(varName) || `${varName}${originalVersions.get(varName)}`;
                    if (thenVar !== elseVar) {
                        const newVar = this.getVersion(varName);
                        this.phiNodes.push({ type: 'Phi', target: newVar, vars: [thenVar, elseVar], condition });
                    }
                }
                break;
            case 'While':
                this.unrollWhile(stmt, unrollDepth);
                break;
            case 'For':
                this.unrollFor(stmt, unrollDepth);
                break;
            case 'Assert':
                this.statements.push({ type: 'Assert', condition: this.convertExpression(stmt.condition) });
                break;
            case 'ArrayAssert':
                this.statements.push({
                    type: 'ArrayAssert',
                    varName: stmt.varName,
                    rangeEnd: this.convertExpression(stmt.rangeEnd),
                    condition: this.convertExpression(stmt.condition)
                });
                break;
        }
    }

    convertExpression(expr) {
        if (!expr) return null;
        switch (expr.type) {
            case 'Constant':
                return expr;
            case 'Variable':
                const version = this.varVersions.get(expr.name) || 0;
                return { type: 'Variable', name: `${expr.name}${version}` };
            case 'ArrayAccess':
                return { 
                    type: 'ArrayAccess', 
                    array: this.getVersion(expr.array), 
                    index: this.convertExpression(expr.index) 
                };
            case 'Binary':
                return {
                    type: 'Binary',
                    op: expr.op,
                    left: this.convertExpression(expr.left),
                    right: this.convertExpression(expr.right)
                };
            default:
                return expr;
        }
    }

    unrollWhile(whileStmt, depth) {
        const condition = this.convertExpression(whileStmt.condition);
        for (let i = 0; i < depth; i++) {
            const originalVersions = new Map(this.varVersions);
            this.statements.push({ type: 'Assume', condition });
            this.convertStatements(whileStmt.body.statements, depth);
            this.varVersions = new Map(originalVersions);
        }
        this.statements.push({ 
            type: 'Assume', 
            condition: { 
                type: 'Binary', 
                op: '==', 
                left: condition, 
                right: { type: 'Constant', value: 0 } 
            } 
        });
    }

    unrollFor(forStmt, depth) {
        this.convertStatement(forStmt.init, depth);
        const condition = this.convertExpression(forStmt.condition);
        for (let i = 0; i < depth; i++) {
            const originalVersions = new Map(this.varVersions);
            this.statements.push({ type: 'Assume', condition });
            this.convertStatements(forStmt.body.statements, depth);
            this.convertStatement(forStmt.update, depth);
            this.varVersions = new Map(originalVersions);
        }
        this.statements.push({ 
            type: 'Assume', 
            condition: { 
                type: 'Binary', 
                op: '==', 
                left: condition, 
                right: { type: 'Constant', value: 0 } 
            } 
        });
    }
}

class SSAOptimizer {
    optimize(ssa) {
        let changed = true;
        while (changed) {
            changed = false;
            changed |= this.constantPropagation(ssa);
            changed |= this.deadCodeElimination(ssa);
            changed |= this.commonSubexpressionElimination(ssa);
        }
        return ssa;
    }

    constantPropagation(ssa) {
        const constants = new Map();
        let changed = false;
        for (let i = 0; i < ssa.statements.length; i++) {
            let stmt = ssa.statements[i];
            if (stmt.type === 'Assignment' && stmt.value.type === 'Constant') {
                constants.set(stmt.target, stmt.value.value);
            } else if (stmt.type === 'Assignment' && stmt.value.type === 'Binary') {
                const left = stmt.value.left.type === 'Variable' ? constants.get(stmt.value.left.name) : null;
                const right = stmt.value.right.type === 'Variable' ? constants.get(stmt.value.right.name) : null;
                if (left !== null && right !== null) {
                    const result = this.evaluateBinary(stmt.value.op, left, right);
                    if (result !== null) {
                        ssa.statements[i] = { 
                            type: 'Assignment', 
                            target: stmt.target, 
                            value: { type: 'Constant', value: result } 
                        };
                        constants.set(stmt.target, result);
                        changed = true;
                    }
                }
            }
        }
        return changed;
    }

    evaluateBinary(op, left, right) {
        switch (op) {
            case '+': return left + right;
            case '-': return left - right;
            case '*': return left * right;
            case '/': return right !== 0 ? Math.floor(left / right) : null;
            case '<': return left < right ? 1 : 0;
            case '>': return left > right ? 1 : 0;
            case '<=': return left <= right ? 1 : 0;
            case '>=': return left >= right ? 1 : 0;
            case '==': return left === right ? 1 : 0;
            default: return null;
        }
    }

    deadCodeElimination(ssa) {
        const usedVars = new Set();
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assert' || stmt.type === 'ArrayAssert') {
                this.collectUsedVars(stmt.condition, usedVars);
            }
            if (stmt.type === 'ArrayAssignment') {
                this.collectUsedVars(stmt.index, usedVars);
                this.collectUsedVars(stmt.value, usedVars);
            }
        }
        for (const phi of ssa.phiNodes) {
            usedVars.add(phi.target);
            phi.vars.forEach(v => usedVars.add(v));
        }
        let changed = false;
        ssa.statements = ssa.statements.filter(stmt => {
            if (stmt.type === 'Assignment' && !usedVars.has(stmt.target)) {
                changed = true;
                return false;
            }
            return true;
        });
        return changed;
    }

    collectUsedVars(expr, usedVars) {
        if (!expr) return;
        if (expr.type === 'Variable') {
            usedVars.add(expr.name);
        } else if (expr.type === 'ArrayAccess') {
            this.collectUsedVars(expr.index, usedVars);
        } else if (expr.type === 'Binary') {
            this.collectUsedVars(expr.left, usedVars);
            this.collectUsedVars(expr.right, usedVars);
        }
    }

    commonSubexpressionElimination(ssa) {
        const exprMap = new Map();
        let changed = false;
        for (let i = 0; i < ssa.statements.length; i++) {
            const stmt = ssa.statements[i];
            if (stmt.type === 'Assignment' && stmt.value.type === 'Binary') {
                const exprKey = JSON.stringify(stmt.value);
                if (exprMap.has(exprKey)) {
                    ssa.statements[i] = { 
                        type: 'Assignment', 
                        target: stmt.target, 
                        value: { type: 'Variable', name: exprMap.get(exprKey) } 
                    };
                    changed = true;
                } else {
                    exprMap.set(exprKey, stmt.target);
                }
            }
        }
        return changed;
    }
}

// Make them available globally (guarded)
if (!window.SSAConverter) window.SSAConverter = SSAConverter;
if (!window.SSAOptimizer) window.SSAOptimizer = SSAOptimizer;