
// SSA Converter and Optimizer
class SSAConverter {
    constructor() {
        this.varVersions = new Map(); // Tracks current version of each variable
        this.statements = [];         // Stores generated SSA statements
        this.currentBlock = null;     // Tracks current basic block (for phi nodes)
    }

    // Generates a fresh SSA variable name
    getVersion(varName) {
        const count = this.varVersions.get(varName) || 0;
        this.varVersions.set(varName, count + 1);
        return `${varName}${count}`;
    }

    // Main entry point for conversion
    convertProgram(ast, unrollDepth = 1) {
        this.statements = [];
        this.varVersions.clear();
        this.convertStatements(ast.statements, unrollDepth);
        return { statements: this.statements };
    }

    // Converts a list of statements to SSA form
    convertStatements(statements, unrollDepth) {
        for (const stmt of statements) {
            this.convertStatement(stmt, unrollDepth);
        }
    }

    // Handles individual statement types
    convertStatement(stmt, unrollDepth) {
        switch (stmt.type) {
            case 'Assignment':
                this.handleAssignment(stmt);
                break;
            case 'ArrayAssignment':
                this.handleArrayAssignment(stmt);
                break;
            case 'IfElse':
                this.handleIfElse(stmt, unrollDepth);
                break;
            case 'While':
                this.unrollWhile(stmt, unrollDepth);
                break;
            case 'For':
                this.unrollFor(stmt, unrollDepth);
                break;
            case 'Assert':
                this.handleAssert(stmt);
                break;
            case 'ArrayAssert':
                this.handleArrayAssert(stmt);
                break;
            default:
                throw new Error(`Unsupported statement type: ${stmt.type}`);
        }
    }

    // ========== Core Conversion Methods ========== //

    handleAssignment(stmt) {
        const value = this.convertExpression(stmt.value);
        const newVar = this.getVersion(stmt.target);
        this.statements.push({ type: 'Assignment', target: newVar, value });
    }

    handleArrayAssignment(stmt) {
        const arrayValue = this.convertExpression(stmt.value);
        const index = this.convertExpression(stmt.index);
        const newArray = this.getVersion(stmt.array);
        this.statements.push({ 
            type: 'ArrayAssignment', 
            array: newArray, 
            index, 
            value: arrayValue 
        });
    }

    handleIfElse(stmt, unrollDepth) {
        const condition = this.convertExpression(stmt.condition);
        const originalVersions = new Map(this.varVersions);

        // Convert THEN branch
        this.convertStatements(stmt.thenBranch.statements, unrollDepth);
        const thenVersions = new Map(this.varVersions);

        // Convert ELSE branch (if exists)
        this.varVersions = new Map(originalVersions);
        const elseVersions = new Map(originalVersions);
        if (stmt.elseBranch) {
            this.convertStatements(stmt.elseBranch.statements, unrollDepth);
            elseVersions.set(...this.varVersions);
        }

        // Insert phi nodes for variables that diverged
        this.varVersions = new Map(originalVersions);
        for (const varName of originalVersions.keys()) {
            const origVersion = originalVersions.get(varName) || 0;
            const thenVersion = thenVersions.get(varName) || origVersion;
            const elseVersion = elseVersions.get(varName) || origVersion;

            const thenVar = thenVersion > origVersion 
                ? `${varName}${thenVersion}` 
                : `${varName}${origVersion}`;
            const elseVar = elseVersion > origVersion
                ? `${varName}${elseVersion}`
                : `${varName}${origVersion}`;

            if (thenVar !== elseVar) {
                const newVar = this.getVersion(varName);
                this.statements.push({
                    type: 'Phi',
                    target: newVar,
                    vars: [thenVar, elseVar],
                    condition
                });
            }
        }
    }

    unrollWhile(whileStmt, depth) {
        const condition = this.convertExpression(whileStmt.condition);
        const loopVarVersions = new Map();

        for (let i = 0; i < depth; i++) {
            const preLoopVersions = new Map(this.varVersions);
            this.statements.push({ type: 'Assume', condition });
            this.convertStatements(whileStmt.body.statements, depth);

            // Track variables modified in the loop
            this.varVersions.forEach((v, k) => {
                if (v > (preLoopVersions.get(k) || 0)) {
                    loopVarVersions.set(k, `${k}${v}`);
                }
            });

            this.varVersions = new Map(preLoopVersions);
        }

        // Add phi nodes for loop-carried dependencies
        for (const [varName, postVar] of loopVarVersions) {
            const newVar = this.getVersion(varName);
            this.statements.push({
                type: 'Phi',
                target: newVar,
                vars: [`${varName}${this.varVersions.get(varName) || 0}`, postVar],
                condition
            });
        }

        // Add loop exit condition
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
        const loopVarVersions = new Map();

        for (let i = 0; i < depth; i++) {
            const preLoopVersions = new Map(this.varVersions);
            this.statements.push({ type: 'Assume', condition });
            this.convertStatements(forStmt.body.statements, depth);
            this.convertStatement(forStmt.update, depth);

            // Track modified variables
            this.varVersions.forEach((v, k) => {
                if (v > (preLoopVersions.get(k) || 0)) {
                    loopVarVersions.set(k, `${k}${v}`);
                }
            });

            this.varVersions = new Map(preLoopVersions);
        }

        // Add phi nodes
        for (const [varName, postVar] of loopVarVersions) {
            const newVar = this.getVersion(varName);
            this.statements.push({
                type: 'Phi',
                target: newVar,
                vars: [`${varName}${this.varVersions.get(varName) || 0}`, postVar],
                condition
            });
        }

        // Add exit condition
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

    handleAssert(stmt) {
        this.statements.push({
            type: 'Assert',
            condition: this.convertExpression(stmt.condition)
        });
    }

    handleArrayAssert(stmt) {
        this.statements.push({
            type: 'ArrayAssert',
            varName: stmt.varName,
            rangeEnd: this.convertExpression(stmt.rangeEnd),
            condition: this.convertExpression(stmt.condition)
        });
    }

    // ========== Expression Conversion ========== //

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
            case 'Unary':
                return {
                    type: 'Unary',
                    op: expr.op,
                    arg: this.convertExpression(expr.arg)
                };
            default:
                throw new Error(`Unsupported expression type: ${expr.type}`);
        }
    }
}

// ========== Optimizer ========== //
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
            const stmt = ssa.statements[i];
            
            if (stmt.type === 'Assignment' && stmt.value.type === 'Constant') {
                constants.set(stmt.target, stmt.value.value);
            } 
            else if (stmt.type === 'Assignment' && stmt.value.type === 'Variable' && constants.has(stmt.value.name)) {
                ssa.statements[i] = {
                    type: 'Assignment',
                    target: stmt.target,
                    value: { type: 'Constant', value: constants.get(stmt.value.name) }
                };
                changed = true;
            }
            else if (stmt.type === 'Assignment' && stmt.value.type === 'Binary') {
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
            case '!=': return left !== right ? 1 : 0;
            default: return null;
        }
    }

    deadCodeElimination(ssa) {
        const usedVars = new Set();
        
        // Collect all used variables
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assert' || stmt.type === 'Assume') {
                this.collectUsedVars(stmt.condition, usedVars);
            }
            else if (stmt.type === 'Assignment' || stmt.type === 'Phi') {
                this.collectUsedVars(stmt.value, usedVars);
                usedVars.add(stmt.target);
            }
            else if (stmt.type === 'ArrayAssignment') {
                this.collectUsedVars(stmt.index, usedVars);
                this.collectUsedVars(stmt.value, usedVars);
                usedVars.add(stmt.array);
            }
        }

        // Remove unused assignments
        const newStatements = [];
        for (const stmt of ssa.statements) {
            if (stmt.type === 'Assignment' && !usedVars.has(stmt.target)) {
                continue;
            }
            newStatements.push(stmt);
        }

        const changed = newStatements.length !== ssa.statements.length;
        ssa.statements = newStatements;
        return changed;
    }

    collectUsedVars(expr, usedVars) {
        if (!expr) return;
        
        if (expr.type === 'Variable') {
            usedVars.add(expr.name);
        }
        else if (expr.type === 'Binary') {
            this.collectUsedVars(expr.left, usedVars);
            this.collectUsedVars(expr.right, usedVars);
        }
        else if (expr.type === 'Unary') {
            this.collectUsedVars(expr.arg, usedVars);
        }
        else if (expr.type === 'ArrayAccess') {
            usedVars.add(expr.array);
            this.collectUsedVars(expr.index, usedVars);
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
                }
                else {
                    exprMap.set(exprKey, stmt.target);
                }
            }
        }
        
        return changed;
    }
}

// Export for both browser and Node.js
if (typeof window !== 'undefined') {
    window.SSAConverter = SSAConverter;
    window.SSAOptimizer = SSAOptimizer;
}
if (typeof module !== 'undefined' && module.exports) {
    module.exports = { SSAConverter, SSAOptimizer };
}