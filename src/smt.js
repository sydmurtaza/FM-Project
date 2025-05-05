// SMT Generator
class SMTGenerator {
    async verifyProgram(ssa, z3) {
        const smt = this.generateSMT(ssa, true);
        const ctx = new z3.Context();
        const solver = new z3.Solver(ctx);
        await z3.loadSMTLIBString(smt, solver);

        const result = await solver.check();
        let examples = [];
        let counterexamples = [];

        if (result === z3.sat) {
            const model = solver.model();
            examples.push(this.extractModel(model, ssa));
        } else if (result === z3.unsat) {
            // Try to find counterexamples by negating assertion
            const negSmt = this.generateSMT(ssa, false);
            const negSolver = new z3.Solver(ctx);
            await z3.loadSMTLIBString(negSmt, negSolver);
            for (let i = 0; i < 2 && (await negSolver.check()) === z3.sat; i++) {
                const model = negSolver.model();
                counterexamples.push(this.extractModel(model, ssa));
                negSolver.add(ctx.not(model));
            }
        }

        ctx.delete();
        return { result: result === z3.sat ? 'Satisfiable' : 'Unsatisfiable', examples, counterexamples, smt };
    }

    async checkEquivalence(ssa1, ssa2, z3) {
        const smt = this.generateEquivalenceSMT(ssa1, ssa2);
        const ctx = new z3.Context();
        const solver = new z3.Solver(ctx);
        await z3.loadSMTLIBString(smt, solver);

        const result = await solver.check();
        let examples = [];
        let counterexamples = [];

        if (result === z3.unsat) {
            examples.push({}); // Programs are equivalent
        } else if (result === z3.sat) {
            for (let i = 0; i < 2 && (await solver.check()) === z3.sat; i++) {
                const model = solver.model();
                counterexamples.push(this.extractModel(model, { statements: [...ssa1.statements, ...ssa2.statements] }));
                solver.add(ctx.not(model));
            }
        }

        ctx.delete();
        return { result: result === z3.unsat ? 'Equivalent' : 'Not Equivalent', examples, counterexamples, smt };
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
}

export default SMTGenerator;