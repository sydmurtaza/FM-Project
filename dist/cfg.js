// Control Flow Graph Generator
class CFGGenerator {
  generateCFG(ast) {
    const nodes = [];
    const edges = [];
    let nodeId = 0;
    const addNode = label => {
      nodes.push({
        data: {
          id: `n${nodeId}`,
          label
        }
      });
      return `n${nodeId++}`;
    };
    const processStatements = (statements, parentId, exitId) => {
      let currentId = parentId;
      for (const stmt of statements) {
        const label = this.stmtToString(stmt);
        const newId = addNode(label);
        if (currentId) {
          edges.push({
            data: {
              source: currentId,
              target: newId
            }
          });
        }
        currentId = newId;
        if (stmt.type === 'IfElse') {
          const thenId = addNode('Then');
          const elseId = stmt.elseBranch ? addNode('Else') : exitId;
          edges.push({
            data: {
              source: currentId,
              target: thenId,
              label: 'true'
            }
          });
          edges.push({
            data: {
              source: currentId,
              target: elseId,
              label: 'false'
            }
          });
          const thenExit = processStatements(stmt.thenBranch.statements, thenId, exitId);
          if (stmt.elseBranch) {
            const elseExit = processStatements(stmt.elseBranch.statements, elseId, exitId);
          }
          currentId = exitId;
        } else if (stmt.type === 'While' || stmt.type === 'For') {
          const bodyId = addNode('Body');
          edges.push({
            data: {
              source: currentId,
              target: bodyId,
              label: 'true'
            }
          });
          edges.push({
            data: {
              source: currentId,
              target: exitId,
              label: 'false'
            }
          });
          const bodyExit = processStatements(stmt.body.statements, bodyId, currentId);
        }
      }
      return currentId;
    };
    const entryId = addNode('Entry');
    const exitId = addNode('Exit');
    processStatements(ast.statements, entryId, exitId);
    return {
      nodes,
      edges
    };
  }
  generateSSACFG(ssa) {
    const nodes = [];
    const edges = [];
    let nodeId = 0;
    const addNode = label => {
      nodes.push({
        data: {
          id: `n${nodeId}`,
          label
        }
      });
      return `n${nodeId++}`;
    };
    const entryId = addNode('Entry');
    let currentId = entryId;
    const exitId = addNode('Exit');
    for (const stmt of ssa.statements) {
      const label = this.stmtToString(stmt);
      const newId = addNode(label);
      edges.push({
        data: {
          source: currentId,
          target: newId
        }
      });
      currentId = newId;
    }
    for (const phi of ssa.phiNodes) {
      const label = `${phi.target} = phi(${phi.vars.join(', ')})`;
      const phiId = addNode(label);
      edges.push({
        data: {
          source: currentId,
          target: phiId
        }
      });
      currentId = phiId;
    }
    edges.push({
      data: {
        source: currentId,
        target: exitId
      }
    });
    return {
      nodes,
      edges
    };
  }
  stmtToString(stmt) {
    switch (stmt.type) {
      case 'Assignment':
        return `${stmt.target} := ${this.exprToString(stmt.value)}`;
      case 'ArrayAssignment':
        return `${stmt.array}[${this.exprToString(stmt.index)}] := ${this.exprToString(stmt.value)}`;
      case 'Assert':
        return `assert(${this.exprToString(stmt.condition)})`;
      case 'ArrayAssert':
        return `assert(forall ${stmt.varName} in range(${this.exprToString(stmt.rangeEnd)}): ${this.exprToString(stmt.condition)})`;
      case 'Assume':
        return `assume(${this.exprToString(stmt.condition)})`;
      default:
        return JSON.stringify(stmt);
    }
  }
  exprToString(expr) {
    if (!expr) return '';
    switch (expr.type) {
      case 'Constant':
        return expr.value.toString();
      case 'Variable':
        return expr.name;
      case 'ArrayAccess':
        return `${expr.array}[${this.exprToString(expr.index)}]`;
      case 'Binary':
        return `(${this.exprToString(expr.left)} ${expr.op} ${this.exprToString(expr.right)})`;
      default:
        return JSON.stringify(expr);
    }
  }
}
export default CFGGenerator;