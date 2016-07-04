// Copyright 2016 Semmle Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under
// the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

import python

/** A statement */
class Stmt extends Stmt_, AstNode {

    /** Gets the scope immediately enclosing this statement */
    Scope getScope() {
        py_scopes(this, result)
    }

    string toString() {
        result = "Stmt"
    }

    /** Gets the module enclosing this statement */
    Module getEnclosingModule() {
        result = this.getScope().getEnclosingModule()
    }

    Location getLocation() {
    	result = Stmt_.super.getLocation()
    }

    /** Gets an immediate (non-nested) sub-expression of this statement */
    Expr getASubExpression() {
        none()
    }

    /** Gets an immediate (non-nested) sub-statement of this statement */
    Stmt getASubStatement() {
        none()
    }
    
    AstNode getAChildNode() {
        result = this.getASubExpression()
        or
        result = this.getASubStatement()
    }

}

/** A statement that includes a binding (except imports) */
class Assign extends Assign_ {

    /** Use ControlFlowNodes and SsaVariables for data-flow analysis. */
    predicate defines(Variable v) {
        this.getATarget().defines(v)
    }

    Expr getASubExpression() {
        result = this.getATarget() or
        result = this.getValue()
    }

    Stmt getASubStatement() {
        none()
    }
}

/** An augmented assignment statement, such as `x += y` */
class AugAssign extends AugAssign_ {

    Expr getASubExpression() {
        result = this.getOperation()
    }

    Expr getTarget() {
        result = ((BinaryExpr)this.getOperation()).getLeft()
    }

    Expr getValue() {
        result = ((BinaryExpr)this.getOperation()).getRight()
    }

    Stmt getASubStatement() {
        none()
    }
}

/** An exec statement */
class Exec extends Exec_ {

    Expr getASubExpression() {
        result = this.getBody() or
        result = this.getGlobals() or
        result = this.getLocals()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** An except statement (part of a `try` statement), such as `except IOError as err:` */
class ExceptStmt extends ExceptStmt_ {

    /** Gets the immediately enclosing try statement */
    Try getTry() {
        result.getAHandler() = this
    }

    Expr getASubExpression() {
        result = this.getName()
        or
        result = this.getType()
     }

    Stmt getASubStatement() {
        result = this.getAStmt()
     }

}

/** An assert statement, such as `assert a == b, "A is not equal to b"` */
class Assert extends Assert_ {

    Expr getASubExpression() {
        result = this.getMsg() or result = this.getTest()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** A break statement */
class Break extends Break_ {

    Expr getASubExpression() {
        none()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** A continue statement */
class Continue extends Continue_ {

    Expr getASubExpression() {
        none()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** A delete statement, such as `del x[-1]` */
class Delete extends Delete_ {

    Expr getASubExpression() {
        result = this.getATarget()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** An expression statement, such as `len(x)` or `yield y` */
class ExprStmt extends ExprStmt_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** A for statement, such as `for x in y: print(x)` */
class For extends For_ {

    Stmt getASubStatement() {
        result = this.getAStmt() or
        result = this.getAnOrelse()
    }

    Expr getASubExpression() {
        result = this.getTarget() or
        result = this.getIter()
    }
}

/** A global statement, such as `global var` */
class Global extends Global_ {

    Expr getASubExpression() {
        none()
    }

    Stmt getASubStatement() {
        none()
    }
}

/** An if statement, such as `if eggs: print("spam")` */
class If extends If_ {

    Stmt getASubStatement() {
        result = this.getAStmt() or
        result = this.getAnOrelse()
    }

    Expr getASubExpression() {
        result = this.getTest()
    }

    /** Whether this if statement takes the form `if __name__ == "__main__":` */
    predicate isNameEqMain() {
        exists(StrConst m, Name n, Compare c |
            this.getTest() = c and
            c.getOp(0) instanceof Eq and
            (
                c.getLeft() = n and c.getComparator(0) = m
                or
                c.getLeft() = m and c.getComparator(0) = n
            ) and
            n.getId() = "__name__" and
            m.getText() = "__main__"
        )
    }

    /** Whether this if statement starts with the keyword `elif` */
    predicate isElif() {
        /* The Python parser turns all elif chains into nested if-else statements.
         * An `elif` can be indentified as it is the first statement in an `else` block
         * and it is not indented relative to its parent `if`.
         */
        exists(If i | 
            i.getOrelse(0) = this and
            this.getLocation().getStartColumn() = i.getLocation().getStartColumn()
        )
    }

}

/** A nonlocal statement, such as `nonlocal var` */
class Nonlocal extends Nonlocal_ {

    Stmt getASubStatement() {
        none()
    }

    Expr getASubExpression() {
        none()
    }

}

/** A pass statement */
class Pass extends Pass_ {

    Stmt getASubStatement() {
        none()
    }

    Expr getASubExpression() {
        none()
    }

}

/** A print statement (Python 2 only), such as `print 0` */
class Print extends Print_ {

    Stmt getASubStatement() {
        none()
    }

    Expr getASubExpression() {
        result = this.getAValue() or
        result = this.getDest()
    }

}

/** A raise statement, such as `raise CompletelyDifferentException()` */
class Raise extends Raise_ {

    Stmt getASubStatement() {
        none()
    }

    Expr getASubExpression() {
        py_exprs(result, _, this, _)
    }


    /** The exception raised. = getType() for Python2, getExc() for Python3 */
    Expr getException()
    {
        major_version() = 2 and result = this.getType()
        or
        major_version() = 3 and result = this.getExc()
    }
}

/** A return statement, such as return None */
class Return extends Return_ {

    Stmt getASubStatement() {
        none()
    }

    Expr getASubExpression() {
        result = this.getValue()
    }

}

/** A try statement */
class Try extends Try_ {

    Expr getASubExpression() {
        none()
     }

    Stmt getASubStatement() {
        result = this.getAHandler() or
        result = this.getAStmt() or
        result = this.getAFinalstmt() or
        result = this.getAnOrelse()
     }
}

/** A while statement, such as `while parrot_resting():` */
class While extends While_ {

    Expr getASubExpression() {
        result = this.getTest()
    }

    Stmt getASubStatement() {
        result = this.getAStmt() or
        result = this.getAnOrelse()
    }

}

/** A with statement such as `with f as open("file"): text = f.read()` */
class With extends With_ {

    Expr getASubExpression() {
        result = this.getContextExpr() or
        result = this.getOptionalVars()
     }

    Stmt getASubStatement() {
        result = this.getAStmt()
     }

}

/** A plain text used in a template is wrapped in a TemplateWrite statement */
class TemplateWrite extends TemplateWrite_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

    Stmt getASubStatement() {
        none()
    }

}

/** A list of statements */
class StmtList extends StmtList_ {

    /** Whether this list of statements contains s */
    predicate contains(AstNode a) {
        exists(Stmt item | 
            item = this.getAnItem() |
            item = a or item.contains(a)
        )
    }

    Stmt getLastItem() { result = this.getItem(max(int i | exists(this.getItem(i)))) }

}



