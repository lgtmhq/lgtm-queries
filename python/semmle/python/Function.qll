// Copyright 2017 Semmle Ltd.
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

/** A function, independent of defaults and binding.
    It is the syntactic entity that is compiled to a code object. */
class Function extends Function_, Scope, AstNode {

    /** The expression defining this function */
    CallableExpr getDefinition() {
        result = this.getParent()
    }

    /** The scope in which this function occurs, will be a class for a method,
     *  another function for nested functions, generator expressions or comprehensions, 
     * or a module for a plain function. */
    Scope getEnclosingScope() {
        result = this.getParent().(Expr).getScope()
    }

    Scope getScope() {
        result = this.getEnclosingScope()
    }

    /** Whether this function is declared in a class */
    predicate isMethod() {
        exists(Class cls | this.getEnclosingScope() = cls)
    }

    /** Whether this is a special method, that is does its name have the form `__xxx__` (except `__init__`) */
    predicate isSpecialMethod() {
        this.isMethod() and
        exists(string name | this.getName() = name |
            name.matches("\\_\\_%\\_\\_") and
            name != "__init__")
    }

    /** Whether this function is a generator function,
        that is whether it contains a yield or yield-from expression */
    predicate isGenerator() {
        exists(Yield y | y.getScope() = this)
        or
        exists(YieldFrom y | y.getScope() = this)
    }

    /** Whether this function is declared in a class and is named "__init__" */
    predicate isInitMethod() {
        this.isMethod() and this.getName() = "__init__"
    }

    /** Gets a decorator of this function */
    Expr getADecorator() {
        result = ((FunctionExpr)this.getDefinition()).getADecorator()
    }

    /** Gets the name of the nth argument (for simple arguments) */
    string getArgName(int index) {
        result = ((Name)this.getArg(index)).getId()
    }

    Parameter getArgByName(string name) {
        result = this.getAnArg() and
        result.(Name).getId() = name
    }

    Location getLocation() {
        py_scope_location(result, this)
    }

    string toString() {
        result = "Function " + this.getName()
    }

    /** Gets the statements forming the body of this function */
    StmtList getBody() {
        result = Function_.super.getBody()
    }

    /** Gets the nth statement in the function */
    Stmt getStmt(int index) {
        result = Function_.super.getStmt(index)
    }

    /** Gets a statement in the function */
    Stmt getAStmt() {
        result = Function_.super.getAStmt()
    }

    /** Gets the name used to define this function */
    string getName() {
        result = Function_.super.getName()
    }

    /** Gets the metrics for this function */
    FunctionMetrics getMetrics() {
        result = this
    }

    /** Gets the FunctionObject corresponding to this function */
    FunctionObject getFunctionObject() {
    		result.getOrigin() = this.getDefinition()
    }

    /** Whether this function is a procedure, that is, it has no explicit return statement and is not a generator function */
    predicate isProcedure() {
        not exists(this.getReturnNode()) and exists(this.getFallthroughNode()) and not this.isGenerator()
    }

    /** Gets the number of positional parameters */
    int getPositionalParameterCount() {
        result = count(this.getAnArg())
    }

    /** Gets the number of keyword-only parameters */
    int getKeywordOnlyParameterCount() {
        result = count(this.getAKwonlyarg())
    }

    /** Whether this function accepts a variable number of arguments. That is, whether it has a starred (*arg) parameter. */
    predicate hasVarArg() {
        exists(this.getVararg())
    }

    /** Whether this function accepts arbitrary keyword arguments. That is, whether it has a double-starred (**kwarg) parameter. */
    predicate hasKwArg() {
        exists(this.getKwarg())
    }

    AstNode getAChildNode() {
        result = this.getAStmt() or
        result = this.getAnArg() or
        result = this.getVararg() or
        result = this.getKwarg()
    }

    /** Gets the qualified name for this function.
     * Should return the same name as the `__qualname__` attribute on functions in Python 3.
     */
    string getQualifiedName() {
        this.getEnclosingScope() instanceof Module and result = this.getName()
        or
        exists(string enclosing_name |
            enclosing_name = this.getEnclosingScope().(Function).getQualifiedName()
            or
            enclosing_name = this.getEnclosingScope().(Class).getQualifiedName() |
            result = enclosing_name + "." + this.getName()
        )
    }

    /** Gets the nth keyword-only parameter of this function. */
    Name getKeywordOnlyArg(int n) {
        result = Function_.super.getKwonlyarg(n)
    }

    /** Gets a keyword-only parameter of this function. */
    Name getAKeywordOnlyArg() {
        result = this.getKeywordOnlyArg(_)
    }

    Scope getEvaluatingScope() {
        major_version() = 2 and exists(Comp comp | comp.getFunction() = this | result = comp.getEvaluatingScope())
        or
        not exists(Comp comp | comp.getFunction() = this) and result = this
        or 
        major_version() = 3 and result = this
    }

}

/** A def statement. Note that FunctionDef extends Assign as a function definition binds the newly created function */
class FunctionDef extends Assign {

    FunctionDef() {
        /* This is an artificial assignment the rhs of which is a (possibly decorated) FunctionExpr */
        exists(FunctionExpr f | this.getValue() = f or this.getValue() = f.getADecoratorCall())
    }

    string toString() {
        result = "FunctionDef"
    }

    /** Gets the function for this statement */
    Function getDefinedFunction() {
        exists(FunctionExpr func | this.containsInScope(func) and result = func.getInnerScope())
    }

}

class FastLocalsFunction extends Function {
    
    /** A function that uses 'fast' locals, stored in the frame not in a dictionary. */
    FastLocalsFunction () {
        not exists(ImportStar i | i.getScope() = this) 
        and
        not exists(Exec e | e.getScope() = this)
    }

}

/** A parameter. Either a Tuple or a Name (always a Name for Python 3) */
class Parameter extends Parameter_ {

    Parameter() {
        /* Parameter_ is just defined as a Name or Tuple, narrow to actual parameters */
        exists(ParameterList pl | py_exprs(this, _, pl, _))
    }

    Location getLocation() {
        result = this.asName().getLocation()
        or
        result = this.asTuple().getLocation()
    }

    /** Gets this parameter if it is a Name (not a Tuple) */
    Name asName() {
        result = this
    }

    /** Gets this parameter if it is a Tuple (not a Name) */
    Tuple asTuple() {
        result = this
    }

    Expr getDefault() {
        exists(Function f, int n, int c, int d, Arguments args |
            args = f.getDefinition().getArgs() |
            f.getArg(n) = this and
            c = count(f.getAnArg()) and
            d = count(args.getADefault()) and
            result = args.getDefault(d-c+n)
        )
    }

    Variable getVariable() {
        result.getAnAccess() = this.asName()
    }

    int getPosition() {
        exists(Function f |
            f.getArg(result) = this
        )
    }

    /** Holds if this parameter is the first parameter of a method. It is not necessarily called "self" */
    predicate isSelf() {
        exists(Function f |
            f.getArg(0) = this and
            f.isMethod()
        )
    }

}

/** An expression that generates a callable object, either a function expression or a lambda */
abstract class CallableExpr extends Expr {

    /** Gets the parameters of this callable.
     *  This predicate is called getArgs(), rather than getParameters() for compatibility with Python's AST module. */
    abstract Arguments getArgs();

    /** Gets the function scope of this code expression. */
    abstract Function getInnerScope();

}

/** An (artificial) expression corresponding to a function definition. */
class FunctionExpr extends FunctionExpr_, CallableExpr {

    Expr getASubExpression() {
        result = this.getArgs().getASubExpression() or
        result = this.getReturns()
    }

    predicate hasSideEffects() {
        any()
    }

    Call getADecoratorCall() {
        result.getArg(0) = this or
        result.getArg(0) = this.getADecoratorCall()
    }

    /** Gets a decorator of this function expression */
    Expr getADecorator() {
        result = this.getADecoratorCall().getFunc()
    }

    AstNode getAChildNode() {
        result = this.getASubExpression()
        or
        result = this.getInnerScope()
    }

    Function getInnerScope() {
        result = FunctionExpr_.super.getInnerScope()
    }

    Arguments getArgs() {
        result = FunctionExpr_.super.getArgs()
    }

}

/** A lambda expression, such as lambda x:x*x  */
class Lambda extends Lambda_, CallableExpr {

    /** Gets the expression to the right of the colon in this lambda expression */
    Expr getExpression() {
        exists(Return ret | ret = this.getInnerScope().getStmt(0) |
                            result = ret.getValue())
    }

    Expr getASubExpression() {
        result = this.getArgs().getASubExpression()
    }

    AstNode getAChildNode() {
        result = this.getASubExpression() or
        result = this.getInnerScope()
    }

    Function getInnerScope() {
        result = Lambda_.super.getInnerScope()
    }

    Arguments getArgs() {
        result = Lambda_.super.getArgs()
    }

}

/** The arguments in a function definition */
class Arguments extends Arguments_ {

    Expr getASubExpression() {
        result = this.getAKwDefault() or
        result = this.getAnAnnotation() or
        result = this.getKwargannotation() or
        result = this.getVarargannotation() or
        result = this.getADefault()
    }
}


