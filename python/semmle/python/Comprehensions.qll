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
 
/** Base class for list, set and dictionary comprehensions, and generator expressions. */
abstract class Comp extends Expr {

    abstract Function getFunction();

    /** Gets the iteration variable for the nth innermost generator of this list comprehension */
    Variable getIterationVariable(int n) {
        result.getAnAccess() = this.getNthInnerLoop(n).getTarget()
    }

    private For getNthInnerLoop(int n) {
        n = 0 and result = this.getFunction().getStmt(0)
        or
        result = this.getNthInnerLoop(n-1).getStmt(0)
    }

    /** Gets the iteration variable for a generator of this list comprehension */
    Variable getAnIterationVariable() {
        result = this.getIterationVariable(_)
    }

    /** Gets the scope in which the body of this list comprehension executes. */
    Scope getExecutingScope() {
        result = this.getFunction()
    }

}

/** A list comprehension, such as `[ chr(x) for x in range(ord('A'), ord('Z')+1) ]` */
class ListComp extends ListComp_, Comp {

    Expr getASubExpression() {
        result = this.getAGenerator().getASubExpression() or
        result = this.getElt() or
        result = this.getIterable()
    }

    AstNode getAChildNode() {
        result = this.getAGenerator() or
        result = this.getElt() or
        result = this.getIterable() or
        result = this.getFunction()
    }

    predicate hasSideEffects() {
        any()
    }

    /** Gets the scope in which the body of this list comprehension executes. */
    Scope getExecutingScope() {
        major_version() = 2 and result = this.getScope()
        or
        major_version() = 3 and result = this.getFunction()
    }

    /** Gets the iteration variable for the nth innermost generator of this list comprehension */
    Variable getIterationVariable(int n) {
        major_version() = 2 and result.getAnAccess() = this.getGenerator(n).getTarget()
        or
        major_version() = 3 and result = Comp.super.getIterationVariable(n)
    }

    Function getFunction() {
        result = ListComp_.super.getFunction()
    }

    string toString() {
        result = ListComp_.super.toString()
    }

}


/** A set comprehension such as  `{ v for v in "0123456789" }` */
class SetComp extends SetComp_, Comp {

    Expr getASubExpression() {
        result = this.getIterable()
    }

    AstNode getAChildNode() {
        result = this.getASubExpression() or
        result = this.getFunction()
    }

    predicate hasSideEffects() {
        any()
    }

    Function getFunction() {
        result = SetComp_.super.getFunction()
    }

    string toString() {
        result = SetComp_.super.toString()
    }

}

/** A dictionary comprehension, such as `{ k:v for k, v in enumerate("0123456789") }` */
class DictComp extends DictComp_, Comp {

    Expr getASubExpression() {
        result = this.getIterable()
    }

    AstNode getAChildNode() {
        result = this.getASubExpression() or
        result = this.getFunction()
    }

    predicate hasSideEffects() {
        any()
    }

    Function getFunction() {
        result = DictComp_.super.getFunction()
    }

    string toString() {
        result = DictComp_.super.toString()
    }

}


/** A generator expression, such as `(var for var in iterable)` */
class GeneratorExp extends GeneratorExp_, Comp {

    Expr getASubExpression() {
        result = this.getIterable()
    }

    AstNode getAChildNode() {
        result = this.getASubExpression() or
        result = this.getFunction()
    }

    predicate hasSideEffects() {
        any()
    }

    Function getFunction() {
        result = GeneratorExp_.super.getFunction()
    }

    string toString() {
        result = GeneratorExp_.super.toString()
    }

}

