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

/**
 * @name Unused static function
 * @description A static function that is never called or accessed may be an
 *              indication that the code is incomplete or has a typo.
 * @description Static functions that are never called or accessed.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/unused-static-function
 * @tags efficiency
 *       useless-code
 *       external/cwe/cwe-561
 */
import default

predicate immediatelyReachableFunction(Function f) {
    not f.isStatic()
    or exists(BlockExpr be | be.getFunction() = f)
    or f instanceof MemberFunction
    or f instanceof TemplateFunction
    or f.getFile() instanceof HeaderFile
    or f.getAnAttribute().hasName("constructor")
    or f.getAnAttribute().hasName("destructor")
    or f.getAnAttribute().hasName("used")
    or f.getAnAttribute().hasName("unused")
}

predicate immediatelyReachableVariable(Variable v) {
    (v.isTopLevel() and not v.isStatic())
    or exists(v.getDeclaringType())
    or v.getFile() instanceof HeaderFile
    or v.getAnAttribute().hasName("used")
    or v.getAnAttribute().hasName("unused")
}

class ImmediatelyReachableThing extends Thing {
    ImmediatelyReachableThing() {
        immediatelyReachableFunction(this) or
        immediatelyReachableVariable(this)
    }
}

predicate reachableThing(Thing t) {
    t instanceof ImmediatelyReachableThing or
    exists(Thing mid | reachableThing(mid) and mid.callsOrAccesses() = t)
}

class Thing extends Locatable {
    Thing() {
        this instanceof Function or
        this instanceof Variable
    }

    string getName() {
        result = this.(Function).getName() or
        result = this.(Variable).getName()
    }

    Thing callsOrAccesses() {
        this.(Function).calls((Function)result) or
        this.(Function).accesses((Function)result) or
        this.(Function).accesses((Variable)result) or
        (exists(Access a | this.(Variable).getInitializer().getExpr().getAChild*() = a
                         | result = a.getTarget()))
    }
}

class FunctionToRemove extends Function {
    FunctionToRemove() {
        this.hasDefinition()
        and not reachableThing(this)
    }

    Thing getOther() {
        result.callsOrAccesses+() = this
        and this != result
        // We will already be reporting the enclosing function of a
        // local variable, so don't also report the variable
        and not result instanceof LocalVariable
    }
}

from FunctionToRemove f, string clarification, Thing other
where if exists(f.getOther())
      then (clarification = " ($@ must be removed at the same time)"
        and other = f.getOther())
      else (clarification = "" and other = f)
select f,
       "Static function " + f.getName() + " is unreachable" + clarification,
       other,
       other.getName()

