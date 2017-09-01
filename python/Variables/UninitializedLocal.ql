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
 * @name Potentially uninitialized local variable
 * @description Using a local variable before it is initialized causes an UnboundLocalError.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision high
 * @id py/uninitialized-local-variable
 */

import python
import Loop

predicate defined_and_used_in_condition(Name use) {
    exists(If i1, If i2, Name defn | i1 != i2 and defn.defines(use.getVariable()) |
        i1.getASubStatement().contains(defn) and i2.getASubStatement().contains(use)
    )
}

predicate never_returns(FunctionObject func) {
    exists(Function f | f = func.getFunction() |
                        not exists(f.getANormalExit())
                        or
                        exists(Call c, Attribute a, string name, ClassObject cls | c.getScope() = f and a = c.getFunc() and a.getName() = name and
                                                               ((Name)a.getObject()).getId() = "self" and
                                                               cls.getPyClass() = f.getScope() and never_returns(cls.lookupAttribute(name))))
}

predicate calls_exit_func(Function f) {
    exists(Call c, Attribute a | c.getScope() = f and a = c.getFunc() and a.getName() = "exit" and ((Name)a.getObject()).getId() = "sys")
    or
    exists(Call c, Attribute a, string name, ClassObject cls | c.getScope() = f and a = c.getFunc() and a.getName() = name and
                                                               ((Name)a.getObject()).getId() = "self" and
                                                               cls.getPyClass() = f.getScope() and never_returns(cls.lookupAttribute(name)))
}

predicate nonlocal(NameNode use) {
    exists(Nonlocal l, Variable v | 
        v.getAUse() = use and
        l.getAVariable() = v
    )
}

FunctionObject non_returning_method() {
    result.neverReturns() and
    result.isNormalMethod()
}

predicate maybe_not_a_successor(RaisingNode r, ControlFlowNode s) {
    r.unlikelySuccessor(s)
    or
    /* A call to a method that we cannot identify, and there 
     * exists a method of the same name that doesn't return.
     */
    not exists(FunctionObject f | f.getACall() = r) and
    s = r.getANormalSuccessor() and
    r.(CallNode).getFunction().(AttrNode).getName() = non_returning_method().getName()
}

predicate undefined_ssa(SsaVariable l) {
    l.maybeUndefined() and
    forall(ControlFlowNode incoming |
        incoming = l.getDefinition().getAPredecessor() |
        not maybe_not_a_successor(incoming, l.getDefinition())
    )
}

predicate possibly_uninitialized_local(NameNode use) {
    exists(SsaVariable l, Function f | f = use.getScope() and l.getAUse() = use |
        l.getVariable() instanceof FastLocalVariable and
        undefined_ssa(l) and
        not defined_and_used_in_condition(use.getNode()) and
        not calls_exit_func(f) and
        not probably_defined_in_loop(use.getNode())
    ) and
    not nonlocal(use)
}

/** Since any use of a local will raise if it is undefined, then
 * any use dominated by another use of the same variable must be defined.
 */
predicate uninitialized_local(NameNode use) {
    possibly_uninitialized_local(use) and
    not exists(NameNode other, LocalVariable v |
        other != use and
        other.uses(v) and use.uses(v) and
        other.dominates(use) and
        possibly_uninitialized_local(other)
    )
}

predicate explicitly_guarded(NameNode u) {
    exists(Try t |
        t.getBody().contains(u.getNode()) and
        t.getAHandler().getType().refersTo(theNameErrorType())
    )
}

from NameNode u
where uninitialized_local(u) and not explicitly_guarded(u)
select u.getNode(), "Local variable '" + u.getId() + "' may be used before it is initialized."

