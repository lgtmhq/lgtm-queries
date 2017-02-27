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

predicate undefined_ssa(SsaVariable l) {
    l.maybeUndefined() and
    forall(ControlFlowNode incoming |
        incoming = l.getDefinition().getAPredecessor() |
        not ((RaisingNode)incoming).unlikelySuccessor(l.getDefinition())
    )
}

predicate uninitialized_local(Name use) {
    exists(SsaVariable l, Function f | f = use.getScope() and l.getAUse() = use.getAFlowNode() |
        l.getVariable() instanceof FastLocalVariable and
        undefined_ssa(l) and
        not defined_and_used_in_condition(use) and
        not calls_exit_func(f) and
        not probably_defined_in_loop(use)
    )
}

private predicate first_use_in_a_block(ControlFlowNode use) {
    exists(SsaVariable v, BasicBlock b, int i |
        i = min(int j | b.getNode(j) = v.getAUse()) and b.getNode(i) = use
    )
}

predicate first_uninitialized_local(Name use) {
    uninitialized_local(use) and
    exists(SsaVariable v, ControlFlowNode first_use |
        use.getAFlowNode() = first_use and v.getAUse() = first_use |
        first_use_in_a_block(first_use) and
        not exists(ControlFlowNode other | 
            other = v.getAUse() and
            other.getBasicBlock().strictlyDominates(first_use.getBasicBlock())
        )
    )
}

from Name u
where first_uninitialized_local(u)
select u, "Local variable '" + u.getId() + "' may be used before it is initialized."

