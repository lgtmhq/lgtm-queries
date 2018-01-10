// Copyright 2018 Semmle Ltd.
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
 * @name Variable defined multiple times
 * @description Assignment to a variable occurs multiple times without any intermediate use of that variable
 * @kind problem
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-563
 * @problem.severity warning
 * @sub-severity low
 * @precision very-high
 * @id py/multiple-definition
 */

import python
import Definition

predicate multiply_defined(AstNode asgn1, AstNode asgn2, Variable v) {
    /* Must be redefined on all possible paths in the CFG corresponding to the original source.
     * For example, splitting may create a path where `def` is unconditionally redefined, even though
     * it is not in the original source. */
    forex(Definition def, Definition redef |
        def.getVariable() = v and
        def = asgn1.getAFlowNode() and
        redef = asgn2.getAFlowNode() |
        def.isUnused() and
        def.getARedef() = redef and
        def.isRelevant()
    )
}

predicate simple_literal(Expr e) {
    e.(Num).getN() = "0" or
    e instanceof NameConstant or
    e instanceof List and not exists(e.(List).getAnElt()) or
    e instanceof Tuple and not exists(e.(Tuple).getAnElt()) or
    e instanceof Dict and not exists(e.(Dict).getAKey()) or
    e.(StrConst).getText() = ""
}

/** A multiple definition is 'uninteresting' if it sets a variable to a 
 * simple literal before reassigning it.
 * x = None
 * if cond:
 *     x = value1
 * else:
 *     x = value2
 */
predicate uninteresting_definition(AstNode asgn1) {
    exists(AssignStmt a | 
        a.getATarget() = asgn1 |
        simple_literal(a.getValue())
    )
}


from AstNode asgn1, AstNode asgn2, Variable v
where
    multiply_defined(asgn1, asgn2, v) and
    forall(Name el | el = asgn1.getParentNode().(Tuple).getAnElt() | multiply_defined(el, _, _)) and
    not uninteresting_definition(asgn1)
select asgn1, "This assignment to '" + v.getId() + "' is unnecessary as it is redefined $@ before this value is used.", asgn2 as t, "here"
