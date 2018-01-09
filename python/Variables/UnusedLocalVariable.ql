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
 * @name Unused local variable
 * @description Local variable is defined but not used
 * @kind problem
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-563
 * @problem.severity recommendation
 * @sub-severity high
 * @precision very-high
 * @id py/unused-local-variable
 */

import python
import Definition

predicate unused_local(Name unused, LocalVariable v) {
    forex(Definition def |
        def.getNode() = unused |
        def.getVariable() = v and
        def.isUnused() and
        not exists(def.getARedef()) and
        def.isRelevant() and
        not exists(def.getNode().getParentNode().(FunctionDef).getDefinedFunction().getADecorator()) and
        not exists(def.getNode().getParentNode().(ClassDef).getDefinedClass().getADecorator())
    )
}


from Name unused, LocalVariable v
where unused_local(unused, v) and 
// If unused is part of a tuple, count it as unused if all elements of that tuple are unused.
forall(Name el | el = unused.getParentNode().(Tuple).getAnElt() | unused_local(el, _))
select unused, "The value assigned to local variable '" + v.getId() + "' is never used."
