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


/**
 * @name Unused global variable
 * @description Global variable is defined but not used
 * @kind problem
 * @problem.severity recommendation
 */

import python
import Definition

predicate unused_global(Name unused, GlobalVariable v) {
    not exists(ImportingStmt is | is.contains(unused)) and
    forex(DefinitionNode defn |
        defn.getNode() = unused |
        not defn.getValue().getNode() instanceof FunctionExpr and
        not defn.getValue().getNode() instanceof ClassExpr and
        not exists(Name u | 
            // A use of the variable
            u.uses(v) |
            // That is reachable from this definition, directly
            defn.strictlyReaches(u.getAFlowNode())
            or // indirectly
            defn.getBasicBlock().reachesExit() and u.getScope() != unused.getScope()
        ) and
        not unused.getEnclosingModule().getAnExport() = v.getId() and
        not exists(unused.getParentNode().(ClassDef).getDefinedClass().getADecorator()) and
        not exists(unused.getParentNode().(FunctionDef).getDefinedFunction().getADecorator()) and
        unused.defines(v) and
        not name_acceptable_for_unused_variable(v)
    )
}

from Name unused, GlobalVariable v
where unused_global(unused, v) and
// If unused is part of a tuple, count it as unused if all elements of that tuple are unused.
forall(Name el | el = unused.getParentNode().(Tuple).getAnElt() | unused_global(el, _))
select unused, "The global variable '" + v.getId() + "' is not used."
