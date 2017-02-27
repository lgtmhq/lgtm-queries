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
 * @name Module is imported more than once
 * @description Importing a module a second time has no effect and impairs readability
 * @kind problem
 * @tags maintainability
 *       useless-code
 * @problem.severity recommendation
 * @sub-severity high
 * @precision very-high
 */

import python

predicate is_simple_import(Import imp) {
    not exists(Attribute a | imp.contains(a))
}

predicate double_import(Import original, Import duplicate, Module m) {
    original != duplicate and
    is_simple_import(original) and is_simple_import(duplicate) and
    /* Imports import the same thing */
    exists (ImportExpr e1, ImportExpr e2 | e1.getName() = m.getName() and e2.getName() = m.getName() and
         e1 = original.getAName().getValue() and e2 = duplicate.getAName().getValue()
    )
    and
    exists(Module enclosing |
        original.getScope() = enclosing and
        duplicate.getEnclosingModule() = enclosing and
        (
          /* Duplicate is not at top level scope */
          duplicate.getScope() != enclosing 
          or 
          /* Original dominates duplicate */
          exists(BasicBlock b, int i1, int i2 | 
              original.getAFlowNode() = b.getNode(i1) and 
              duplicate.getAFlowNode() = b.getNode(i2) and 
              i1 < i2
          ) 
          or
          original.getAFlowNode().getBasicBlock().strictlyDominates(duplicate.getAFlowNode().getBasicBlock()) 
        )
     )
}

from Import original, Import duplicate, Module m
where double_import(original, duplicate, m)
select duplicate, "This import of module " + m.getName() + " is redundant, as it was previously imported $@.", 
  original, "on line " + original.getLocation().getStartLine().toString()
