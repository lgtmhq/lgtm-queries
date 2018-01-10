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
 * @name Assignment to exports variable
 * @description Assigning to the special 'exports' variable only overwrites its value and does not export
 *              anything. Such an assignment is hence most likely unintentional.
 * @kind problem
 * @problem.severity warning
 * @id js/node/assignment-to-exports-variable
 * @tags maintainability
 *       frameworks/node.js
 *       external/cwe/cwe-563
 * @precision very-high
 */

import javascript

from Assignment assgn, NodeModule m, Variable exportsVar, DataFlowNode exportsVal
where exportsVar = m.getScope().getVariable("exports") and
      // `assgn` assigns `exportsVal` to `exports`
      assgn.getLhs() = exportsVar.getAnAccess() and
      assgn.getRhs().(DataFlowNode).getALocalSource() = exportsVal and
      // this is OK if `exportsVal` flows into `module.exports`
      not exists (PropWriteNode pw |
        pw.getBase() instanceof ModuleAccess and
        pw.getPropertyName() = "exports" and
        pw.getRhs().getALocalSource() = exportsVal and
        // however, if there are no further uses of `exports` the assignment is useless anyway
        strictcount (exportsVar.getAnAccess()) > 1
      )
select assgn, "Assigning to 'exports' does not export anything."