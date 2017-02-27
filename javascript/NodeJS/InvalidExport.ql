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
 * @name Assignment to exports variable
 * @description Assigning to the special 'exports' variable only overwrites its value and does not export
 *              anything. Such an assignment is hence most likely unintentional.
 * @kind problem
 * @problem.severity error
 * @tags maintainability
 *       frameworks/node.js
 * @precision high
 */

import javascript

from Assignment assgn, NodeModule m, Variable exports
where exports = m.getScope().getVariable("exports") and
      assgn.getLhs() = exports.getAnAccess() and
      // exclude common pattern `exports = module.exports = ...;`
      // or, equivalently, `module.exports = exports = ...;`
      not exists (Assignment meAssgn | meAssgn.getTarget() = m.getAnExportsAccess() |
        (meAssgn = assgn.getRhs().stripParens() or assgn = meAssgn.getRhs().stripParens()) and
        // however, if there are no further uses of `exports` the assignment is useless anyway
        strictcount (exports.getAnAccess()) > 1
      )
select assgn, "Assigning to 'exports' does not export anything."