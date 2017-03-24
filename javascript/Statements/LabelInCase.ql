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
 * @name Non-case label in switch statement
 * @description A non-case label appearing in a switch statement that is textually aligned with a case
 *              label is confusing to read, or may even indicate a bug.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       readability
 * @precision very-high
 */

import javascript

from LabeledStmt l, Case c
where l = c.getAChildStmt+() and
      l.getLocation().getStartColumn() = c.getLocation().getStartColumn()
select l.getChildExpr(0), "Non-case labels in switch statements are confusing."