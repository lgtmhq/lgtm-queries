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
 * @name No trivial switch statements
 * @description Using a switch statement when there are fewer than two non-default cases leads to unclear code.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/trivial-switch
 * @tags maintainability
 *       readability
 */
import cpp

from SwitchStmt s
where s.fromSource() and
      count(SwitchCase sc | sc.getSwitchStmt() = s and not sc instanceof DefaultCase) < 2 and
      not exists(s.getGeneratingMacro())
select s, "This switch statement should either handle more cases, or be rewritten as an if statement."
