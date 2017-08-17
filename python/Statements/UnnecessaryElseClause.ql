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
 * @name Unnecessary 'else' clause in loop
 * @description An 'else' clause in a 'for' or 'while' statement that does not contain a 'break' is redundant.
 * @kind problem
 * @tags maintainability
 *       useless-code
 * @problem.severity warning
 * @sub-severity low
 * @precision very-high
 * @id py/redundant-else
 */

import python

from Stmt loop, StmtList body, StmtList clause, string kind
where
(exists(For f | f = loop | clause = f.getOrelse() and body = f.getBody() and kind = "for")
 or
 exists(While w | w = loop | clause = w.getOrelse() and body = w.getBody() and kind = "while")
)
and not exists(Break b | body.contains(b))
select loop, "This '" + kind + "' statement has a redundant 'else' as no 'break' is present in the body."
