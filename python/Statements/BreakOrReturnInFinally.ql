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
 * @name 'break' or 'return' statement in finally
 * @description Using a Break or Return statement in a finally block causes the
 *              Try-finally block to exit, discarding the exception.
 * @kind problem
 * @tags reliability
 *       maintainability
 *       external/cwe/cwe-584
 * @problem.severity warning
 * @sub-severity low
 * @precision medium
 * @id py/exit-from-finally
 */

import python

from Stmt s, string kind
where 
s instanceof Return and kind = "return" and exists(Try t | t.getFinalbody().contains(s))
or
s instanceof Break and kind = "break" and
exists(Try t | t.getFinalbody().contains(s) |
    not exists(For loop | loop.contains(s) and t.getFinalbody().contains(loop))
    and
    not exists(While loop | loop.contains(s) and t.getFinalbody().contains(loop))
)
select s, "'" + kind + "' in a finally block will swallow any exceptions raised."
