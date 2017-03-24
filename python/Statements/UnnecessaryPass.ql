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
 * @name Unnecessary pass
 * @description Unnecessary 'pass' statement
 * @kind problem
 * @tags maintainability
 *       useless-code
 * @problem.severity warning
 * @sub-severity low
 * @precision very-high
 */

import python

predicate is_doc_string(ExprStmt s) {
  s.getValue() instanceof Unicode or s.getValue() instanceof Bytes
}

predicate has_doc_string(StmtList stmts) {
    stmts.getParent() instanceof Scope
    and
    is_doc_string(stmts.getItem(0))
}

from Pass p, StmtList list
where list.getAnItem() = p and
(
    strictcount(list.getAnItem()) = 2 and not has_doc_string(list)
    or
    strictcount(list.getAnItem()) > 2
)
select p, "Unnecessary 'pass' statement."

