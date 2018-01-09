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
 * @name Use of a print statement at module level
 * @description Using a print statement at module scope (except when guarded by if __name__ == '__main__') will cause surprising output when the module is imported.
 * @kind problem
 * @tags reliability
 *       maintainability
 *       convention
 * @problem.severity recommendation
 * @sub-severity high
 * @precision high
 * @id py/print-during-import
 */

import python


predicate main_eq_name(If i) {
    exists(Name n, StrConst m, Compare c |
        i.getTest() = c and c.getLeft() = n and
        c.getAComparator() = m and
        n.getId() = "__name__" and
        m.getText() = "__main__"
    )
}

predicate is_print_stmt(Stmt s) {
    s instanceof Print or
    exists(ExprStmt e, Call c, Name n | e = s and c = e.getValue() and n = c.getFunc() and n.getId() = "print")
}

from Stmt p
where is_print_stmt(p) and
exists(ModuleObject m | m.getModule() = p.getScope() and m.getKind() = "module") and
not exists(If i | main_eq_name(i) and i.getASubStatement().getASubStatement*() = p)
select p, "Print statement may execute during import."
