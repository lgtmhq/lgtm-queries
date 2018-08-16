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
 * @name Useless null check
 * @description Checking whether an expression is null when that expression cannot
 *              possibly be null is useless.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id java/useless-null-check
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-561
 */

import java
import semmle.code.java.dataflow.NullGuards
import semmle.code.java.controlflow.Guards

from Expr guard, Expr e, Expr reason, string msg
where
  guard = basicNullGuard(e, _, true) and
  e = clearlyNotNullExpr(reason) and
  (if reason instanceof Guard then
    msg = "This check is useless, $@ cannot be null here, since it is guarded by $@."
  else if reason != e then
    msg = "This check is useless, $@ cannot be null here, since $@ always is non-null."
  else
    msg = "This check is useless, since $@ always is non-null.")
select guard, msg, e, e.toString(), reason, reason.toString()
