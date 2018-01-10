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
 * @description Checking whether a variable is null when that variable cannot
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
import semmle.code.java.dataflow.SSA
private import semmle.code.java.dataflow.Nullness

from Expr guard, SsaVariable ssa, Variable v
where
  guard = superfluousNullGuard(ssa) and
  v = ssa.getSourceVariable().getVariable()
select guard, "This check is useless, since $@ cannot be null here", v, v.getName()
