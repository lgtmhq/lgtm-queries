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
 * @name Missing return statement
 * @description All functions that are not void should return a value on every exit path.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @id cpp/missing-return
 * @tags reliability
 *       readability
 *       language-features
 */
import default

/* This is slightly subtle: The extractor adds a dummy 'return;' statement for control paths
   that fall off the end of a function. So we can simply look for non-void functions containing
   a non-value carrying return. If the predecessor is a return statement it means that
   the return did not return a value. (If that return was not added by the extractor but by the
   programmer, we can flag it anyway, since this is arguably a bug.) */

predicate functionsMissingReturnStmt(Function f, ControlFlowNode blame) {
                        f.fromSource() and
      not f.getType().getUnderlyingType().getUnspecifiedType() instanceof VoidType and
      exists(ReturnStmt s | f.getAPredecessor() = s | blame = s.getAPredecessor())}

/* If a function has a value-carrying return statement, but the extractor hit a snag
   whilst parsing the value, then the control flow graph will not include the value.
   As such, to avoid embarrassing false positives, we exclude any function which
   wasn't perfectly extracted. */
predicate functionImperfectlyExtracted(Function f) {
  exists(CompilerError e | f.getBlock().getLocation().subsumes(e.getLocation()))
}

from Stmt stmt, string msg
where
  exists(Function f, ControlFlowNode blame |
    functionsMissingReturnStmt(f, blame) and
    reachable(blame) and
    not functionImperfectlyExtracted(f) and
    (blame = stmt or blame.(Expr).getEnclosingStmt() = stmt) and
    msg = "Function " + f.getName() + " should return a value of type " + f.getType().getName() + " but does not return a value here"
  )
select stmt, msg
