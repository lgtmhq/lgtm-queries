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
 * @name Loop with unreachable exit condition
 * @description An iteration or loop with an exit condition that cannot be
 *              reached is an indication of faulty logic and can likely lead to infinite
 *              looping.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags security
 *       external/cwe/cwe-835
 */

import java
import Likely_Bugs.Comparison.UselessComparisonTest

/**
 * The condition `cond` is a loop condition for `loop` - potentially indirectly
 * by guarding a `break` or a `return` that can exit the loop.
 */
predicate loopCondition(LoopStmt loop, Expr cond, boolean polarity) {
  polarity = true and cond = loop.getCondition() or
  exists (IfStmt ifstmt, Stmt exit |
    ifstmt.getParent*() = loop.getBody() and
    ifstmt.getCondition() = cond and
    (  exit.(BreakStmt).(JumpStmt).getTarget() = loop or
      exit.(ReturnStmt).getParent*() = loop.getBody()
    ) and
    (  polarity = false and exit.getParent*() = ifstmt.getThen() or
      polarity = true and exit.getParent*() = ifstmt.getElse()
    )
  )
}

/**
 * The expression `subcond` is a (reflexive, transitive) sub-expression of
 * `cond` passing through only logical connectives. The boolean `negated`
 * indicates whether an odd number of negations separates `cond` and `subcond`.
 */
predicate subCondition(Expr cond, Expr subcond, boolean negated) {
  cond = subcond and negated = false or
  subCondition(cond.(AndLogicalExpr).getAnOperand(), subcond, negated) or
  subCondition(cond.(OrLogicalExpr).getAnOperand(), subcond, negated) or
  subCondition(cond.(ParExpr).getExpr(), subcond, negated) or
  subCondition(cond.(LogNotExpr).getExpr(), subcond, negated.booleanNot())
}

from LoopStmt loop, BinaryExpr test, boolean testIsTrue, Expr cond, boolean polarity, boolean negated
where
  loopCondition(loop, cond, polarity) and
  not loop instanceof EnhancedForStmt and
  subCondition(cond, test, negated) and
  uselessTest(_, test, testIsTrue) and
  testIsTrue = polarity.booleanXor(negated)
select
  loop, "Loop might not terminate, as termination depends in part on $@ being "
        + testIsTrue.booleanNot() + " but it is always " + testIsTrue + ".", test, "this test"
