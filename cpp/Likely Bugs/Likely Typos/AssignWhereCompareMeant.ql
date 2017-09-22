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
 * @name Assignment where comparison was intended
 * @description The '=' operator may have been used accidentally, where '=='
 *              was intended.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-481
 */
import default

abstract class BooleanControllingAssignment extends AssignExpr {
  abstract predicate isWhitelisted();
}

class BooleanControllingAssignmentInExpr extends BooleanControllingAssignment {
  BooleanControllingAssignmentInExpr() {
       this.getParent() instanceof UnaryLogicalOperation
    or this.getParent() instanceof BinaryLogicalOperation
    or exists(ConditionalExpr c | c.getCondition() = this)
  }

  predicate isWhitelisted() {
    this.getConversion().(ParenthesisExpr).isParenthesised()
  }
}

class BooleanControllingAssignmentInStmt extends BooleanControllingAssignment {
  BooleanControllingAssignmentInStmt() {
       exists(IfStmt i | i.getCondition() = this)
    or exists(ForStmt f | f.getCondition() = this)
    or exists(WhileStmt w | w.getCondition() = this)
    or exists(DoStmt d | d.getCondition() = this)
  }

  predicate isWhitelisted() {
    this.isParenthesised()
  }
}

from BooleanControllingAssignment ae
where ae.getRValue().isConstant() and not ae.isWhitelisted()
select ae, "Use of '=' where '==' may have been intended."
