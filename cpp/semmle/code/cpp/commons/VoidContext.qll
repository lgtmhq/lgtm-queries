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

import semmle.code.cpp.exprs.Expr

/**
 * An expression that is used to qualify some other expression.
 */
class Qualifier extends Expr {
  Qualifier() {
       exists(VariableAccess a | a.getQualifier() = this)
    or exists(Call c | c.getQualifier() = this)
    or exists(VacuousDestructorCall v | v.getQualifier() = this)
  }
}

/**
 * An expression that occurs in a void context, i.e. either as the toplevel expression of
 * an expression statement or on the left hand side of the comma operator.
 *
 * Expressions that are explicitly cast to void are not considered to be in void context.
 */
class ExprInVoidContext extends Expr {
  ExprInVoidContext() {
    exprInVoidContext(this)
  }
}

private predicate exprInVoidContext(Expr e) {
    (   exists(ExprStmt s |
               s = e.getParent()
               and not exists(StmtExpr se |
                              s = se.getStmt().(Block).getLastStmt()))
     or exists(ConditionalExpr c | c.getThen() = e and c instanceof ExprInVoidContext)
     or exists(ConditionalExpr c | c.getElse() = e and c instanceof ExprInVoidContext)
     or exists(CommaExpr c | c.getLeftOperand() = e)
     or exists(CommaExpr c | c.getRightOperand() = e and c instanceof ExprInVoidContext)) and
    not e instanceof Qualifier and
    not e.getActualType() instanceof VoidType
}

