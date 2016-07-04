// Copyright 2016 Semmle Ltd.
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
 * @name Spin on field
 * @description Repeatedly reading a non-volatile field within the condition of an empty loop may
 *              result in an infinite loop.
 * @kind problem
 * @problem.severity warning
 */
import default

/** A numerical comparison or an equality test. */
class ComparisonOrEqTestExpr extends Expr {
  ComparisonOrEqTestExpr() {
    this instanceof ComparisonExpr or
    this instanceof EqualityTest
  }
}

/** An empty statement or block. */
class Empty extends Stmt {
  Empty() {
    this instanceof EmptyStmt or
    this.(Block).getNumStmt() = 0
  }
}

/** An empty loop statement. */
class EmptyLoop extends Stmt {
  EmptyLoop() {
    exists(ForStmt stmt | stmt = this |
      count(stmt.getAnInit()) = 0 and 
      count(stmt.getAnUpdate()) = 0 and 
      stmt.getStmt() instanceof Empty
    ) or
    this.(WhileStmt).getStmt() instanceof Empty or
    this.(DoStmt).getStmt() instanceof Empty
  }

  Expr getCondition() {
    result = this.(ForStmt).getCondition() or
    result = this.(WhileStmt).getCondition() or
    result = this.(DoStmt).getCondition()
  }
}

/** An access to a field in this object. */
class FieldAccessInThis extends VarAccess {
  FieldAccessInThis() {
    this.getVariable() instanceof Field and 
    (not this.hasQualifier() or this.getQualifier() instanceof ThisAccess)
  }
}

from EmptyLoop loop, FieldAccessInThis access, Field field, ComparisonOrEqTestExpr expr
where loop.getCondition() = expr and
      access.getParent() = expr and
      field = access.getVariable() and
      field.isStatic() and
      not field.isVolatile() and
      field.getType() instanceof RefType
select access, "Spinning on " + field.getName() + " in " 
                              + loop.getEnclosingCallable().getName() + "."
