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
 * @name Result of integer multiplication cast to long
 * @description Casting the result of an integer multiplication to type 'long' instead of casting
 *              before the multiplication may cause overflow.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id java/integer-multiplication-cast-to-long
 * @tags reliability
 *       security
 *       correctness
 *       types
 *       external/cwe/cwe-190
 *       external/cwe/cwe-192
 *       external/cwe/cwe-197
 *       external/cwe/cwe-681
 */
import java
import semmle.code.java.dataflow.RangeUtils

/** Either the boxed type `java.lang.Long` or the primitive type `long`. */
class Long extends Type {
  Long() {
    this.(Class).hasQualifiedName("java.lang","Long") or
    this.hasName("long")
  }
}

/** A declaration of a local variable whose initializer is a `MulExpr`. */
class LocalVariableWithMulExprInit extends LocalVariableDeclStmt {
  MulExpr getInit() {
    result = this.getAVariable().getInit()
  }
  Type getType() {
    result = this.getAVariable().getType()
  }
}

/** A return statement returning a `MulExpr`. */
class ReturnMulExpr extends ReturnStmt {
  MulExpr getInit() {
    result = this.getResult()
  }
  Type getType() {
    result = this.getEnclosingCallable().getReturnType()
  }
}

/** An assignment whose right hand side is a `MulExpr`. */
class AssignMulExprStmt extends ExprStmt {
  MulExpr getInit() {
    result = this.getExpr().(AssignExpr).getSource()
  }
  Type getType() {
    result = this.getExpr().(AssignExpr).getType()
  }
}

/** An integer multiplication that does not overflow. */
predicate small(MulExpr e) {
  exists(float lhs, float rhs, float res |
    lhs = e.getLeftOperand().getProperExpr().(ConstantIntegerExpr).getIntValue() and
    rhs = e.getRightOperand().getProperExpr().(ConstantIntegerExpr).getIntValue() and
    lhs * rhs = res and
    -2147483648.0 <= res and res <= 2147483647.0
  )
}

from Stmt s, MulExpr e
where s.getEnclosingCallable().fromSource() and
      not exists(Long l | e.getAnOperand().getType() = l) and
      (
        exists(LocalVariableWithMulExprInit p | s = p and
          p.getType() instanceof Long and
          p.getInit() = e
        ) or
        exists(ReturnMulExpr p | s = p and
          p.getType() instanceof Long and
          p.getInit() = e
        ) or
        exists(AssignMulExprStmt p | s = p and
          p.getType() instanceof Long and
          p.getInit() = e
        )
      ) and
      not small(e)
select s, "Result of integer multiplication cast to long."
