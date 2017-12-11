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
 * @name Reference equality test on strings
 * @description Comparing two strings using the == or != operator
 *              compares object identity, which may not be intended.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/reference-equality-on-strings
 * @tags reliability
 *       external/cwe/cwe-597
 */
import java

/** An expression of type `java.lang.String`. */
class StringValue extends Expr {
  StringValue() {
    this.getType() instanceof TypeString
  }

  predicate isInterned() {
    // A call to `String.intern()`.
    exists(Method intern |
      intern.getDeclaringType() instanceof TypeString and
      intern.hasName("intern") and
      this.(MethodAccess).getMethod() = intern
    )
    // Parenthesized expressions.
    or this.(ParExpr).getExpr().(StringValue).isInterned()
    // Ternary conditional operator.
    or (this.(ConditionalExpr).getTrueExpr().(StringValue).isInterned()
        and this.(ConditionalExpr).getFalseExpr().(StringValue).isInterned())
    // Values of type `String` that are compile-time constant expressions (JLS 15.28).
    or this instanceof CompileTimeConstantExpr
    // Variables that are only ever assigned an interned `StringValue`.
    or variableValuesInterned(this.(VarAccess).getVariable())
    // Method accesses whose results are all interned.
    or forex(ReturnStmt rs | rs.getEnclosingCallable() = this.(MethodAccess).getMethod() |
      rs.getResult().(StringValue).isInterned()
    )
  }
}

predicate variableValuesInterned(Variable v) {
  v.fromSource() and
  // All assignments to variables are interned.
  forall(StringValue sv | sv = v.getAnAssignedValue() | sv.isInterned())
  // For parameters, assume they could be non-interned.
  and not v instanceof Parameter
  // If the string is modified with `+=`, then the new string is not interned
  // even if the components are.
  and not exists(AssignOp append | append.getDest().getProperExpr() = v.getAnAccess())
}

from EqualityTest e, StringValue lhs, StringValue rhs
where e.getLeftOperand() = lhs
      and e.getRightOperand() = rhs
      and not (lhs.isInterned() and rhs.isInterned())
select e, "String values compared with " + e.getOp() + "."
