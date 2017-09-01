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
 * @name Uncontrolled data in arithmetic expression
 * @description Arithmetic operations on uncontrolled data that is not validated can cause
 *              overflows.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/uncontrolled-arithmetic
 * @tags security
 *       external/cwe/cwe-190
 *       external/cwe/cwe-191
 */
import java
import semmle.code.java.security.DataFlow
import semmle.code.java.security.SecurityTests
import ArithmeticCommon

class TaintSource extends FlowSource {
  TaintSource() {
    // Either this is an access to a random number generating method of the right kind, ...
    exists(Method def |
      def = this.(MethodAccess).getMethod()
      and 
      (
        // Some random-number methods are omitted:
        // `nextDouble` and `nextFloat` are between 0 and 1,
        // `nextGaussian` is extremely unlikely to hit max values.
        def.getName() = "nextInt" or
        def.getName() = "nextLong"
      )
      and def.getNumberOfParameters() = 0
      and def.getDeclaringType().hasQualifiedName("java.util", "Random")
    )
    
    // ... or this is the array parameter of `nextBytes`, which is filled with random bytes.
    or exists(MethodAccess m, Method def | 
      m.getAnArgument() = this 
      and m.getMethod() = def
      and def.getName() = "nextBytes" 
      and def.getNumberOfParameters() = 1
      and def.getDeclaringType().hasQualifiedName("java.util", "Random")
    )
  }
}

from ArithExpr exp, VarAccess tainted, TaintSource origin, string effect
where
  exp.getAnOperand() = tainted and
  origin.flowsTo(tainted) and
  (
    (not guardedAgainstUnderflow(exp, tainted) and effect = "underflow") or 
    (not guardedAgainstOverflow(exp, tainted) and effect = "overflow")
  )
  // Exclude widening conversions of tainted values due to binary numeric promotion (JLS 5.6.2)
  // unless there is an enclosing cast down to a narrower type.
  and narrowerThanOrEqualTo(exp, tainted.getType())
  and not exp.getEnclosingCallable() instanceof HashCodeMethod
  and not exp.getEnclosingCallable().getDeclaringType() instanceof NonSecurityTestClass
select exp, "$@ flows to here and is used in arithmetic, potentially causing an " + effect + ".", 
  origin, "Uncontrolled value"
