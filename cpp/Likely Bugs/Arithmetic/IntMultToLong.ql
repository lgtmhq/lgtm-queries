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
 * @name Multiplication result converted to larger type
 * @description A multiplication result that is converted to a larger type can
 *              be a sign that the result can overflow the type converted from.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/integer-multiplication-cast-to-long
 * @tags reliability
 *       security
 *       correctness
 *       types
 *       external/cwe/cwe-190
 *       external/cwe/cwe-192
 *       external/cwe/cwe-197
 *       external/cwe/cwe-681
 */
import default

from MulExpr me, Type t1, Type t2
where t1 = me.getType().getUnderlyingType() and
      t2 = me.getConversion().getType().getUnderlyingType() and
      t1.getSize() < t2.getSize() and
      (
        (
          t1.getUnspecifiedType() instanceof IntegralType and
          t2.getUnspecifiedType() instanceof IntegralType
        ) or (
          t1.getUnspecifiedType() instanceof FloatingPointType and
          t2.getUnspecifiedType() instanceof FloatingPointType
        )
      ) and
      not me.getLeftOperand().isConstant() and
      not me.getRightOperand().isConstant() and
      me.getConversion().isCompilerGenerated()
select me, "Cast to '" + me.getFullyConverted().getType().toString() + "' before multiplication to avoid potential overflow."

