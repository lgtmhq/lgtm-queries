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
 * @name Potentially unsafe use of strcat
 * @description Using 'strcat' without checking the size of the source string
 *              may result in a buffer overflow
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/unsafe-strcat
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-676
 *       external/cwe/cwe-120
 *       external/cwe/cwe-251
 */
import default
import Buffer

/**
 * An access to a variable that is initialized by a constant
 * expression, and is never used as an lvalue anywhere else.
 */
predicate isEffectivelyConstAccess(VariableAccess a)
{
  exists(Variable v |
    a.getTarget() = v and
    v.getInitializer().getExpr().isConstant() and
    not v.getAnAccess().isUsedAsLValue()
  )
}

from FunctionCall fc, VariableAccess src
where fc.getTarget().hasName("strcat") and
      src = fc.getArgument(1) and
      not src.getType() instanceof ArrayType and
      not exists(BufferSizeExpr bse |
        bse.getArg().(VariableAccess).getTarget() = src.getTarget()) and
      not isEffectivelyConstAccess(src)
select fc, "Always check the size of the source buffer when using strcat."
