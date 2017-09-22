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
 * @name Dubious NULL check
 * @description The address of a field (except the first) will never be NULL,
 *              so it is misleading, at best, to check for that case.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @tags reliability
 *       readability
 */

import default

predicate zeroComparison(EqualityOperation e) {
  exists(Expr zero | zero.getValue() = "0" |
    zero = e.getLeftOperand() or
    zero = e.getRightOperand()
  )
}

predicate inNullContext(AddressOfExpr e) {
  e.getFullyConverted().getUnderlyingType() instanceof BoolType
  or exists(ControlStructure c | c.getControllingExpr() = e)
  or exists(EqualityOperation cmp | zeroComparison(cmp) |
    e = cmp.getLeftOperand() or
    e = cmp.getRightOperand()
  )
}

FieldAccess chainedFields(FieldAccess fa) {
  result = fa or
  result = chainedFields(fa.getQualifier())
}

from AddressOfExpr addrof, FieldAccess fa, Variable v, int offset
where fa = addrof.getOperand()
  and inNullContext(addrof)
  and not addrof.isInMacroExpansion()
  and v.getAnAccess() = chainedFields(fa).getQualifier()
  and not v instanceof MemberVariable
  and offset = strictsum(chainedFields(fa).getTarget().getByteOffset())
  and offset != 0
select addrof, "This will only be NULL if " + v.getName() + " == -" + offset + "."
