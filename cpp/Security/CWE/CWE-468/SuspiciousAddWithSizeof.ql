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
 * @name Suspicious add with sizeof
 * @description Explicitly scaled pointer arithmetic expressions
 *              can cause buffer overflow conditions if the offset is also
 *              implicitly scaled.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags security
 *       external/cwe/cwe-468
 */
import cpp
import IncorrectPointerScalingCommon

private predicate isCharPtrExpr(Expr e) {
  exists (PointerType pt
  | pt = e.getFullyConverted().getUnderlyingType()
  | pt.getBaseType().getUnspecifiedType() instanceof CharType)
}

from Expr sizeofExpr, Expr e
where
  // If we see an addWithSizeof then we expect the type of
  // the pointer expression to be char*. Otherwise it is probably
  // a mistake.
  addWithSizeof(e, sizeofExpr, _) and not isCharPtrExpr(e)
select
  sizeofExpr,
  "Suspicious sizeof offset in a pointer arithmetic expression. " +
  "The type of the pointer is " +
  e.getFullyConverted().getType().toString() + "."
