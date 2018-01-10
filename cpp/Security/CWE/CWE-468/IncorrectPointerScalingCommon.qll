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

/**
 * Shared utilities for the CWE-468 queries.
 */
import cpp

/**
 * Gets the type parameter of `sizeof` expression `e`.
 */
private
Type sizeofParam(Expr e) {
  result = e.(SizeofExprOperator).getExprOperand().getFullyConverted().getType()
  or
  result = e.(SizeofTypeOperator).getTypeOperand()
}

/**
 * Holds if `e` is `sizeof` expression `sizeofExpr`, possibly multiplied
 * by another expression, and `sizeofParam` is `sizeofExpr`'s type
 * parameter.
 *
 * For example, if `e` is `4 * sizeof(T)` then `sizeofExpr` is
 * `sizeof(T)` and `sizeofParam` is `T`.
 */
private
predicate multiplyWithSizeof(Expr e, Expr sizeofExpr, Type sizeofParam) {
  (e = sizeofExpr and sizeofParam = sizeofParam(e).getUnspecifiedType())
  or
  multiplyWithSizeof(e.(MulExpr).getAnOperand(), sizeofExpr, sizeofParam)
}

/**
 * Holds if the pointer `e` is added to the `sizeof` expression
 * `sizeofExpr` (which may first be multiplied by another expression),
 * and `sizeofParam` is `sizeofExpr`'s type parameter.

 * For example, if the program contains the expression
 * `p - (i * sizeof(T))` then `e` would be `p`, `sizeofExpr` would be
 * `sizeof(T)`, and `sizeofParam` would be `T`.
 */
predicate addWithSizeof(Expr e, Expr sizeofExpr, Type sizeofParam) {
  exists (PointerAddExpr addExpr
  | e = addExpr.getLeftOperand() and
    multiplyWithSizeof(addExpr.getRightOperand(), sizeofExpr, sizeofParam))
  or
  exists (PointerSubExpr subExpr
  | e = subExpr.getLeftOperand() and
    multiplyWithSizeof(subExpr.getRightOperand(), sizeofExpr, sizeofParam))
}
