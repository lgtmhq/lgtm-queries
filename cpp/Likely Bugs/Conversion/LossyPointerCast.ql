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
 * @name Lossy pointer cast
 * @description A pointer type is converted to a smaller integer type. This may lead to loss of information in the variable and is highly non-portable.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags reliability
 *       correctness
 *       types
 */
import default

predicate lossyPointerCast(Expr e, PointerType pt, IntegralType it) {
  not it instanceof BoolType and
  e.getConversion().getType().getUnderlyingType() = it and
  e.getType().getUnderlyingType() = pt and
  it.getSize() < pt.getSize() and
  not e.isInMacroExpansion()
}

from Expr e, PointerType pt, IntegralType it
where lossyPointerCast(e, pt, it)
select e, "Converted from " + pt.getName() + " to smaller type "+it.getName()
