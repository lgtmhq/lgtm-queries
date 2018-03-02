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
 * @name Non-zero value cast to pointer
 * @description A constant value other than zero is converted to a pointer type. This is a dangerous practice, since the meaning of the numerical value of pointers is platform dependent.
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id cpp/cast-to-pointer
 * @tags reliability
 *       correctness
 *       types
 */
import cpp

predicate commonErrorCode(string value) {
  value = "0" or value = "1" or value = "-1"
  or value = "18446744073709551615" // 2^64-1, i.e. -1 as an unsigned int64
  or value = "4294967295" // 2^32-1, i.e. -1 as an unsigned int32
  or value = "3735928559" // 0xdeadbeef
  or value = "3735929054" // 0xdeadc0de
  or value = "3405691582" // 0xcafebabe
}

from Expr e
where e.isConstant() and
      not commonErrorCode(e.getValue()) and
      e.getFullyConverted().getType() instanceof PointerType and
      not e.getType() instanceof ArrayType and
      not e.getType() instanceof PointerType and
      not e.isInMacroExpansion()
select e, "Nonzero value " + e.getValueText() + " cast to pointer."
