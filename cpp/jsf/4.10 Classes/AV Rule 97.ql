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
 * @name No raw arrays in interfaces
 * @description Arrays should not be used in interfaces. Arrays degenerate to pointers when passed as parameters. This array decay problem has long been known to be a source of errors. Consider using std::vector or encapsulating the array in an Array class.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/array-in-interface
 * @tags reliability
 *       readability
 *       language-features
 */
import default

predicate containsArray(Type t) {
  t instanceof ArrayType
  or containsArray(t.(PointerType).getBaseType())
  or containsArray(t.(SpecifiedType).getBaseType())
  or (containsArray(t.getUnderlyingType()) and not exists(TypedefType allowed | allowed = t |
    allowed.hasGlobalName("jmp_buf") or
    allowed.hasGlobalName("va_list")
  ))
}

predicate functionAPIViolation(MemberFunction f) {
  f.isPublic() and
  containsArray(f.getAParameter().getType())
}

from MemberFunction m
where functionAPIViolation(m)
  and not m.getDeclaringType() instanceof Struct
select m, "Raw arrays should not be used in interfaces. A container class should be used instead."
