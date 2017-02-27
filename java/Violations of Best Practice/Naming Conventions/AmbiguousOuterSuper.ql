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
 * @name Subtle call to inherited method
 * @description An unqualified call to a method that exists with the same signature in both a
 *              superclass and an outer class is ambiguous.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       readability
 */
import java

RefType nestedSupertypePlus(RefType t) {
  t.getASourceSupertype() = result and
  t instanceof NestedType or
  exists(RefType mid | mid = nestedSupertypePlus(t) |
    mid.getASourceSupertype() = result
  )
}

/**
 * A call (without a qualifier) in a nested type
 * to an inherited method with the specified `signature`.
 */
predicate callToInheritedMethod(RefType lexicalScope, MethodAccess ma, string signature) {
  not ma.getMethod().isStatic() and  
  not ma.hasQualifier() and
  ma.getEnclosingCallable().getDeclaringType() = lexicalScope and
  nestedSupertypePlus(lexicalScope).getAMethod() = ma.getMethod() and
  signature = ma.getMethod().getSignature()
}

/**
 * Return accessible methods in an outer class of `nested`.
 *
 * Accessible means that if a method is virtual then none of the nested
 * classes "on-route" can be static.
 */
Method methodInEnclosingType(NestedType nested, string signature) {
  (result.isStatic() or not nested.isStatic())
  and
  result.getSignature() = signature
  and
  exists(RefType outer | outer = nested.getEnclosingType() |
    result = outer.getAMethod() or
    result = methodInEnclosingType(nested, signature)
  )
}

from MethodAccess ma, Method m, NestedType nt, string signature
where callToInheritedMethod(nt, ma, signature) and
      m = methodInEnclosingType(nt, signature) and
      // There is actually scope for confusion.
      not nt.getASourceSupertype+() = m.getDeclaringType()
select ma, "A $@ is called instead of a $@.",
  ma.getMethod(),  "method declared in a superclass",
  m, "method with the same signature in an enclosing class"
