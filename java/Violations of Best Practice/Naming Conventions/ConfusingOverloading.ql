// Copyright 2016 Semmle Ltd.
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
 * @name Confusing overloading of methods
 * @description Overloaded methods that have the same number of parameters, where each pair of 
 *              corresponding parameter types is convertible by casting or autoboxing, may be 
 *              confusing.
 * @kind problem
 * @problem.severity recommendation
 */
import default

private
predicate confusingPrimitiveBoxedTypes(Type t, Type u) {
    t instanceof PrimitiveType and
    u instanceof BoxedType and
    t.(PrimitiveType).getBoxedType() = u
  or
    t instanceof BoxedType and
    u instanceof PrimitiveType and
    u.(PrimitiveType).getBoxedType() = t
}

private
predicate overloadedMethods(Method n, Method m) {
  n.fromSource()
  and exists(RefType rt, string name, int numParams | 
    candidateMethod(rt, m, name, numParams) and
    candidateMethod(rt, n, name, numParams)
  )
  and n != m
  and n.getSourceDeclaration().getSignature() < m.getSourceDeclaration().getSignature()
}

private
predicate overloadedMethodsMostSpecific(Method n, Method m) {
  overloadedMethods(n, m)
  and not exists(Method nSup, Method mSup | n.overrides*(nSup) and m.overrides*(mSup) |
  	overloadedMethods(nSup, mSup) and
  	(n != nSup or m != mSup)
  )
}

/**
 * A whitelist of names that are commonly overloaded in odd ways and should
 * not be reported by this query.
 */
private predicate whitelist(string name) {
	name = "visit"
}

/**
 * Method `m` has name `name`, number of parameters `numParams`
 * and is declared in `t` or inherited from a supertype of `t`.
 */
private 
predicate candidateMethod(RefType t, Method m, string name, int numParam) {
  t.inherits(m) and
  m.getName() = name and 
  m.getNumberOfParameters() = numParam and
  m = m.getSourceDeclaration() and
  not whitelist(name)
}

private
predicate potentiallyConfusingTypes(Type a, Type b) {
  exists(RefType commonSubtype | hasSubtypeStar(a, commonSubtype) |
    hasSubtypeStar(b, commonSubtype)
  ) or
  confusingPrimitiveBoxedTypes(a, b)
}

private
predicate confusinglyOverloaded(Method m, Method n) {
  overloadedMethodsMostSpecific(n, m) and
  forall(int i, Parameter p, Parameter q | p = n.getParameter(i) and q = m.getParameter(i) |
    potentiallyConfusingTypes(p.getType(), q.getType())
  )
}

from Method m, Method n, string messageQualifier
where confusinglyOverloaded(m, n)
  and (if m.getDeclaringType() = n.getDeclaringType()
       then messageQualifier = ""
       else messageQualifier = m.getDeclaringType().getName() + ".")
select n, "Method " + n.getDeclaringType() + "." + n +
       "(..) could be confused with overloaded method $@, since dispatch depends on static types.",
       m.getSourceDeclaration(), messageQualifier + m.getName()
       
