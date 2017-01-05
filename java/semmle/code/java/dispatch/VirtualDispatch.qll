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

import java

/**
 * A conservative analysis that returns a single method - if we can establish
 * one - that will be the target of the virtual dispatch.
 */
Method exactVirtualMethod(MethodAccess c) {
  // If there are multiple potential implementations, return nothing.
  implCount(c, 1) and
  result = viableImpl(c)
}

/**
 * A conservative analysis that returns a single callable - if we can establish
 * one - that will be the target of the call.
 */
Callable exactCallable(Call c) {
  result = exactVirtualMethod(c)
  or
  c instanceof ConstructorCall and result = c.getCallee()
}

private predicate implCount(MethodAccess m, int c) {
  strictcount(viableImpl(m)) = c
}

/** A viable implementation of the method called in the given method access. */
Method viableImpl(MethodAccess source) {
  not result.isAbstract() and
  exists(Method def | source.getMethod() = def |
    // If we have a qualifier, then we track it through one local variable assignment
    // and take the type of the assigned value.
    exists(Expr src | src = variableTrack(source.getQualifier()) | 
      // If we have a class instance expression or a `super` expr, then we know the exact type.
      // This is an important improvement in precision.
      exists(Type t | 
        t = src.(ClassInstanceExpr).getConstructedType() or t = src.(SuperAccess).getType() | 
        result = exactMethodImpl(def, t)
      )
      or
      // If not, we have to consider subtypes.
      not (src instanceof ClassInstanceExpr or src instanceof SuperAccess) 
      and result = viableMethodImpl(def, src.getType())
    )
    or
    // If the call has no qualifier then it's an implicit `this` qualifier,
    // so start from the callee's declaring type.
    not source.hasQualifier() and result = viableMethodImpl(def, def.getDeclaringType())
  )
}

/** The implementation of `top` present on a value of precisely type `t`. */
private Method exactMethodImpl(Method top, RefType t) {
  t.hasMethod(result, _) and
  top.getAPossibleImplementation() = result
}

/** The implementations of `top` present on viable subtypes of `t`. */
cached private Method viableMethodImpl(Method top, RefType t) {
  // This is a performance-critical method - exercise caution when editing it.
  exists(RefType sub | 
    result.getDeclaringType() = sub
    and top.getAPossibleImplementation() = result 
    and hasSubtypeStar(t, sub) 
    and viable(sub)
  )
}

private predicate viable(Type t) {
  // For now, we consider everything to be viable.
  any()
}

private Expr variableTrack(Expr use) {
  exists(LocalVariableDecl v |
    use = v.getAnAccess() and
    result = v.getAnAssignedValue()
  )
  or not exists(LocalVariableDecl v | use = v.getAnAccess()) and result = use
}
