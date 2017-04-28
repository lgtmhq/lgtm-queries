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

Callable viableCallable(Call c) {
  result = viableImpl(c) or
  c instanceof ConstructorCall and result = c.getCallee().getSourceDeclaration()
}

/** A viable implementation of the method called in the given method access. */
cached
Method viableImpl(MethodAccess source) {
  not result.isAbstract() and
  if source instanceof VirtualMethodAccess then
    exists(Method def, RefType t, boolean exact |
      source.getMethod() = def and
      hasQualifierType(source, t, exact)
      |
      exact = true and result = exactMethodImpl(def, t.getSourceDeclaration())
      or
      exact = false and
      exists(RefType t2 |
        result = viableMethodImpl(def, t.getSourceDeclaration(), t2) and
        not failsUnification(t, t2)
      )
    )
  else
    result = source.getMethod().getSourceDeclaration()
}

pragma[noinline]
private predicate unificationTargetLeft(ParameterizedType t1, GenericType g) {
  hasQualifierType(_, t1, _) and t1.getGenericType() = g
}

pragma[noinline]
private predicate unificationTargetRight(ParameterizedType t2, GenericType g) {
  hasViableSubtype(t2, _) and t2.getGenericType() = g
}

private predicate unificationTargets(Type t1, Type t2) {
  exists(GenericType g | unificationTargetLeft(t1, g) and unificationTargetRight(t2, g)) or
  exists(Array a1, Array a2 |
    unificationTargets(a1, a2) and
    t1 = a1.getComponentType() and
    t2 = a2.getComponentType()
  ) or
  exists(ParameterizedType pt1, ParameterizedType pt2, int pos |
    unificationTargets(pt1, pt2) and
    not pt1.getSourceDeclaration() != pt2.getSourceDeclaration() and
    t1 = pt1.getTypeArgument(pos) and
    t2 = pt2.getTypeArgument(pos)
  )
}

pragma[noinline]
private predicate typeArgsOfUnificationTargets(ParameterizedType t1, ParameterizedType t2, int pos, RefType arg1, RefType arg2) {
  unificationTargets(t1, t2) and
  arg1 = t1.getTypeArgument(pos) and
  arg2 = t2.getTypeArgument(pos)
}

private predicate failsUnification(Type t1, Type t2) {
  unificationTargets(t1, t2) and
  (
    exists(RefType arg1, RefType arg2 |
      typeArgsOfUnificationTargets(t1, t2, _, arg1, arg2) and
      failsUnification(arg1, arg2)
    ) or
    failsUnification(t1.(Array).getComponentType(), t2.(Array).getComponentType()) or
    not (
      t1 instanceof Array and t2 instanceof Array or
      t1.(PrimitiveType) = t2.(PrimitiveType) or
      t1.(Class).getSourceDeclaration() = t2.(Class).getSourceDeclaration() or
      t1.(Interface).getSourceDeclaration() = t2.(Interface).getSourceDeclaration() or
      t1 instanceof BoundedType and t2 instanceof RefType or
      t1 instanceof RefType and t2 instanceof BoundedType
    )
  )
}

private predicate hasQualifierType(VirtualMethodAccess ma, RefType t, boolean exact) {
  exists(Expr src | src = variableTrack(ma.getQualifier()) |
    // If we have a qualifier, then we track it through variable assignments
    // and take the type of the assigned value.
    exists(RefType srctype | srctype = src.getType() |
      exists(TypeVariable v | v = srctype |
        t = v.getAnUltimatelySuppliedType() or
        not exists(v.getAnUltimatelySuppliedType()) and t = ma.getMethod().getDeclaringType()
      ) or
      t = srctype and not srctype instanceof TypeVariable
    ) and
    // If we have a class instance expression, then we know the exact type.
    // This is an important improvement in precision.
    if src instanceof ClassInstanceExpr then exact = true else exact = false
  ) or
  // If the call has no qualifier then it's an implicit `this` qualifier,
  // so start from the caller's declaring type.
  not exists(ma.getQualifier()) and t = ma.getEnclosingCallable().getDeclaringType() and exact = false
}

private class SrcRefType extends RefType {
  SrcRefType() { this.isSourceDeclaration() }
}

/** The implementation of `top` present on a value of precisely type `t`. */
private Method exactMethodImpl(Method top, SrcRefType t) {
  hasSrcMethod(t, result) and
  top.getAPossibleImplementation() = result
}

/** The implementations of `top` present on viable subtypes of `t`. */
private Method viableMethodImpl(Method top, SrcRefType tsrc, RefType t) {
  exists(SrcRefType sub |
    result = exactMethodImpl(top, sub) and
    tsrc = t.getSourceDeclaration() and
    hasViableSubtype(t, sub)
  )
}

private predicate hasSrcMethod(SrcRefType t, Method impl) {
  exists(Method m |
    t.hasMethod(m, _) and impl = m.getSourceDeclaration()
  )
}

private predicate hasViableSubtype(RefType t, SrcRefType sub) {
  sub.extendsOrImplements*(t) and
  not sub instanceof Interface and
  not sub.isAbstract()
}

private Expr variableTrackStep(Expr use) {
  exists(Variable v |
    use = v.getAnAccess() and
    not v instanceof Parameter and
    result = v.getAnAssignedValue() and
    not result instanceof NullLiteral
  )
}

private Expr variableTrackPath(Expr use) {
  result = variableTrackStep*(use) and
  not exists(variableTrackStep(result))
}

private Expr variableTrack(Expr use) {
  result = variableTrackPath(use)
  or not exists(variableTrackPath(use)) and result = use
}
