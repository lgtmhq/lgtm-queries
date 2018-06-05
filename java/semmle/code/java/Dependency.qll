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
 * Provides utility predicates for representing dependencies between types.
 */

import Type
import Generics
import Expr

/**
 * Holds if type `t` depends on type `dep`.
 *
 * Dependencies are restricted to generic and non-generic reference types.
 *
 * Dependencies on parameterized or raw types are decomposed into
 * a dependency on the corresponding generic type and separate
 * dependencies on (source declarations of) any type arguments.
 *
 * For example, a dependency on type `List<Set<String>>` is represented by
 * dependencies on the generic types `List` and `Set` as well as a dependency
 * on the type `String` but not on the parameterized types `List<Set<String>>`
 * or `Set<String>`.
 */
predicate depends(RefType t, RefType dep) {
  // Type `t` is neither a parameterized nor a raw type and is distinct from `dep`.
  not isParameterized(t) and
  not isRaw(t) and
  not t = dep and
  // Type `t` depends on:
  (
    // its supertypes,
    usesType(t.getASupertype(), dep)
    or
    // its enclosing type,
    usesType(t.(NestedType).getEnclosingType(), dep)
    or
    // the type of any field declared in `t`,
    exists(Field f | f.getDeclaringType() = t |
      usesType(f.getType(), dep)
    ) or
    // the return type of any method declared in `t`,
    exists(Method m | m.getDeclaringType() = t |
      usesType(m.getReturnType(), dep)
    ) or
    // the type of any parameter of a callable in `t`,
    exists(Callable c | c.getDeclaringType() = t |
      usesType(c.getAParamType(), dep)
    ) or
    // the type of any exception in the `throws` clause of a callable declared in `t`,
    exists(Exception e | e.getCallable().getDeclaringType() = t |
      usesType(e.getType(), dep)
    ) or
    // the declaring type of a callable accessed in `t`,
    exists(Callable c |
      c.getAReference().getEnclosingCallable().getDeclaringType() = t |
      usesType(c.getSourceDeclaration().getDeclaringType(), dep)
    ) or
    // the declaring type of a field accessed in `t`,
    exists(Field f |
      f.getAnAccess().getEnclosingCallable().getDeclaringType() = t  |
      usesType(f.getSourceDeclaration().getDeclaringType(), dep)
    ) or
    // the type of a local variable declared in `t`,
    exists(LocalVariableDeclExpr decl |
      decl.getEnclosingCallable().getDeclaringType() = t |
      usesType(decl.getType(), dep)
    ) or
    // the type of a type literal accessed in `t`,
    exists(TypeLiteral l |
      l.getEnclosingCallable().getDeclaringType() = t |
      usesType(l.getTypeName().getType(), dep)
    ) or
    // the type of an annotation (or one of its element values) that annotates `t` or one of its members,
    exists(Annotation a |
      a.getAnnotatedElement() = t or
      a.getAnnotatedElement().(Member).getDeclaringType() = t |
      usesType(a.getType(), dep) or
      usesType(a.getAValue().getType(), dep)
    ) or
    // the type accessed in an `instanceof` expression in `t`.
    exists(InstanceOfExpr ioe |
      t = ioe.getEnclosingCallable().getDeclaringType() |
      usesType(ioe.getTypeName().getType(), dep)
    )
  )
}

/**
 * Bind the reference type `dep` to the source declaration of any types used to construct `t`,
 * including (possibly nested) type parameters of parameterized types, element types of array types,
 * and bounds of type variables or wildcards.
 */
cached
predicate usesType(Type t, RefType dep) {
  dep = inside*(t).getSourceDeclaration() and
  not dep instanceof TypeVariable and
  not dep instanceof Wildcard and
  not dep instanceof Array
}

/**
 * A type argument of a parameterized type,
 * the element type of an array type, or
 * a bound of a type variable or wildcard.
 */
private
RefType inside(Type t) {
  result = t.(TypeVariable).getATypeBound().getType() or
  result = t.(Wildcard).getATypeBound().getType() or
  result = t.(ParameterizedType).getATypeArgument() or
  result = t.(Array).getElementType()
}
