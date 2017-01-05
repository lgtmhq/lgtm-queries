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
 * A library for working with generic types.
 *
 * A generic type as declared in the program, for example
 *
 * ```
 *   class X<T> { }
 * ```
 * is represented by a `GenericType`.
 *
 * A parameterized instance of such a type, for example
 *
 * ```
 *   X<String>
 * ```
 * is represented by a `ParameterizedType`.
 *
 * For dealing with legacy code that is unaware of generics, every generic type has a
 * "raw" version, represented by a `RawType`. In the example, `X` is the raw version of
 * `X<T>`.
 *
 * The erasure of a parameterized or raw type is its generic counterpart.
 *
 * Type parameters may have bounds as in
 *
 * ```
 *   class X<T extends Number> { }
 * ```
 * which are represented by a `TypeBound`.
 *
 * The terminology for generic methods is analogous.
 */

import Type

/**
 * A generic type is a type that has a type parameter.
 *
 * For example, `X` in `class X<T> { }`.
 */
class GenericType extends RefType {
  GenericType() { typeVars(_,_,_,_,this) }

  /**
   * A parameterization of this generic type, where each use of
   * a formal type parameter has been replaced by its argument.
   *
   * For example, `List<Number>` is a parameterization of
   * the generic type `List<E>`, where `E` is a type parameter.
   */
  ParameterizedType getAParameterizedType() { result.getErasure() = this }

  /**
   * The raw version of this generic type is the type that is formed by
   * using the name of this generic type without specifying its type arguments.
   *
   * For example, `List` is the raw version of the generic type
   * `List<E>`, where `E` is a type parameter.
   */
  RawType getRawType() { result.getErasure() = this }

  /**
   * The `i`-th type parameter of this generic type.
   */
  TypeVariable getTypeParameter(int i) { typeVars(result, _, i, _, this) }

  /**
   * A type parameter of this generic type.
   */
  TypeVariable getATypeParameter() { result = getTypeParameter(_) }

  /**
   * The number of type parameters of this generic type.
   */
  int getNumberOfTypeParameters() { result = strictcount(getATypeParameter()) }
}

/** A generic type that is a class. */
class GenericClass extends GenericType, Class { 
  /** The source declaration of this generic class. */
  RefType getSourceDeclaration() { result = Class.super.getSourceDeclaration() }

  /** An annotation attached to this generic class. */
  Annotation getAnAnnotation() { result = Class.super.getAnAnnotation() }
}

/** A generic type that is an interface. */
class GenericInterface extends GenericType, Interface { 
  RefType getSourceDeclaration() { result = Interface.super.getSourceDeclaration() }
  predicate isAbstract() { Interface.super.isAbstract() }
}

/**
 * A common super-class for Java types that may have a type bound.
 * This includes type parameters and wildcards.
 */
abstract class BoundedType extends RefType, @boundedtype {
  /** Whether this type is bounded. */
  predicate hasTypeBound() { exists(TypeBound tb | tb = this.getATypeBound()) }

  /** A type bound for this type, if any. */
  TypeBound getATypeBound() { result.getBoundedType() = this }
  
  /**
   * The upper type bound of this type, or `Object`
   * if no explicit type bound is present.
   */
  abstract RefType getUpperBoundType();
}

/**
 * A type parameter used in the declaration of a generic type or method.
 *
 * For example, `T` is a type parameter in
 * `class X<T> { }` and in `<T> void m() { }`.
 */
class TypeVariable extends BoundedType, @typevariable {
  /** The generic type that is parameterized by this type parameter, if any. */
  RefType getGenericType() { typeVars(this,_,_,_,result) }

  /** The generic callable that is parameterized by this type parameter, if any. */
  GenericCallable getGenericCallable() { typeVars(this,_,_,_,result) }

  /** DEPRECATED: Use `getGenericCallable()` instead. */
  deprecated Method getGenericMethod() { typeVars(this,_,_,_,result) }

  /**
   * The upper bound of this type parameter, or `Object`
   * if no explicit type bound is present.
   */
  RefType getUpperBoundType() {
    if this.hasTypeBound() then
      result = this.getATypeBound().getType()
    else
      result instanceof TypeObject
  }

  /** The lexically enclosing package of this type parameter, if any. */
  Package getPackage() {
    result = getGenericType().getPackage() or
    result = getGenericCallable().getDeclaringType().getPackage()
  }
}

/**
 * A wildcard used as a type argument.
 *
 * For example, in
 *
 * ```
 *   Map<? extends Number, ? super Float>
 * ```
 * the first wildcard has an upper bound of `Number`
 * and the second wildcard has a lower bound of `Float`.
 */
class Wildcard extends BoundedType, @wildcard {
  /** Whether this wildcard has an upper bound. */
  predicate hasUpperBound() {
    wildcards(this, _, 1)
  }

  /** Whether this wildcard has a lower bound. */
  predicate hasLowerBound() {
    wildcards(this, _, 2)
  }
  
  /** The upper bound for this wildcard, if any. */
  TypeBound getUpperBound() {
    this.hasUpperBound() and result = this.getATypeBound()
  }
  
  /**
   * The upper bound type of this wildcard, or `Object`
   * if no explicit type bound is present.
   */
  RefType getUpperBoundType() {
    if this.hasUpperBound() then
      result = this.getUpperBound().getType()
    else
      result instanceof TypeObject
  }

  /** The lower bound of this wildcard, if any. */
  TypeBound getLowerBound() {
    this.hasLowerBound() and result = this.getATypeBound()
  }
  
  /**
   * The lower bound type for this wildcard,
   * if an explicit lower bound is present.
   */
  Type getLowerBoundType() {
    result = this.getLowerBound().getType()
  }

  /**
   * Whether this is the unconstrained wildcard `?`.
   */
  predicate isUnconstrained() {
    not hasUpperBound() and
    not hasLowerBound()
  }
}

/**
 * A type bound on a type variable.
 *
 * For example, `Number` is a type bound on the type variable
 * `T` in `class X<T extends Number> { }`.
 *
 * Type variables can have multiple type bounds, specified by
 * an intersection type `T0 & T1 & ... & Tn`.
 * A bound with position 0 is an interface type or class type (possibly `Object`) and
 * a bound with a non-zero position is an interface type.
 */
class TypeBound extends @typebound {
  /**
   * The type variable that is bounded by this type bound.
   *
   * For example, `T` is the type variable bounded by the
   * type `Number` in `T extends Number`.
   */
  BoundedType getBoundedType() { typeBounds(this,_,_,result) }

  /**
   * The type of this bound.
   *
   * For example, `Number` is the type of the bound (of
   * the type variable `T`) in `T extends Number`.
   */
  RefType getType() { typeBounds(this,result,_,_) }

  /**
   * The (zero-indexed) position of this bound.
   *
   * For example, in
   *
   * ```
   *   class X<T extends Runnable & Cloneable> { }
   * ```
   * the position of the bound `Runnable` is 0 and
   * the position of the bound `Cloneable` is 1.
   */
  int getPosition() { typeBounds(this,_,result,_) }

  /** A printable representation of this type bound. */
  string toString() { result = this.getType().getName() }
}

// -------- Parameterizations of generic types  --------

/**
 * A parameterized type is an instantiation of a generic type, where
 * each formal type variable has been replaced with a type argument.
 *
 * For example, `List<Number>` is a parameterization of
 * the generic type `List<E>`, where `E` is a type parameter.
 */
class ParameterizedType extends RefType {
  ParameterizedType() {
    typeArgs(_,_,this) or
    typeVars(_,_,_,_,this)
  }

  /**
   * The erasure of a parameterized type is its generic counterpart.
   *
   * For example, the erasure of both `X<Number>` and `X<Integer>` is `X<T>`.
   */
  RefType getErasure() { erasure(this,result) }

  /**
   * The generic type corresponding to this parameterized type.
   *
   * For example, the generic type for both `X<Number>` and `X<Integer>` is `X<T>`.
   */
  GenericType getGenericType() { result.getAParameterizedType() = this }

  /**
   * A type argument for this parameterized type.
   *
   * For example, `Number` in `List<Number>`.
   */
  RefType getATypeArgument() {
    typeArgs(result,_,this) or
    typeVars(result,_,_,_,this)
  }

  /** The type argument of this parameterized type at the specified position. */
  RefType getTypeArgument(int pos) {
    typeArgs(result,pos,this) or
    typeVars(result,_,pos,_,this)
  }

  /** The number of type arguments of this parameterized type. */
  int getNumberOfTypeArguments() {
    result = count(int pos |
      typeArgs(_,pos,this) or
      typeVars(_,_,pos,_,this)
    )
  }

  /** Whether this type originates from source code. */
  predicate fromSource() { typeVars(_,_,_,_,this) and RefType.super.fromSource() }
}

/** A parameterized type that is a class. */
class ParameterizedClass extends Class, ParameterizedType { 
  /** Whether this type originates from source code. */
  predicate fromSource() { ParameterizedType.super.fromSource() }

  /** The source declaration of this parameterized class. */
  RefType getSourceDeclaration() { result = Class.super.getSourceDeclaration() }

  /** An annotation attached to this parameterized class. */
  Annotation getAnAnnotation() { result = Class.super.getAnAnnotation() }
}

/** A parameterized type that is an interface. */
class ParameterizedInterface extends Interface, ParameterizedType {
  predicate fromSource() { ParameterizedType.super.fromSource() }
  RefType getSourceDeclaration() { result = Interface.super.getSourceDeclaration() }
  predicate isAbstract() { Interface.super.isAbstract() }
}

/**
 * The raw version of a generic type is the type that is formed by
 * using the name of a generic type without specifying its type arguments.
 *
 * For example, `List` is the raw version of the generic type
 * `List<E>`, where `E` is a type parameter.
 *
 * Raw types typically occur in legacy code that was written
 * prior to the introduction of generic types in Java 5.
 */
 class RawType extends RefType {
  RawType() { isRaw(this) }

  /**
   * The erasure of a raw type is its generic counterpart.
   *
   * For example, the erasure of `List` is `List<E>`.
   */
   RefType getErasure() { erasure(this,result) }

  /** Whether this type originates from source code. */
  predicate fromSource() { not any() }
}

/** A raw type that is a class. */
class RawClass extends Class, RawType { 
  /** Whether this type originates from source code. */
  predicate fromSource() { RawType.super.fromSource() }

  /** The source declaration of this raw class. */
  RefType getSourceDeclaration() { result = Class.super.getSourceDeclaration() }

  /** An annotation attached to this raw class. */
  Annotation getAnAnnotation() { result = Class.super.getAnAnnotation() }
}

/** A raw type that is an interface. */
class RawInterface extends Interface, RawType { 
  predicate fromSource() { RawType.super.fromSource() }
  RefType getSourceDeclaration() { result = Interface.super.getSourceDeclaration() }
  predicate isAbstract() { Interface.super.isAbstract() }
}

// -------- Generic callables  --------

/**
 * A generic callable is a callable with a type parameter.
 */
class GenericCallable extends Callable {
  GenericCallable() { typeVars(_,_,_,_,this) }

  /**
   * The `i`-th type parameter of this generic callable.
   */
  TypeVariable getTypeParameter(int i) { typeVars(result, _, i, _, this) }

  /**
   * A type parameter of this generic callable.
   */
  TypeVariable getATypeParameter() { result = getTypeParameter(_) }

  /**
   * The number of type parameters of this generic callable.
   */
  int getNumberOfTypeParameters() { result = strictcount(getATypeParameter()) }
}

/**
 * A generic constructor is a constructor with a type parameter.
 *
 * For example, `<T> C(T t) { }` is a generic constructor for type `C`.
 */
class GenericConstructor extends Constructor, GenericCallable {
  GenericConstructor getSourceDeclaration() { result = Constructor.super.getSourceDeclaration() }
  ConstructorCall getAReference() { result = Constructor.super.getAReference() }
  string getSignature() { result = Constructor.super.getSignature() }
  predicate isAbstract() { Constructor.super.isAbstract() }
  predicate isPublic() { Constructor.super.isPublic() }
  predicate isStrictfp() { Constructor.super.isStrictfp() }
  string getIconPath() { result = Constructor.super.getIconPath() }
}

/**
 * A generic method is a method with a type parameter.
 *
 * For example, `<T> void m(T t) { }` is a generic method.
 */
class GenericMethod extends Method, GenericCallable {
  GenericMethod getSourceDeclaration() { result = Method.super.getSourceDeclaration() }
  MethodAccess getAReference() { result = Method.super.getAReference() }
  string getSignature() { result = Method.super.getSignature() }
  predicate isAbstract() { Method.super.isAbstract() }
  predicate isPublic() { Method.super.isPublic() }
  predicate isStrictfp() { Method.super.isStrictfp() }
  string getIconPath() { result = Method.super.getIconPath() }

  /**
   * A parameterization of this generic method.
   *
   * A parameterized method is an instantiation of a generic method, where
   * each formal type variable has been replaced with a type argument.
   *
   * DEPRECATED: to reason about type arguments of generic method invocations,
   * use `MethodAccess.getATypeArgument()` or `MethodAccess.getTypeArgument(int)`.
   */
  deprecated
  ParameterizedMethod getAParameterizedMethod() { result.getErasure() = this }

  /**
   * A raw method corresponding to this generic method.
   *
   * DEPRECATED: to reason about type arguments of generic method invocations,
   * use `MethodAccess.getATypeArgument()` or `MethodAccess.getTypeArgument(int)`.
   */
  deprecated
  RawMethod getARawMethod() { result.getErasure() = this }
}

// -------- Parameterizations of generic methods  --------

/**
 * A parameterized method is an instantiation of a generic method, where
 * each formal type variable has been replaced with a type argument.
 *
 * DEPRECATED: to reason about type arguments of generic method invocations,
 * use `MethodAccess.getATypeArgument()` or `MethodAccess.getTypeArgument(int)`.
 */
deprecated
class ParameterizedMethod extends Method {
  ParameterizedMethod() { isParameterized(this) }

  /**
   * The erasure of a parameterized method is its generic counterpart.
   *
   * For example, the erasure of `<Number> m(Number t) { }`
   * is `<T> m(T t) { }`.
   */
  Method getErasure() { erasure(this,result) }
}

/**
 * A raw method is a generic method that is used as if it was not generic.
 *
 * DEPRECATED: to reason about type arguments of generic method invocations,
 * use `MethodAccess.getATypeArgument()` or `MethodAccess.getTypeArgument(int)`.
 */
deprecated
class RawMethod extends Method {
  RawMethod() { isRaw(this) }

  /** The erasure of a raw method is its generic counterpart. */
  Method getErasure() { erasure(this,result) }
}
