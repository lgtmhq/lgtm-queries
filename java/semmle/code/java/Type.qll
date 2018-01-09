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
 * Provides classes and predicates for working with Java types.
 *
 * Types can be primitive types (`PrimitiveType`), array types (`Array`), or reference
 * types (`RefType`), where the latter are either classes (`Class`) or interfaces
 * (`Interface`).
 *
 * Reference types can be at the top level (`TopLevelType`) or nested (`NestedType`).
 * Classes can also be local (`LocalClass`) or anonymous (`AnonymousClass`).
 * Enumerated types (`EnumType`) are a special kind of class.
 */

import Member
import Modifier
import JDK

/**
 * Holds if reference type `t` is an immediate super-type of `sub`.
 */
cached
predicate hasSubtype(RefType t, Type sub) {
  // Direct subtype.
  (extendsReftype(sub, t) and t != sub) or
  implInterface(sub, t) or
  // A parameterized type `T<A>` is a subtype of the corresponding raw type `T<>`.
  (parSubtypeRaw(t, sub) and t != sub) or
  // Array subtyping is covariant.
  (arraySubtype(t, sub) and t != sub) or
  // Type parameter containment for parameterized types.
  (parContainmentSubtype(t, sub) and t != sub) or
  // Type variables are subtypes of their upper bounds.
  (typeVarSubtypeBound(t, sub) and t != sub)
}

private
predicate typeVarSubtypeBound(RefType t, TypeVariable tv) {
  if tv.hasTypeBound() then
    t = tv.getATypeBound().getType()
  else
    t instanceof TypeObject
}

private
predicate parContainmentSubtype(ParameterizedType pt, ParameterizedType psub) {
  pt != psub and
  typeArgumentsContain(_, pt, psub, pt.getNumberOfTypeArguments()-1)
}

private
predicate parSubtypeRaw(RefType t, ParameterizedType sub) {
  t = sub.getErasure().(GenericType).getRawType()
}

private
predicate arraySubtype(Array sup, Array sub) {
  hasSubtype(sup.getComponentType(), sub.getComponentType())
}

/**
 * Auxiliary index: The `result` is the `index`-th type parameter of `t`, which
 * is a parameterization of `g`.
 */
private
RefType parameterisationTypeArgument(GenericType g, ParameterizedType t, int index) {
  g = t.getGenericType() and
  result = t.getTypeArgument(index)
}

private predicate varianceCandidate(ParameterizedType pt) {
  pt.getATypeArgument() instanceof Wildcard
}

/**
 * Holds if every type argument of `s` (up to `n`) contains the corresponding type argument of `t`.
 * Both `s` and `t` are constrained to being parameterizations of `g`.
 */
private
predicate typeArgumentsContain(GenericType g, ParameterizedType s, ParameterizedType t, int n) {
  varianceCandidate(s) and
  contains(g, s, t, n) and
  (n = 0 or typeArgumentsContain(g, s, t, n-1))
}

/**
 * Does the `n`-th type argument of `sParm` contain the `n`-th type argument of `tParm`,
 * where both `sParm` and `tParm` are parameterizations of the same generic type `g`?
 *
 * See JLS 4.5.1, Type Arguments of Parameterized Types.
 */
private 
predicate contains(GenericType g, ParameterizedType sParm, ParameterizedType tParm, int n) {
  exists (RefType s, RefType t |
    containsAux(g, tParm, n, s, t) and
    s = parameterisationTypeArgument(g, sParm, n)
  )
}

pragma[nomagic]
private predicate containsAux(GenericType g, ParameterizedType tParm, int n, RefType s, RefType t) {
  typeArgumentContains(s,t) and
  t = parameterisationTypeArgument(g, tParm, n)
}

/**
 * Holds if the type argument `s` contains the type argument `t`.
 * 
 * See JLS 4.5.1, Type Arguments of Parameterized Types.
 */
private
predicate typeArgumentContains(RefType s, RefType t) {
    exists (RefType tUpperBound | tUpperBound = t.(Wildcard).getUpperBound().getType() |
      // ? extends T <= ? extends S if T <: S
      hasSubtypeStar(s.(Wildcard).getUpperBound().getType(), tUpperBound) or
      // ? extends T <= ?
      s.(Wildcard).isUnconstrained()
    ) or
    exists (RefType tLowerBound | tLowerBound = t.(Wildcard).getLowerBound().getType() |
      // ? super T <= ? super S if s <: T
      hasSubtypeStar(tLowerBound, s.(Wildcard).getLowerBound().getType()) or
      // ? super T <= ?
      s.(Wildcard).isUnconstrained() or
      // ? super T <= ? extends Object
      s.(Wildcard).getUpperBound().getType() instanceof TypeObject
    ) or
    // T <= T
    s = t or
    // T <= ? extends T
    hasSubtypeStar(s.(Wildcard).getUpperBound().getType(), t) or
    // T <= ? super T
    hasSubtypeStar(t, s.(Wildcard).getLowerBound().getType())
}

predicate hasSubtypeStar(RefType t, RefType sub) {
  sub = t
  or
  hasSubtype(t, sub)
  or
  exists (RefType mid | hasSubtypeStar(t, mid) and hasSubtype(mid, sub))
}

/** Holds if type `t` declares member `m`. */
predicate declaresMember(Type t, @member m) {
  methods(m,_,_,_,t,_) or
  constrs(m,_,_,_,t,_) or
  fields(m,_,_,t,_) or
  (enclInReftype(m,t) and
   // Since the type `@member` in the dbscheme includes all `@reftype`s,
   // anonymous and local classes need to be excluded here.
   not m instanceof AnonymousClass and
   not m instanceof LocalClass)
}

/**
 * A common abstraction for all Java types, including
 * primitive, class, interface and array types.
 */
class Type extends Element, @type {
  /**
   * The JVM descriptor for this type, as used in bytecode.
   */
  string getTypeDescriptor() { none() }

  /** Gets the erasure of this type. */
  Type getErasure() { result = erase(this) }
}

/**
 * An array type.
 *
 * Array types are implicitly declared when used; there is
 * an array declaration for each array type used in the system.
 */
class Array extends RefType, @array {
  /**
   * The component type of an array type is the type of its components.
   *
   * For example, the component type of `Object[][]` is `Object[]`.
   */
  Type getComponentType() { arrays(this, _, _, _, result) }

  /**
   * The element type of an array type is the base type used to construct the array.
   *
   * For example, the element type of `Object[][]` is `Object`.
   */
  Type getElementType() { arrays(this, _, result, _, _) }

  /**
   * The arity of the array type.
   *
   * For example, the dimension of `Object[][]` is 2.
   */
  int getDimension() { arrays(this, _, _, result, _) }

  /**
   * The JVM descriptor for this type, as used in bytecode.
   */
  string getTypeDescriptor() {
    result = "[" + this.getComponentType().getTypeDescriptor()
  }
}

/**
 * A common super-class for various kinds of reference types,
 * including classes, interfaces, type parameters and arrays.
 */
class RefType extends Type, Annotatable, Modifiable, @reftype {
  /** The package in which this type is declared. */
  Package getPackage() {
    classes(this,_,result,_) or
    interfaces(this,_,result,_)
  }

  /** The type in which this reference type is enclosed, if any. */
  RefType getEnclosingType() {
    enclInReftype(this, result)
  }

  /** The compilation unit in which this type is declared. */
  CompilationUnit getCompilationUnit() { result = this.getFile() }

  /** Holds if `t` is an immediate supertype of this type. */
  predicate hasSupertype(RefType t) { hasSubtype(t,this) }

  /** Holds if `t` is an immediate subtype of this type. */
  predicate hasSubtype(RefType t) { hasSubtype(this,t) }

  /** A direct subtype of this type. */
  RefType getASubtype() { hasSubtype(this,result) }

  /** A direct supertype of this type. */
  RefType getASupertype() { hasSubtype(result,this) }

  /** A direct or indirect supertype of this type, including itself. */
  RefType getAnAncestor() { hasSubtypeStar(result, this) }

  /**
   * The source declaration of a direct supertype of this type, excluding itself.
   *
   * Note, that a generic type is the source declaration of a direct supertype
   * of itself, namely the corresponding raw type, and this case is thus
   * explicitly excluded. See also `getSourceDeclaration()`.
   */
  RefType getASourceSupertype() {
    result = this.getASupertype().getSourceDeclaration() and
    result != this
  }

  /**
   * Holds if `t` is an immediate super-type of this type using only the immediate
   * `extends` or `implements` relationships.  In particular, this excludes
   * parameter containment sub-typing for parameterized types.
   */
  predicate extendsOrImplements(RefType t) {
    extendsReftype(this, t) or
    implInterface(this, t) or
    typeVarSubtypeBound(t, this)
  }

  /** Holds if this type declares any members. */
  predicate hasMember() { exists(getAMember()) }

  /** A member declared in this type. */
  Member getAMember() { this = result.getDeclaringType() }

  /** A method declared in this type. */
  Method getAMethod() { this = result.getDeclaringType() }

  /** A constructor declared in this type. */
  Constructor getAConstructor() { this = result.getDeclaringType() }

  /** A method or constructor declared in this type. */
  Callable getACallable() { this = result.getDeclaringType() }

  /** A field declared in this type. */
  Field getAField() { this = result.getDeclaringType() }

  /** Holds if this type declares a method with the specified name. */
  predicate declaresMethod(string name) { this.getAMethod().getName() = name }

  /** Holds if this type declares a method with the specified name and number of parameters. */
  predicate declaresMethod(string name, int n) {
    exists(Method m | m = this.getAMethod() |
      m.getName() = name and
      m.getNumberOfParameters() = n
    )
  }

  /** Holds if this type declares a field with the specified name. */
  predicate declaresField(string name) { this.getAField().getName() = name }

  /** The number of methods declared in this type. */
  int getNumberOfMethods() { result = count(Method m | m.getDeclaringType() = this) }

  /**
   * Holds if this type declares or inherits method `m`, which is declared
   * in `declaringType`.
   */
  cached
  predicate hasMethod(Method m, RefType declaringType) {
    hasNonInterfaceMethod(m, declaringType) or
    hasInterfaceMethod(m, declaringType)
  }

  private predicate noMethodExtraction() {
    not methods(_,_,_,_,this,_) and
    exists(Method m | methods(m,_,_,_,getSourceDeclaration(),_) and m.isInheritable())
  }

  private predicate canInheritFrom(RefType t) {
    t = getASupertype() and
    (noMethodExtraction() implies supertypeSrcDecl(t, getSourceDeclaration()))
  }

  pragma[nomagic]
  private predicate supertypeSrcDecl(RefType sup, RefType srcDecl) {
    sup = getASupertype() and
    srcDecl = sup.getSourceDeclaration()
  }

  private predicate hasNonInterfaceMethod(Method m, RefType declaringType) {
    m = getAMethod() and this = declaringType and not declaringType instanceof Interface or
    exists(RefType sup |
      sup = getASupertype() and
      (if m.isPackageProtected() then sup.getPackage() = this.getPackage() else any()) and
      (not sup instanceof Interface or this instanceof Interface) and
      canInheritFrom(sup) and
      sup.hasNonInterfaceMethod(m, declaringType) and
      exists(string signature | methods(m,_,signature,_,_,_) and not methods(_,_,signature,_,this,_)) and
      m.isInheritable()
    )
  }

  private predicate cannotInheritInterfaceMethod(string signature) {
    methods(_,_,signature,_,this,_) or
    exists(Method m | hasNonInterfaceMethod(m, _) and methods(m,_,signature,_,_,_))
  }

  private predicate interfaceMethodCandidateWithSignature(Method m, string signature, RefType declaringType) {
    m = getAMethod() and this = declaringType and declaringType instanceof Interface and methods(m,_,signature,_,_,_) or
    exists(RefType sup |
      sup = getASupertype() and
      sup.interfaceMethodCandidateWithSignature(m, signature, declaringType) and
      not cannotInheritInterfaceMethod(signature) and
      canInheritFrom(sup) and
      m.isInheritable()
    )
  }

  pragma[nomagic]
  private predicate overrideEquivalentInterfaceMethodCandidates(Method m1, Method m2) {
    exists(string signature |
      interfaceMethodCandidateWithSignature(m1, signature, _) and
      interfaceMethodCandidateWithSignature(m2, signature, _) and
      m1 != m2
    )
  }

  pragma[noinline]
  private predicate overriddenInterfaceMethodCandidate(Method m) {
    exists(Method m2 |
      overrideEquivalentInterfaceMethodCandidates(m, m2) and
      m2.overrides(m)
    )
  }

  private predicate hasInterfaceMethod(Method m, RefType declaringType) {
    interfaceMethodCandidateWithSignature(m, _, declaringType) and
    not overriddenInterfaceMethodCandidate(m)
  }

  /** Holds if this type declares or inherits the specified member. */
  predicate inherits(Member m) {
    exists(Field f | f = m |
      f = getAField() or
      not f.isPrivate() and not declaresField(f.getName()) and getASupertype().inherits(f) or
      getSourceDeclaration().inherits(f)
    )
    or
    hasMethod((Method)m, _)
  }

  /** Holds if this is a top-level type, which is not nested inside any other types. */
  predicate isTopLevel() { this instanceof TopLevelType }

  /** Holds if this type is declared in a specified package with the specified name. */
  predicate hasQualifiedName(string package, string type) {
    this.getPackage().hasName(package) and type = this.nestedName()
  }

  /**
   * The JVM descriptor for this type, as used in bytecode.
   */
  string getTypeDescriptor() {
    result = "L" + this.getPackage().getName().replaceAll(".", "/") + "/" +
      this.getSourceDeclaration().nestedName() + ";"
  }

  /**
   * The qualified name of this type.
   */
  string getQualifiedName() {
    exists (string pkgName | pkgName = getPackage().getName() |
      if pkgName = "" then
        result = nestedName()
      else
        result = pkgName + "." + nestedName()
    )
  }

  /** The nested name of this type. */
  string nestedName() {
     not (this instanceof NestedType) and result = this.getName()
     or
     this.(NestedType).getEnclosingType().nestedName() + "$" + this.getName() = result
  }

  /**
   * The source declaration of this type.
   *
   * For parameterized instances of generic types and raw types, the
   * source declaration is the corresponding generic type.
   *
   * For non-parameterized types declared inside a parameterized
   * instance of a generic type, the source declaration is the
   * corresponding type in the generic type.
   *
   * For all other types, the source declaration is the type itself.
   */
  RefType getSourceDeclaration() { result = this }

  /** Holds if this type is the same as its source declaration. */
  predicate isSourceDeclaration() { this.getSourceDeclaration() = this }

  /** Cast this reference type to a class that provides access to metrics information. */
  MetricRefType getMetrics() { result = this }

  /**
   * A common (reflexive, transitive) subtype of the erasures of
   * types `t1` and `t2`, if it exists.
   *
   * If there is no such common subtype, then the two types are disjoint.
   * However, the converse is not true; for example, the parameterized types
   * `List<Integer>` and `Collection<String>` are disjoint,
   * but their erasures (`List` and `Collection`, respectively)
   * do have common subtypes (such as `List` itself).
   *
   * For the definition of the notion of *erasure* see JLS v8, section 4.6 (Type Erasure).
   */
  pragma[inline]
  RefType commonSubtype(RefType other) {
    result.getASourceSupertype*() = erase(this) and
    result.getASourceSupertype*() = erase(other)
  }
}

/** A class declaration. */
class Class extends RefType, @class {
  /** Holds if this class is an anonymous class. */
  predicate isAnonymous() { isAnonymClass(this,_) }

  /** Holds if this class is a local class. */
  predicate isLocal() { isLocalClass(this,_) }

  RefType getSourceDeclaration() { classes(this,_,_,result) }

  /**
   * An annotation that applies to this class.
   *
   * Note that a class may inherit annotations from super-classes.
   */
  Annotation getAnAnnotation() {
    result = RefType.super.getAnAnnotation() or
    exists(AnnotationType tp | tp = result.getType() |
      tp.isInherited() and
      not exists(Annotation ann | ann = RefType.super.getAnAnnotation() | ann.getType() = tp) and
      result = this.getASupertype().(Class).getAnAnnotation()
    )
  }
}

/** An anonymous class. */
class AnonymousClass extends NestedClass {
  AnonymousClass() { this.isAnonymous() }

  /**
   * Utility method: an integer that is larger for classes that
   * are defined textually later.
   */
  private int rankInParent(RefType parent) {
    this.getEnclosingType() = parent and
    exists(Location myLocation, File f, int maxCol | myLocation = this.getLocation() |
      f = myLocation.getFile() and
      maxCol = max(Location loc | loc.getFile() = f | loc.getStartColumn()) and
      result = myLocation.getStartLine() * maxCol + myLocation.getStartColumn()
    )
  }

  /**
   * The JVM descriptor for this type, as used in bytecode.
   *
   * For an anonymous class, the type descriptor is the descriptor of the
   * enclosing type followed by a (1-based) counter of anonymous classes
   * declared within that type.
   */
  string getTypeDescriptor() {
    exists(RefType parent | parent = this.getEnclosingType() |
      exists(int num | num = 1 + count(AnonymousClass other | other.rankInParent(parent) < rankInParent(parent)) |
        exists(string parentWithSemi | parentWithSemi = parent.getTypeDescriptor() |
          result = parentWithSemi.prefix(parentWithSemi.length() - 1) + "$" + num + ";"
        )
      )
    )
  }

  /** The class instance expression where this anonymous class occurs. */
  ClassInstanceExpr getClassInstanceExpr() { isAnonymClass(this, result) }

  string toString() { result = "new " + this.getClassInstanceExpr().getTypeName() + "(...) { ... }" }

  /**
   * The qualified name of this type.
   *
   * Anonymous classes do not have qualified names, so we use
   * the string `"<anonymous class>"` as a placeholder.
   */
  string getQualifiedName() { result = "<anonymous class>" }
}

/** A local class. */
class LocalClass extends NestedClass {
  LocalClass() { this.isLocal() }

  /** The statement that declares this local class. */
  LocalClassDeclStmt getLocalClassDeclStmt() { isLocalClass(this, result) }
}

/** A top-level type. */
class TopLevelType extends RefType {
  TopLevelType() {
    not enclInReftype(this,_) and
    (this instanceof Class or this instanceof Interface)
  }
}

/** A top-level class. */
class TopLevelClass extends TopLevelType, Class {
}

/** A nested type is a type declared within another type. */
class NestedType extends RefType {
  NestedType() {
    enclInReftype(this,_)
  }

  /** The type enclosing this nested type. */
  RefType getEnclosingType() {
    enclInReftype(this,result)
  }

  /** The nesting depth of this nested type. Top-level types have nesting depth 0. */
  int getNestingDepth() {
    if getEnclosingType() instanceof NestedType then
      result = getEnclosingType().(NestedType).getNestingDepth() + 1
    else
      result = 1
  }

  predicate isPublic() {
    super.isPublic() or
    // JLS 9.5: A member type declaration in an interface is implicitly public and static
    exists(Interface i | this = i.getAMember())
  }

  predicate isStrictfp() {
    super.isStrictfp() or
    // JLS 8.1.1.3, JLS 9.1.1.2
    getEnclosingType().isStrictfp()
  }

  /**
   * Holds if this nested type is static.
   *
   * A nested type is static either if it is explicitly declared as such
   * using the modifier `static`, or if it is implicitly static
   * because one of the following holds:
   *
   * - it is a member type of an interface,
   * - it is a member interface, or
   * - it is a nested enum type.
   *
   * See JLS v8, section 8.5.1 (Static Member Type Declarations),
   * section 8.9 (Enums) and section 9.5 (Member Type Declarations).
   */
  predicate isStatic() {
    super.isStatic() or
    // JLS 8.5.1: A member interface is implicitly static.
    this instanceof Interface or
    // JLS 8.9: A nested enum type is implicitly static.
    this instanceof EnumType or
    // JLS 9.5: A member type declaration in an interface is implicitly public and static
    exists(Interface i | this = i.getAMember())
  }
}

/**
 * A class declared within another type.
 *
 * This includes (static and non-static) member classes,
 * local classes and anonymous classes.
 */
class NestedClass extends NestedType, Class {
}

/**
 * An inner class is a nested class that is neither
 * explicitly nor implicitly declared static.
 */
class InnerClass extends NestedClass {
  InnerClass() {
    not this.isStatic()
  }
}

/** An interface. */
class Interface extends RefType, @interface {
  RefType getSourceDeclaration() { interfaces(this,_,_,result) }

  predicate isAbstract() {
    // JLS 9.1.1.1: "Every interface is implicitly abstract"
    any()
  }
}

/** A class or interface. */
class ClassOrInterface extends RefType {
  ClassOrInterface() {
    this instanceof Class or
    this instanceof Interface
  }
}

/**
 * A primitive type.
 *
 * This includes `boolean`, `byte`, `short`,
 * `char`, `int`, `long`, `float`,
 * and `double`.
 */
class PrimitiveType extends Type, @primitive {
  PrimitiveType() {
    this.getName().regexpMatch("float|double|int|boolean|short|byte|char|long")
  }

  /** The boxed type corresponding to this primitive type. */
  BoxedType getBoxedType() {
    result.getPrimitiveType() = this
  }

  /**
   * The JVM descriptor for this type, as used in bytecode.
   */
  string getTypeDescriptor() {
       (this.hasName("float") and result = "F")
    or (this.hasName("double") and result = "D")
    or (this.hasName("int") and result = "I")
    or (this.hasName("boolean") and result = "Z")
    or (this.hasName("short") and result = "S")
    or (this.hasName("byte") and result = "B")
    or (this.hasName("char") and result = "C")
    or (this.hasName("long") and result = "J")
  }

  /**
   * A default value for this primitive type, as assigned by the compiler
   * for variables that are declared but not initialized explicitly.
   * Typically zero for numeric and character types and `false` for `boolean`.
   *
   * For numeric primitive types, default literals of one numeric type are also
   * considered to be default values of all other numeric types, even if they
   * require an explicit cast.
   */
  Literal getADefaultValue() {
    getName() = "boolean" and result.getLiteral() = "false" or
    getName() = "char" and (result.getLiteral() = "'\\0'" or result.getLiteral() = "'\\u0000'") or
    getName().regexpMatch("(float|double|int|short|byte|long)") and result.getLiteral().regexpMatch("0(\\.0)?+[lLfFdD]?+")
  }
}

/** The type of the `null` literal. */
class NullType extends Type, @primitive {
  NullType() { this.hasName("<nulltype>") }
}

/** The `void` type. */
class VoidType extends Type, @primitive {
  VoidType() { this.hasName("void") }

  /**
   * The JVM descriptor for this type, as used in bytecode.
   */
  string getTypeDescriptor() {
    result = "V"
  }
}

/**
 * A boxed type.
 *
 * This includes `Boolean`, `Byte`, `Short`,
 * `Character`, `Integer`, `Long`, `Float`,
 * and `Double`.
 */
class BoxedType extends RefType {
  BoxedType() {
    this.hasQualifiedName("java.lang", "Float") or
    this.hasQualifiedName("java.lang", "Double") or
    this.hasQualifiedName("java.lang", "Integer") or
    this.hasQualifiedName("java.lang", "Boolean") or
    this.hasQualifiedName("java.lang", "Short") or
    this.hasQualifiedName("java.lang", "Byte") or
    this.hasQualifiedName("java.lang", "Character") or
    this.hasQualifiedName("java.lang", "Long")
  }

  /** The primitive type corresponding to this boxed type. */
  PrimitiveType getPrimitiveType() {
       (this.hasName("Float") and result.hasName("float"))
    or (this.hasName("Double") and result.hasName("double"))
    or (this.hasName("Integer") and result.hasName("int"))
    or (this.hasName("Boolean") and result.hasName("boolean"))
    or (this.hasName("Short") and result.hasName("short"))
    or (this.hasName("Byte") and result.hasName("byte"))
    or (this.hasName("Character") and result.hasName("char"))
    or (this.hasName("Long") and result.hasName("long"))
  }
}

/**
 * An enumerated type.
 *
 * Each enum type has zero or more enum constants which can
 * be enumerated over.
 * The type of an enum constant is the enum type itself.
 *
 * For example,
 *
 * ```
 *   enum X { A, B, C }
 * ```
 * is an enum type declaration, where the type of the enum
 * constant `X.A` is `X`.
*/
class EnumType extends Class {
  EnumType() { isEnumType(this) }

  /** The enum constant with the specified name. */
  EnumConstant getEnumConstant(string name)  {
    fields(result,_,_,this,_) and result.hasName(name)
  }

  /** An enum constant declared in this enum type. */
  EnumConstant getAnEnumConstant() {
    fields(result,_,_,this,_)
  }

  predicate isFinal() {
    // JLS 8.9: An enum declaration is implicitly `final` unless it contains
    // at least one enum constant that has a class body.
    not getAnEnumConstant().getAnAssignedValue().getType() instanceof AnonymousClass
  }
}

/** An enum constant is a member of a enum type. */
class EnumConstant extends Field {
  EnumConstant() { isEnumConst(this) }

  // JLS 8.9.3: For each enum constant `c` in the body of the declaration of
  // [enum type] `E`, `E` has an implicitly declared `public static final`
  // field of type `E` that has the same name as `c`.
  predicate isPublic() { any() }
  predicate isStatic() { any() }
  predicate isFinal() { any() }
}

/**
 * The erasure of a type.
 *
 * See JLS v8, section 4.6 (Type Erasure).
 */
private cached Type erase(Type t) {
  result = t.(Class).getSourceDeclaration() or
  result = t.(Interface).getSourceDeclaration() or
  result.(Array).getComponentType() = erase(t.(Array).getComponentType()) or
  result = erase(t.(BoundedType).getFirstUpperBoundType()) or
  result = (NullType)t or
  result = (VoidType)t or
  result = (PrimitiveType)t
}

/**
 * Is there a common (reflexive, transitive) subtype of the erasures of
 * types `t1` and `t2`?
 *
 * If there is no such common subtype, then the two types are disjoint.
 * However, the converse is not true; for example, the parameterized types
 * `List<Integer>` and `Collection<String>` are disjoint,
 * but their erasures (`List` and `Collection`, respectively)
 * do have common subtypes (such as `List` itself).
 *
 * For the definition of the notion of *erasure* see JLS v8, section 4.6 (Type Erasure).
 */
pragma[inline]
predicate haveIntersection(RefType t1, RefType t2) {
  exists(RefType e1, RefType e2 | e1 = erase(t1) and e2 = erase(t2) |
    e1 instanceof TypeObject or e2 instanceof TypeObject
    or
    not e1 instanceof TypeObject and not e2 instanceof TypeObject and
    exists(RefType commonSub | commonSub.getASourceSupertype*() = e1 and commonSub.getASourceSupertype*() = e2)
  )
}

/** An integral type, which may be either a primitive or a boxed type. */
class IntegralType extends Type {
  IntegralType() {
    exists(string name |
      name = this.(PrimitiveType).getName() or name = this.(BoxedType).getPrimitiveType().getName() |
      name.regexpMatch("byte|char|short|int|long")
    )
  }
}

/** A boolean type, which may be either a primitive or a boxed type. */
class BooleanType extends Type {
  BooleanType() {
    exists(string name |
      name = this.(PrimitiveType).getName() or name = this.(BoxedType).getPrimitiveType().getName() |
      name = "boolean"
    )
  }
}

/** A character type, which may be either a primitive or a boxed type. */
class CharacterType extends Type {
  CharacterType() {
    exists(string name |
      name = this.(PrimitiveType).getName() or name = this.(BoxedType).getPrimitiveType().getName() |
      name = "char"
    )
  }
}

/** A numeric or character type, which may be either a primitive or a boxed type. */
class NumericOrCharType extends Type {
  NumericOrCharType() {
    exists(string name |
      name = this.(PrimitiveType).getName() or name = this.(BoxedType).getPrimitiveType().getName() |
      name.regexpMatch("byte|char|short|int|long|double|float")
    )
  }
}

/** A floating point type, which may be either a primitive or a boxed type. */
class FloatingPointType extends Type {
  FloatingPointType() {
    exists(string name |
      name = this.(PrimitiveType).getName() or name = this.(BoxedType).getPrimitiveType().getName() |
      name.regexpMatch("float|double")
    )
  }
}
