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

import semmle.code.cpp.Element
import semmle.code.cpp.Member
import semmle.code.cpp.Function

/**
 * A C/C++ type.
 */
class Type extends Locatable, @type {

  /** the name of this element */
  string getName() {
    none()
  }

    /** whether this element has named name */
  predicate hasName(string name) { name = this.getName() }

  /**
   * Whether this declaration has the specifier `name`, recursively looking
   * through `typedef` and `decltype`. For example, in the context of
   * `typedef const int *restrict t`, the type `volatile t` has specifiers
   * `volatile` and `restrict` but not `const` since the `const` is attached to
   * the type being pointed to rather than the pointer itself.
   */
  // This predicate should not be overridden, but it cannot be declared `final`
  // because there is a similarly-named predicate in Declaration, and UserType
  // inherits from both Type and Declaration and must override it to resolve
  // the ambiguity.
  predicate hasSpecifier(string name) {
    this.getASpecifier().hasName(name)
  }

  /**
   * Get a specifier of this type, recursively looking through `typedef` and
   * `decltype`. For example, in the context of `typedef const int *restrict
   * t`, the type `volatile t` has specifiers `volatile` and `restrict` but not
   * `const` since the `const` is attached to the type being pointed to rather
   * than the pointer itself.
   */
  // This predicate should not be overridden, but it cannot be declared `final`
  // because there is a similarly-named predicate in Declaration, and UserType
  // inherits from both Type and Declaration and must override it to resolve
  // the ambiguity.
  Specifier getASpecifier() {
    typespecifiers(this,result)
    or
    result = this.internal_getAnAdditionalSpecifier()
  }

  /** an attribute of this type */
  Attribute getAnAttribute() { typeattributes(this,result) }

  /**
   * Internal -- should be `protected` when QL supports such a flag. Subtypes
   * override this to recursively get specifiers that are not attached directly
   * to this `@type` in the database but arise through type aliases such as
   * `typedef` and `decltype`.
   */
  Specifier internal_getAnAdditionalSpecifier() { none() }

  /** whether this type is const */
  predicate isConst() { this.hasSpecifier("const") }

  /** whether this type is volatile */
  predicate isVolatile() { this.hasSpecifier("volatile") }

  /** whether this type refers to type t -- by default,
    * a type always refers to itself. */
  predicate refersTo(Type t) { refersToDirectly*(t) }

  /** whether this type refers to type t directly */
  predicate refersToDirectly(Type t) { none() }

  /**
   * This type after typedefs have been resolved.
   *
   * The result of this predicate will be the type itself, except in the case of a TypedefType or a Decltype,
   * in which case the result will be type which results from (possibly recursively) resolving typedefs.
   */
  Type getUnderlyingType() { result = this }

  /**
   * This type after specifiers have been deeply stripped and typedefs have been resolved.
   *
   * For example, starting with `const i64* const` in the context of `typedef long long i64;`, this predicate will return `long long*`.
   */
  Type getUnspecifiedType() { unspecifiedtype(this, result) }

  /** the size of this type in bytes (on the machine where facts were extracted) */
  int getSize() {
       builtintypes(this,_,_,result,_)
    or pointerishsize(this, result)
    or usertypesize(this,result,_)
  }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = 0
  }

  /** Get a detailed string representation explaining the AST of this type
   *  (with all specifiers and nested constructs such as pointers). This is
   *  intended to help debug queries and is a very expensive operation; not
   *  to be used in production queries.
   *
   *  An example output is "const {pointer to {const {char}}}"
   */
  string explain() { result = "type" } // Concrete base impl to allow filters on Type

  /**
   * Test whether this type is constant and only contains constant types.
   * For instance, a "char *const" is a constant type, but not deeply constant,
   * because while the pointer can't be modified the character can. The type
   * "const char *const* is a deeply constant type though - both the pointer
   * and what it points to are immutable.
   */
  predicate isDeeplyConst() { this.isConst() and this.isDeeplyConstBelow() }

  /**
   * Like Type.isDeeplyConst(), but excludes the type itself. It is implied by
   * Type.isDeeplyConst() and is just used to implement that predicate.
   * For example, "const char *const" is deeply constant and deeply constant below,
   * but "const char *" is only deeply constant below (the pointer can be changed,
   * but not the underlying char). "char *const" is neither (it is just const).
   */
  predicate isDeeplyConstBelow() { none() } // Concrete base impl to allow filters on Type

  /**
   * Gets as many places as possible where this type is used by name in the source after macros have been replaced
   * (in particular, therefore, this will find type name uses caused by macros). Note that all type name uses within
   * instantiations are currently excluded - this is too draconian in the absence of indexing prototype instantiations
   * of functions, and is likely to improve in the future. At present, the method takes the conservative approach of
   * giving valid type name uses, but not necessarily *all* type name uses.
   */
  Element getATypeNameUse() {
    // An explicit cast to a type referring to T uses T. We exclude casts within instantiations,
    // since they do not appear directly in the source.
    exists(Cast c |
      not(c.isImplicit())
      and c.getType().refersTo(this)
      and result = c
      and not function_instantiation(c.getEnclosingFunction(),_)
    )

    // A class derivation from a type referring to T uses T. We exclude class derivations within
    // instantiations, since they do not appear directly in the source.
    or exists(ClassDerivation cd |
      cd.getBaseType().refersTo(this)
      and result = cd
      and not cd.getDerivedClass() instanceof ClassTemplateInstantiation
    )

    // A new, new array, or placement new expression with a type that refers to T uses T.
    // We exclude news within instantiations, since they do not appear directly in the source.
    or exists(Expr e |
      (
        e instanceof NewArrayExpr
        or e instanceof NewExpr
      )
      and e.getType().refersTo(this)
      and result = e
      and not function_instantiation(e.getEnclosingFunction(),_)
    )

    // The declaration of a function that returns a type referring to T uses T. We exclude
    // declarations of function template instantiations, since their return types do not
    // appear directly in the source. We also exclude constructors and destructors, since
    // they are indexed with a dummy return type of void that does not appear in the source.
    or exists(FunctionDeclarationEntry fde, Type t |
      (
        if exists(fde.getTypedefType()) then
          t = fde.getTypedefType()
        else
          t = fde.getType()
      )
      and t.refersTo(this)
      and result = fde
      and not function_instantiation(fde.getDeclaration(),_)
      and not(fde.getDeclaration() instanceof Constructor)
      and not(fde.getDeclaration() instanceof Destructor)
    )

    // A function call that provides an explicit template argument that refers to T uses T.
    // We exclude calls within instantiations, since they do not appear directly in the source.
    or exists(FunctionCall c |
      c.getAnExplicitTemplateArgument().refersTo(this)
      and result = c
      and not function_instantiation(c.getEnclosingFunction(),_)
    )

    // Qualifying an expression with a type that refers to T uses T. We exclude qualifiers
    // within instantiations, since they do not appear directly in the source.
    or exists(NameQualifier nq |
      ((Type)nq.getQualifyingElement()).refersTo(this)
      and result = nq
      and not function_instantiation(nq.getExpr().getEnclosingFunction(),_)
    )

    // Calculating the size of a type that refers to T uses T. We exclude sizeofs within
    // instantiations, since they do not appear directly in the source.
    or exists(SizeofTypeOperator soto |
      soto.getTypeOperand().refersTo(this)
      and result = soto
      and not function_instantiation(soto.getEnclosingFunction(),_)
    )

    // A typedef of a type that refers to T uses T.
    or exists(TypeDeclarationEntry tde |
      ((TypedefType)tde.getDeclaration()).getBaseType().refersTo(this)
      and result = tde
    )

    // Using something declared within a type that refers to T uses T.
    or exists(UsingDeclarationEntry ude |
      ude.getDeclaration().getDeclaringType().refersTo(this)
      and result = ude
    )

    // The declaration of a variable with a type that refers to T uses T. We exclude declarations within
    // instantiations, since those do not appear directly in the source.
    or exists(VariableDeclarationEntry vde |
      vde.getType().refersTo(this)
      and result = vde
      and not exists(LocalScopeVariable sv | sv = vde.getDeclaration() and function_instantiation(sv.getFunction(),_))
      and not exists(MemberVariable mv | mv = vde.getDeclaration() and mv.getDeclaringType() instanceof ClassTemplateInstantiation)
    )
  }

  /**
   * Recursively checks whether the specified type involves a reference.
   */
  predicate involvesReference() {
    none()
  }

  /**
   * Recursively checks whether the specified type involves a template parameter.
   */
  predicate involvesTemplateParameter() {
    none()
  }

  /**
   * Recursively resolves any typedefs in a type. For example, given typedef C T, this would resolve
   * const T&amp; to const C&amp;. Note that this will only work if the resolved type actually appears on its
   * own elsewhere in the program.
   */
  Type resolveTypedefs() {
    result = this
  }

  /**
   * Strips a type, removing pointers, references and cv-qualifiers, and resolving typedefs.
   * For example, given typedef const C&amp; T, stripType(T) = C.
   */
  Type stripType() {
    result = this
  }

  Location getLocation() {
    suppressUnusedThis(this) and
    result instanceof UnknownDefaultLocation
  }
}

/**
 * A C/C++ built-in primitive type (int, float, void, and so on). See 4.1.1.
 */
class BuiltInType extends Type, @builtintype {
  /** a printable representation of this named element */
  string toString() { result = this.getName() }

  /** the name of this built-in type */
  string getName() { builtintypes(this,result,_,_,_) }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = this.getName() }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { any() } // No subparts

}

/**
 * An erroneous type.
 */
class ErroneousType extends BuiltInType {

  ErroneousType() { builtintypes(this,_,1,_,_) }

}

/**
 * The unknown type.
 */
class UnknownType extends BuiltInType {

  UnknownType() { builtintypes(this,_,2,_,_) }

}

/**
 * The C/C++ arithmetic types. See 4.1.1.
 */
class ArithmeticType extends BuiltInType {

  ArithmeticType() {
    exists(int kind | builtintypes(this,_,kind,_,_) and kind >= 4)
  }

}

/**
 * The C/C++ integral types. See 4.1.1.
 */
class IntegralType extends ArithmeticType {

  IntegralType() {
    exists(int kind | builtintypes(this,_,kind,_,_) and
      (kind < 24 or kind = 33 or (35 <= kind and kind <= 37) or
       kind = 43 or kind = 44))
  }

  /** whether this integral type is unsigned */
  predicate isUnsigned() {
    builtintypes(this,_,_,_,1)
  }

  /** whether this integral type is signed */
  predicate isExplicitlySigned() {
    builtintypes(this,_,7,_,_) or builtintypes(this,_,10,_,_) or builtintypes(this,_,13,_,_) or
    builtintypes(this,_,16,_,_) or builtintypes(this,_,19,_,_) or
    builtintypes(this,_,37,_,_)
  }

  predicate isExplicitlyUnsigned() {
    builtintypes(this,_,6,_,_) or builtintypes(this,_,9,_,_) or builtintypes(this,_,12,_,_) or
    builtintypes(this,_,15,_,_) or builtintypes(this,_,18,_,_) or
    builtintypes(this,_,36,_,_)
  }

  /** whether this integral type is implicitly unsigned */
  predicate isImplicitlySigned() {
    builtintypes(this,_,5,_,-1) or builtintypes(this,_,8,_,-1) or builtintypes(this,_,11,_,-1) or
    builtintypes(this,_,14,_,-1) or builtintypes(this,_,17,_,-1) or
    builtintypes(this,_,35,_,-1)
  }

  predicate isSigned() {
    builtintypes(this,_,_,_,-1)
  }

  IntegralType getUnsigned() {
       (builtintypes(this,_, 5,_,_) or builtintypes(this,_, 6,_,_) or builtintypes(this,_, 7,_,_)) and builtintypes(result,_, 6,_,_)
    or (builtintypes(this,_, 8,_,_) or builtintypes(this,_, 9,_,_) or builtintypes(this,_,10,_,_)) and builtintypes(result,_, 9,_,_)
    or (builtintypes(this,_,11,_,_) or builtintypes(this,_,12,_,_) or builtintypes(this,_,13,_,_)) and builtintypes(result,_,12,_,_)
    or (builtintypes(this,_,14,_,_) or builtintypes(this,_,15,_,_) or builtintypes(this,_,16,_,_)) and builtintypes(result,_,15,_,_)
    or (builtintypes(this,_,17,_,_) or builtintypes(this,_,18,_,_) or builtintypes(this,_,19,_,_)) and builtintypes(result,_,18,_,_)
    or (builtintypes(this,_,35,_,_) or builtintypes(this,_,36,_,_) or builtintypes(this,_,37,_,_)) and builtintypes(result,_,36,_,_)
  }
}

/**
 * The C/C++ boolean type. See 4.2.
 */
class BoolType extends IntegralType {

  BoolType() { builtintypes(this,_,4,_,_) }

}

/**
 * The C/C++ character types. See 4.3.
 */
abstract class CharType extends IntegralType { }

/**
 * The C/C++ char type (which is different to signed char and unsigned char).
 */
class PlainCharType extends CharType {
  PlainCharType() {
    builtintypes(this,_,5,_,_)
  }
}

/**
 * The C/C++ unsigned char type (which is different to plain char, even when chars are unsigned by default).
 */
class UnsignedCharType extends CharType {
  UnsignedCharType() {
    builtintypes(this,_,6,_,_)
  }
}

/**
 * The C/C++ signed char type (which is different to plain char, even when chars are signed by default).
 */
class SignedCharType extends CharType {
  SignedCharType() {
    builtintypes(this,_,7,_,_)
  }
}

/**
 * The C/C++ short types. See 4.3.
 */
class ShortType extends IntegralType {

  ShortType() {
    builtintypes(this,_,8,_,_) or builtintypes(this,_,9,_,_) or builtintypes(this,_,10,_,_)
  }

}

/**
 * The C/C++ integer types. See 4.4.
 */
class IntType extends IntegralType {

  IntType() {
    builtintypes(this,_,11,_,_) or builtintypes(this,_,12,_,_) or builtintypes(this,_,13,_,_)
  }

}

/**
 * The C/C++ long types. See 4.4.
 */
class LongType extends IntegralType {

  LongType() {
    builtintypes(this,_,14,_,_) or builtintypes(this,_,15,_,_) or builtintypes(this,_,16,_,_)
  }

}

/**
 * The C/C++ long long types. See 4.4.
 */
class LongLongType extends IntegralType {

  LongLongType() {
    builtintypes(this,_,17,_,_) or builtintypes(this,_,18,_,_) or builtintypes(this,_,19,_,_)
  }

}

/**
 * The GNU C __int128 types.
 */
class Int128Type extends IntegralType {

  Int128Type() {
    builtintypes(this,_,35,_,_) or builtintypes(this,_,36,_,_) or builtintypes(this,_,37,_,_)
  }

}

/**
 * The C/C++ floating point types. See 4.5.
 */
class FloatingPointType extends ArithmeticType {

  FloatingPointType() {
    exists(int kind | builtintypes(this,_,kind,_,_) and ((kind >= 24 and kind <= 32) or (kind = 38)))
  }

}

/**
 * The C/C++ float type.
 */
class FloatType extends FloatingPointType {

  FloatType() { builtintypes(this,_,24,_,_) }

}

/**
 * The C/C++ double type.
 */
class DoubleType extends FloatingPointType {

  DoubleType() { builtintypes(this,_,25,_,_) }

}

/**
 * The C/C++ long double type.
 */
class LongDoubleType extends FloatingPointType {

  LongDoubleType() { builtintypes(this,_,26,_,_) }

}

/**
 * The GNU C __float128 type.
 */
class Float128Type extends FloatingPointType {

  Float128Type() { builtintypes(this,_,38,_,_) }

}

/**
 * The GNU C _Decimal32 type.
 */
class Decimal32Type extends FloatingPointType {

  Decimal32Type() { builtintypes(this,_,40,_,_) }

}

/**
 * The GNU C _Decimal64 type.
 */
class Decimal64Type extends FloatingPointType {

  Decimal64Type() { builtintypes(this,_,41,_,_) }

}

/**
 * The GNU C _Decimal128 type.
 */
class Decimal128Type extends FloatingPointType {

  Decimal128Type() { builtintypes(this,_,42,_,_) }

}

/**
 * The C/C++ void type. See 4.7.
 */
class VoidType extends BuiltInType {

  VoidType() { builtintypes(this,_,3,_,_) }

}

/**
 * The C/C++ wide character type.
 */
class WideCharType extends IntegralType {

  WideCharType() { builtintypes(this,_,33,_,_) }

}

/**
 * The C/C++ `char16_t` type.
 */
class Char16Type extends IntegralType {

  Char16Type() { builtintypes(this,_,43,_,_) }

}

/**
 * The C/C++ `char32_t` type.
 */
class Char32Type extends IntegralType {

  Char32Type() { builtintypes(this,_,44,_,_) }

}

/**
 * The type of the C++11 nullptr constant.
 *
 * Note that this is not nullptr_t, as nullptr_t is defined as:
 *  typedef decltype(nullptr) nullptr_t;
 * Instead, this is the unspeakable type given by decltype(nullptr).
 */
class NullPointerType extends BuiltInType {
  NullPointerType() { builtintypes(this,_,34,_,_) }
}

/**
 * A C/C++ derived type.
 *
 * These are pointer and reference types, array and vector types, and const and volatile types.
 * In all cases, the type is formed from a single base type.
 */
class DerivedType extends Type, @derivedtype {
  /** a printable representation of this named element */
  string toString() { result = this.getName() }

  /** the name of this type */
  string getName() { derivedtypes(this,result,_,_) }

  /**
   * The base type of this derived type.
   *
   * This predicate strips off one level of decoration from a type. For example, it returns `char*` for the PointerType `char**`,
   * `const int` for the ReferenceType `const int&amp;`, and `long` for the SpecifiedType `volatile long`.
   */
  Type getBaseType() { derivedtypes(this,_,_,result) }

  /** whether this type refers to type t directly */
  predicate refersToDirectly(Type t) { t = this.getBaseType() }

  /**
   * Recursively checks whether the specified type involves a reference.
   */
  predicate involvesReference() {
    getBaseType().involvesReference()
  }

  /**
   * Recursively checks whether the specified type involves a template parameter.
   */
  predicate involvesTemplateParameter() {
    getBaseType().involvesTemplateParameter()
  }

  /**
   * Strips a type, removing pointers, references and cv-qualifiers, and resolving typedefs.
   * For example, given typedef const C&amp; T, stripType(T) = C.
   */
  Type stripType() {
    result = getBaseType().stripType()
  }

  predicate isAutoReleasing() {
    this.hasSpecifier("__autoreleasing") or
    this.(PointerType).getBaseType().hasSpecifier("__autoreleasing")
  }

  predicate isStrong() {
    this.hasSpecifier("__strong") or
    this.(PointerType).getBaseType().hasSpecifier("__strong")
  }

  predicate isUnsafeRetained() {
    this.hasSpecifier("__unsafe_unretained") or
    this.(PointerType).getBaseType().hasSpecifier("__unsafe_unretained")
  }

  predicate isWeak() {
    this.hasSpecifier("__weak") or
    this.(PointerType).getBaseType().hasSpecifier("__weak")
  }
}

/**
 * An instance of the C++11 decltype operator.
 */
class Decltype extends Type, @decltype {

  /**
   * The expression whose type is being obtained by this decltype.
   */
  Expr getExpr() {
    decltypes(this, result, _, _)
  }

  /**
   * The type immediately yielded by this decltype.
   */
  Type getBaseType() {
    decltypes(this, _, result, _)
  }

  /**
   * Whether an extra pair of parentheses around the expression would change the semantics of this decltype.
   *
   * The following example shows the effect of an extra pair of parentheses:
   *   struct A { double x; };
   *   const A* a = new A();
   *   decltype( a->x ); // type is double
   *   decltype((a->x)); // type is const double&amp;
   * Consult the C++11 standard for more details.
   */
  predicate parenthesesWouldChangeMeaning() {
    decltypes(this, _, _, true)
  }

  /**
   * The type obtained after stepping through this decltype and any resulting decltypes or typedefs.
   */
  Type getUnderlyingType() {
    result = getBaseType().getUnderlyingType()
  }

  Type stripType() {
    result = getBaseType().stripType()
  }

  Type resolveTypedefs() {
    result = getBaseType().resolveTypedefs()
  }

  Location getLocation() {
    result = getExpr().getLocation()
  }

  string toString() {
    result = "decltype(...)"
  }

  string getName() {
    none()
  }

  int getSize() {
    result = getBaseType().getSize()
  }

  int getPointerIndirectionLevel() {
    result = getBaseType().getPointerIndirectionLevel()
  }

  string explain() {
    result = "decltype resulting in {" + this.getBaseType().explain() + "}"
  }

  predicate involvesReference() {
    getBaseType().involvesReference()
  }

  predicate involvesTemplateParameter() {
    getBaseType().involvesTemplateParameter()
  }

  predicate isDeeplyConst() {
    this.getBaseType().isDeeplyConst()
  }

  predicate isDeeplyConstBelow() {
    this.getBaseType().isDeeplyConstBelow()
  }

  override Specifier internal_getAnAdditionalSpecifier() {
    result = this.getBaseType().getASpecifier()
  }
}

/**
 * A C/C++ pointer type. See 4.9.1.
 */
class PointerType extends DerivedType {

  PointerType() { derivedtypes(this,_,1,_) }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = 1 + this.getBaseType().getPointerIndirectionLevel()
  }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = "pointer to {" + this.getBaseType().explain() + "}" }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConst() }

  /**
   * Recursively resolves any typedefs in a type. For example, given typedef C T, this would resolve
   * const T&amp; to const C&amp;. Note that this will only work if the resolved type actually appears on its
   * own elsewhere in the program.
   */
  Type resolveTypedefs() {
    result.(PointerType).getBaseType() = getBaseType().resolveTypedefs()
  }
}

/**
 * A C++ reference type. See 4.9.1.
 *
 * For C++11 code bases, this includes both lvalue references (&amp;) and rvalue references (&amp;&amp;).
 * To distinguish between them, use the LValueReferenceType and RValueReferenceType classes.
 */
class ReferenceType extends DerivedType {

  ReferenceType() { derivedtypes(this,_,2,_) or derivedtypes(this,_,8,_) }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = getBaseType().getPointerIndirectionLevel()
  }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = "reference to {" + this.getBaseType().explain() + "}" }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConst() { this.getBaseType().isDeeplyConst() } // No such thing as a const reference type

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConst() }

  /**
   * Recursively checks whether the specified type involves a reference.
   */
  predicate involvesReference() {
    any()
  }

  /**
   * Recursively resolves any typedefs in a type. For example, given typedef C T, this would resolve
   * const T&amp; to const C&amp;. Note that this will only work if the resolved type actually appears on its
   * own elsewhere in the program.
   */
  Type resolveTypedefs() {
    result.(ReferenceType).getBaseType() = getBaseType().resolveTypedefs()
  }
}

/**
 * A C++11 lvalue reference type (e.g. int&amp;).
 */
class LValueReferenceType extends ReferenceType {
  LValueReferenceType() { derivedtypes(this,_,2,_) }
}

/**
 * A C++11 rvalue reference type (e.g. int&amp;&amp;).
 */
class RValueReferenceType extends ReferenceType {
  RValueReferenceType() { derivedtypes(this,_,8,_) }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = "rvalue " + super.explain() }
}

/**
 * A type with specifiers.
 */
class SpecifiedType extends DerivedType {

  SpecifiedType() { derivedtypes(this,_,3,_) }

  int getSize() { result = this.getBaseType().getSize() }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = this.getBaseType().getPointerIndirectionLevel()
  }

  /** all the specifiers of this type as a string in a fixed order (the order
      only depends on the specifiers, not on the source program). This is intended
      for debugging queries only and is an expensive operation. */
  string getSpecifierString() {
    internalSpecString(this, result, 1)
  }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = this.getSpecifierString() + "{" + this.getBaseType().explain() + "}" }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConst() { this.getASpecifier().getName() = "const" and this.getBaseType().isDeeplyConstBelow() }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConstBelow() }

  override Specifier internal_getAnAdditionalSpecifier() {
    result = this.getBaseType().getASpecifier()
  }

  /**
   * Recursively resolves any typedefs in a type. For example, given typedef C T, this would resolve
   * const T&amp; to const C&amp;. Note that this will only work if the resolved type actually appears on its
   * own elsewhere in the program.
   */
  Type resolveTypedefs() {
    result.(SpecifiedType).getBaseType() = getBaseType().resolveTypedefs()
    and result.getASpecifier() = getASpecifier()
  }
}

/**
 * A C/C++ array type. See 4.9.1.
 */
class ArrayType extends DerivedType {

  ArrayType() { derivedtypes(this,_,4,_) }

  predicate hasArraySize() { arraysizes(this,_,_,_) }
  int getArraySize() { arraysizes(this,result,_,_) }

  int getByteSize() { arraysizes(this,_,result,_) }

  int getAlignment() { arraysizes(this,_,_,result) }

  /** the size of this array (only valid for arrays declared to be of a constant
      size, will fail for all others) */
  int getSize() {
    result = this.getByteSize()
  }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() {
    if exists(this.getArraySize()) then
      result = "array of " + this.getArraySize().toString() + " {" + this.getBaseType().explain() + "}"
    else
      result = "array of {" + this.getBaseType().explain() + "}"
  }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConst() { this.getBaseType().isDeeplyConst() } // No such thing as a const array type

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConst() }
}

/**
 * A GNU/Clang vector type.
 *
 * In both Clang and GNU compilers, vector types can be introduced using the
 * __attribute__((vector_size(byte_size))) syntax. The Clang compiler also
 * allows vector types to be introduced using the ext_vector_type,
 * neon_vector_type, and neon_polyvector_type attributes (all of which take
 * an element type rather than a byte size).
 */
class GNUVectorType extends DerivedType {

  GNUVectorType() { derivedtypes(this,_,5,_) }

  /**
   * Get the number of elements in this vector type.
   *
   * For vector types declared using Clang's ext_vector_type, neon_vector_type,
   * or neon_polyvector_type attribute, this is the value which appears within
   * the attribute. For vector types declared using the vector_size attribute,
   * the number of elements is the value in the attribute divided by the size
   * of a single element.
   */
  int getNumElements() { arraysizes(this,result,_,_) }

  /**
   * Get the size, in bytes, of this vector type.
   *
   * For vector types declared using the vector_size attribute, this is the
   * value which appears within the attribute. For vector types declared using
   * Clang's ext_vector_type, neon_vector_type, or neon_polyvector_type
   * attribute, the byte size is the value in the attribute multiplied by the
   * byte size of a single element.
   */
  int getSize() { arraysizes(this,_,result,_) }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = "GNU " + getNumElements() + " element vector of {" + this.getBaseType().explain() + "}" }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConst() }

}

/**
 * A C/C++ pointer to function. See 7.7.
 */
class FunctionPointerType extends FunctionPointerIshType {
  FunctionPointerType() {
    derivedtypes(this,_,6,_)
  }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = 1
  }

  /** Descriptive string for a type (debug - expensive). Overridden
      method. See Type.explain() */
  string explain() { result = "pointer to {" + ((RoutineType)this.getBaseType()).explain() + "}" }
}

/**
 * A C/C++ reference to function.
 */
class FunctionReferenceType extends FunctionPointerIshType {
  FunctionReferenceType() {
    derivedtypes(this,_,7,_)
  }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = getBaseType().getPointerIndirectionLevel()
  }

  /** Descriptive string for a type (debug - expensive). Overridden
      method. See Type.explain() */
  string explain() { result = "reference to {" + ((RoutineType)this.getBaseType()).explain() + "}" }
}

/**
 * A block type, for example int(^)(char, float).
 *
 * Block types (along with blocks themselves) are a language extension
 * supported by Clang, and by Apple's branch of GCC.
 */
class BlockType extends FunctionPointerIshType {
  BlockType() {
    derivedtypes(this,_,10,_)
  }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = 0
  }

  /** Descriptive string for a type (debug - expensive). Overridden
      method. See Type.explain() */
  string explain() { result = "block of {" + ((RoutineType)this.getBaseType()).explain() + "}" }
}

/**
 * A C/C++ pointer to function, or a block.
 */
class FunctionPointerIshType extends DerivedType {
  FunctionPointerIshType() {
    derivedtypes(this,_,6, _) or
    derivedtypes(this,_,7, _) or
    derivedtypes(this,_,10,_)
  }

  /** the return type of this function pointer type */
  Type getReturnType() {
    exists(@routinetype t | derivedtypes(this,_,_,t) and routinetypes(t, result))
  }

  /** the type of the ith argument of this function pointer type */
  Type getParameterType(int i) {
    exists(@routinetype t | derivedtypes(this,_,_,t) and routinetypeargs(t, i, result))
  }

  /** the type of an argument of this function pointer type */
  Type getAParameterType() {
    exists(@routinetype t | derivedtypes(this,_,_,t) and routinetypeargs(t, _, result))
  }

  /** the number of arguments of this function pointer type */
  int getNumberOfParameters() {
    result = count(int i | exists(this.getParameterType(i)))
  }

  /**
   * Recursively checks whether the specified type involves a template parameter.
   */
  predicate involvesTemplateParameter() {
    getReturnType().involvesTemplateParameter()
    or getAParameterType().involvesTemplateParameter()
  }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConst() }
}

/**
 * A C++ pointer to member. See 15.5.
 */
class PointerToMemberType extends Type, @ptrtomember {
  /** a printable representation of this named element */
  string toString() { result = this.getName() }

  /** the name of this type */
  string getName() { result = "..:: *" }

  /** the base type of this pointer to member type */
  Type getBaseType() { ptrtomembers(this,result,_) }

  /** the class referred by this pointer to member type */
  Type getClass() { ptrtomembers(this,_,result) }

  /** whether this type refers to type t directly */
  predicate refersToDirectly(Type t) {
    t = this.getBaseType() or
    t = this.getClass()
  }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = 1 + this.getBaseType().getPointerIndirectionLevel()
  }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result = "pointer to member of " + this.getClass().toString() + " with type {" + this.getBaseType().explain() + "}" }

  /**
   * Recursively checks whether the specified type involves a template parameter.
   */
  predicate involvesTemplateParameter() {
    getBaseType().involvesTemplateParameter()
  }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConst() }
}

/**
 * A C/C++ routine type. This is what results from stripping away the pointer from a function pointer type.
 */
class RoutineType extends Type, @routinetype {
  /** a printable representation of this named element */
  string toString() { result = this.getName() }

  string getName() { result = "..()(..)" }

  Type getParameterType(int n) { routinetypeargs(this,n,result) }

  Type getAParameterType() { routinetypeargs(this,_,result) }

  Type getReturnType() { routinetypes(this, result) }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() {
      result = "function returning {" + this.getReturnType().explain() +
          "} with arguments (" + this.explainParameters(0) + ")"
  }

  /** Get a string with the explain() values for the parameters of
   * this function, for instance "int,int". Internal only: use explain().
   *
   * The integer argument is the index of the first parameter to explain.
   */
  string explainParameters(int i) {
    (i = 0 and result = "" and not exists(this.getAParameterType()))
    or
    (
      exists(this.getParameterType(i)) and
      if i < max(int j | exists(this.getParameterType(j))) then
        // Not the last one
        result = this.getParameterType(i).explain() + "," + this.explainParameters(i+1)
      else
        // Last parameter
        result = this.getParameterType(i).explain()
    )
  }

  /** whether this type refers to type t directly */
  predicate refersToDirectly(Type t) {
    t = this.getReturnType() or
    t = this.getAParameterType()
  }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConst() { none() } // Current limitation: no such thing as a const routine type

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { none() } // Current limitation: no such thing as a const routine type

  /**
   * Recursively checks whether the specified type involves a template parameter.
   */
  predicate involvesTemplateParameter() {
    getReturnType().involvesTemplateParameter()
    or getAParameterType().involvesTemplateParameter()
  }
}

/**
 * A C++ typename template parameter.
 */
class TemplateParameter extends UserType
{
  TemplateParameter() { usertypes(this, _, 7) or usertypes(this, _, 8) }

  string getName() { usertypes(this, result, _) }

  /**
   * Recursively checks whether the specified type involves a template parameter.
   */
  predicate involvesTemplateParameter() {
    any()
  }
}

/** A C++ template template parameter, e.g. template &lt;template &lt;typename,typename> class T>. */
class TemplateTemplateParameter extends TemplateParameter
{
  TemplateTemplateParameter() {
    usertypes(this, _, 8)
  }
}

/**
 * A type representing the use of the C++11 auto keyword.
 */
class AutoType extends TemplateParameter
{
  AutoType() { usertypes(this, "auto", 7) }

  Location getLocation() {
    suppressUnusedThis(this) and
    result instanceof UnknownDefaultLocation
  }
}

//
// Internal implementation predicates
//

predicate allSpecifiers(int i, string s) {
  s = rank[i](string t | specifiers(_, t) | t)
}

predicate internalSpecString(Type t, string res, int i) {
     (if allSpecifiers(i, t.getASpecifier().getName())
      then exists(string spec, string rest
                | allSpecifiers(i, spec) and res = spec + " " + rest
              and internalSpecString(t, rest, i+1))
      else (allSpecifiers(i, _) and internalSpecString(t, res, i+1)))
  or (i = count(Specifier s) + 1 and res = "")
}

private predicate suppressUnusedThis(Type t) { any() }
