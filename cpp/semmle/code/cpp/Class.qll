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

import semmle.code.cpp.Type
import semmle.code.cpp.UserType
import semmle.code.cpp.metrics.MetricClass
import semmle.code.cpp.Linkage

/**
 * A class type [N4140 9].
 *
 * While this does include types declared with the `class` keyword, it also
 * includes types declared with the `struct` and `union` keywords.
 */
class Class extends UserType {

  Class() {
    usertypes(this,_,1) or usertypes(this,_,2) or usertypes(this,_,3) or usertypes(this,_,6)
    or usertypes(this,_,10) or usertypes(this,_,11) or usertypes(this,_,12)
  }

  /** Gets a child declaration of this class. */
  Declaration getADeclaration() { result.getDeclaringType() = this }

  /** Gets a type declared in this class. */
  UserType getANestedType() { result.getDeclaringType() = this }

  /** Gets a function declared in this class. */
  MemberFunction getAMemberFunction() { result.getDeclaringType() = this }

  /** Gets a member variable declared in this class. */
  MemberVariable getAMemberVariable() { result.getDeclaringType() = this }

  /** Gets a member declared in this class. */
  Declaration getAMember() { result.getDeclaringType() = this }
  Declaration getMember(int index) { member(this,index,result) }
  int getNumMember() { result = count(this.getAMember()) }

  /** Gets a private member declared in this class. */
  Declaration getAPrivateMember() {
    result = this.getAMember() and result.hasSpecifier("private")
  }

  /** Gets a protected member declared in this class. */
  Declaration getAProtectedMember() {
    result = this.getAMember() and result.hasSpecifier("protected")
  }

  /** Gets a public member declared in this class. */
  Declaration getAPublicMember() {
    result = this.getAMember() and result.hasSpecifier("public")
  }

  /** Gets a static member declared in this class. */
  Declaration getAStaticMember() {
    result = this.getAMember() and result.isStatic()
  }

  /** Gets a field of this class. */
  Field getAField() { result = this.getAMemberVariable() }

  /** Gets a constructor of this class. */
  Constructor getAConstructor() { result = this.getAMemberFunction() }

  /** Holds if this class has a constructor. */
  predicate hasConstructor() { exists(this.getAConstructor()) }

  /**
   * Holds if this class has a copy constructor that is either explicitly
   * declared (though possibly `= delete`) or is auto-generated, non-trivial
   * and called from somewhere.
   *
   * DEPRECATED: There is more than one reasonable definition of what it means
   * to have a copy constructor, and we do not want to promote one particular
   * definition by naming it with this predicate. Having a copy constructor
   * could mean that such a member is declared or defined in the source or that
   * it is callable by a particular caller. For C++11, there's also a question
   * of whether to include members that are defaulted or deleted.
   */
  deprecated predicate hasCopyConstructor() {
    exists(CopyConstructor cc | cc = this.getAMemberFunction())
  }

  /**
   * Holds if this class has a copy assignment operator that is either
   * explicitly declared (though possibly `= delete`) or is auto-generated,
   * non-trivial and called from somewhere.
   *
   * DEPRECATED: There is more than one reasonable definition of what it means
   * to have a copy assignment operator, and we do not want to promote one
   * particular definition by naming it with this predicate. Having a copy
   * assignment operator could mean that such a member is declared or defined
   * in the source or that it is callable by a particular caller. For C++11,
   * there's also a question of whether to include members that are defaulted
   * or deleted.
   */
  deprecated predicate hasCopyAssignmentOperator() {
    exists(CopyAssignmentOperator coa | coa = this.getAMemberFunction())
  }

  /**
   * Like accessOfBaseMember but returns multiple results if there are multiple
   * paths to `base` through the inheritance graph.
   */
  private AccessSpecifier accessOfBaseMemberMulti(Class base,
                                                  AccessSpecifier fieldInBase)
  {
    (this = base and result = fieldInBase)
    or
    exists(ClassDerivation cd | cd.getBaseClass() = base |
      result = this.accessOfBaseMemberMulti(
        cd.getDerivedClass(),
        fieldInBase.accessInDirectDerived(cd.getASpecifier().(AccessSpecifier))
      )
    )
  }

  /**
   * Gets the access specifier, if any, that a hypothetical member of `base`
   * would have when viewed as a member of `this`, given that this member had
   * access specifier `fieldInBase`. Encodes the rules of C++14 11.2/1 and
   * 11.6/1, except that this predicate includes the case of `base` = `this`.
   */
  AccessSpecifier accessOfBaseMember(Class base, AccessSpecifier fieldInBase) {
    // If there are multiple paths through the inheritance graph, we take the
    // most permissive one (C++14 11.6/1). This implementation relies on the
    // alphabetical order of "private", "protected", "public".
    result.hasName(
      max(this.accessOfBaseMemberMulti(base, fieldInBase).getName())
    )
  }

  /**
   * Gets the access specifier, if any, that `member` has when viewed as a
   * member of `this`, where `member` may come from a base class of `this`.
   * Encodes the rules of C++14 11.2/1 and 11.6/1, except that this predicate
   * includes the case of `base` = `this`.
   */
  AccessSpecifier accessOfBaseMember(Declaration member) {
    result = this.accessOfBaseMember(
      member.getDeclaringType(),
      member.getASpecifier().(AccessSpecifier)
    )
  }

  /**
   * DEPRECATED: name changed from `hasImplicitCopyConstructor` to reflect that
   * `= default` members are no longer included.
   */
  deprecated predicate hasGeneratedCopyConstructor() {
    hasImplicitCopyConstructor()
  }

  /**
   * DEPRECATED: name changed from `hasImplicitCopyAssignmentOperator` to
   * reflect that `= default` members are no longer included.
   */
  deprecated predicate hasGeneratedCopyAssignmentOperator() {
    hasImplicitCopyConstructor()
  }

  /**
   * Holds if this class has an implicitly-declared copy constructor that is
   * not _deleted_. This predicate is more accurate than checking
   * if this class has a `CopyConstructor cc` where `cc.isCompilerGenerated()`
   * since such a `CopyConstructor` may not exist in the database if (1) it is
   * never called or (2) it is _trivial_, meaning that it is equivalent to
   * `memcpy`.
   */
  predicate hasImplicitCopyConstructor() {
    not this.implicitCopyConstructorDeleted() and
    forall(CopyConstructor cc | cc = this.getAMemberFunction() |
      cc.isCompilerGenerated()
    )
  }

  /**
   * Holds if this class has an implicitly-declared copy assignment operator
   * that is not _deleted_. This predicate is more accurate than checking
   * if this class has a `CopyAssignmentOperator ca` where
   * `ca.isCompilerGenerated()` since such a `CopyAssignmentOperator` may not
   * exist in the database if (1) it is never called or (2) it is _trivial_,
   * meaning that it is equivalent to `memcpy`.
   */
  predicate hasImplicitCopyAssignmentOperator() {
    not this.implicitCopyAssignmentOperatorDeleted() and
    forall(CopyAssignmentOperator ca | ca = this.getAMemberFunction() |
      ca.isCompilerGenerated()
    )
  }

  /**
   * Holds if the compiler would be unable to generate a copy constructor for
   * this class. This predicate implements the rules listed here:
   * http://en.cppreference.com/w/cpp/language/copy_constructor#Deleted_implicitly-declared_copy_constructor
   */
  predicate implicitCopyConstructorDeleted() {
    // - T has non-static data members that cannot be copied (have deleted,
    //   inaccessible, or ambiguous copy constructors);
    exists(Type t | t = this.getAFieldSubobjectType().getUnspecifiedType() |
        // Note: Overload resolution is not implemented -- all copy
        // constructors are considered equal.
        this.cannotAccessCopyConstructorOnAny(t.(Class))
    )
    or
    // - T has direct or virtual base class that cannot be copied (has deleted,
    //   inaccessible, or ambiguous copy constructors);
    exists(Class c | c = this.getADirectOrVirtualBase() |
        // Note: Overload resolution is not implemented -- all copy
        // constructors are considered equal.
        this.cannotAccessCopyConstructorOnThis(c)
    )
    or
    // - T has direct or virtual base class with a deleted or inaccessible
    //   destructor;
    exists(Class base | base = this.getADirectOrVirtualBase() |
      this.cannotAccessDestructor(base, this)
    )
    or
    // - T has a user-defined move constructor or move assignment operator;
    exists(MoveConstructor mc | mc = this.getAMemberFunction() |
        not mc.isCompilerGenerated())
    or
    exists(MoveAssignmentOperator ma | ma = this.getAMemberFunction() |
        not ma.isCompilerGenerated())
    or
    // - T is a union and has a variant member with non-trivial copy
    //   constructor (since C++11)
    none() // Not implemented
    or
    // - T has a data member of rvalue reference type.
    exists (Type t | t = this.getAFieldSubobjectType() |
        t instanceof RValueReferenceType
    )
  }

  /**
   * Holds if the compiler would be unable to generate a copy assignment
   * operator for this class. This predicate implements the rules listed here:
   * http://en.cppreference.com/w/cpp/language/copy_assignment#Deleted_implicitly-declared_copy_assignment_operator
   */
  predicate implicitCopyAssignmentOperatorDeleted() {
    // - T has a user-declared move constructor;
    exists(MoveConstructor mc | mc = this.getAMemberFunction() |
        not mc.isCompilerGenerated())
    or
    // - T has a user-declared move assignment operator.
    exists(MoveAssignmentOperator ma | ma = this.getAMemberFunction() |
        not ma.isCompilerGenerated())
    or

    // - T has a non-static data member of non-class type (or array thereof)
    //   that is const;
    exists(Type t | t = this.getAFieldSubobjectType() |
        // The rule for this case refers only to non-class types only, but our
        // implementation extends it to cover class types too. Class types are
        // supposed to be covered by the rule below on data members that
        // cannot be copy-assigned. Copy-assigning a const class-typed member
        // would call an overload of type
        // `const C& operator=(const C&) const;`. Such an overload is unlikely
        // to exist because it contradicts the intention of "const": it allows
        // assigning to a const object. But since we have not implemented the
        // ability to distinguish between overloads, we cannot distinguish that
        // overload from the ordinary `C& operator=(const C&);`. Instead, we
        // require class types to be non-const in this clause.
        /* not t instanceof Class and */ t.isConst()
    )
    or
    // - T has a non-static data member of a reference type;
    exists (Type t | t = this.getAFieldSubobjectType() |
        t instanceof ReferenceType
    )
    or
    // - T has a non-static data member or a direct or virtual base class that
    //   cannot be copy-assigned (overload resolution for the copy assignment
    //   fails, or selects a deleted or inaccessible function);
    exists(Type t | t = this.getAFieldSubobjectType().getUnspecifiedType() |
        // Note: Overload resolution is not implemented -- all copy assignment
        // operators are considered equal.
        this.cannotAccessCopyAssignmentOperatorOnAny(t.(Class))
    )
    or
    exists(Class c | c = this.getADirectOrVirtualBase() |
        // Note: Overload resolution is not implemented -- all copy assignment
        // operators are considered equal.
        this.cannotAccessCopyAssignmentOperatorOnThis(c)
    )
    // - T is a union-like class, and has a variant member whose corresponding
    //   assignment operator is non-trivial.
    // Not implemented
  }

  /** Gets the destructor of this class, if any. */
  Destructor getDestructor() { result = this.getAMemberFunction() }

  /** Holds if this class has a destructor. */
  predicate hasDestructor() { exists(this.getDestructor()) }

  /**
   * Holds if this class is a POD (Plain Old Data) class [N4140 9(10)].
   *
   * The definition of POD changed between C++03 and C++11, so whether
   * a class is POD can depend on which version of the language it was
   * compiled for. For this reason, the `is_pod_class` predicate is
   * generated by the extractor.
   */
  predicate isPOD() { is_pod_class(this) }

  /**
   * Holds if this class is abstract, in other words whether it declares one
   * or more pure virtual member functions.
   */
  predicate isAbstract() { this.getAMemberFunction() instanceof PureVirtualFunction }

  /** Gets a direct base class of this class [N4140 10]. */
  Class getABaseClass() { this.getADerivation().getBaseClass() = result }

  /** Gets a class that is directly derived from this class [N4140 10]. */
  Class getADerivedClass() { result.getABaseClass() = this }

  /** Holds if this class derives directly from that. */
  predicate derivesFrom(Class that) {
    this.getABaseClass() = that
  }

  /** Holds if this type refers to type `t` directly */
  predicate refersToDirectly(Type t) {
    t = this.getATemplateArgument() or
    class_instantiation(this, t)
  }

  /**
   * Gets a class derivation of this class, for example the "public B"
   * in "class D : public B { ... };".
   */
  ClassDerivation getADerivation() {
    exists(ClassDerivation d | d.getDerivedClass() = this and d = result)
  }
  ClassDerivation getDerivation(int index) {
    exists(ClassDerivation d
    | d.getDerivedClass() = this and d.getIndex() = index and d = result)
  }

  /**
   * Holds if this class has a virtual class derivation, for example the
   * "virtual public B" in "class D : virtual public B { ... };".
   */
  predicate hasVirtualBaseClass(Class base) {
      exists(ClassDerivation cd |
              this.getADerivation() = cd and
              cd.getBaseClass() = base and
              cd.hasSpecifier("virtual")
      )
  }

  /**
   * Holds if this class has a private class derivation, for example the
   * "private B" in "class D : private B { ... };".
   */
  predicate hasPrivateBaseClass(Class base) {
      exists(ClassDerivation cd |
              this.getADerivation() = cd and
              cd.getBaseClass() = base and
              cd.hasSpecifier("private")
      )
  }

  /**
   * Holds if this class has a public class derivation, for example the
   * "public B" in "class D : public B { ... };".
   */
  predicate hasPublicBaseClass(Class base) {
      exists(ClassDerivation cd |
              this.getADerivation() = cd and
              cd.getBaseClass() = base and
              cd.hasSpecifier("public")
      )
  }

  /**
   * Holds if this class has a protected class derivation, for example the
   * "protected B" in "class D : protected B { ... };".
   */
  predicate hasProtectedBaseClass(Class base) {
      exists(ClassDerivation cd |
              this.getADerivation() = cd and
              cd.getBaseClass() = base and
              cd.hasSpecifier("protected")
      )
  }

  /** Gets the metric class. */
  MetricClass getMetrics() { result = this }

  /** Gets a friend declaration in this class. */
  FriendDecl getAFriendDecl() { result.getDeclaringClass() = this }

  /**
   * Descriptive string for a type (debug - expensive). Overridden
   * method. See `Type.explain()`.
   */
  string explain() { result = "class " + this.getName() }

  /** See `Type.isDeeplyConst()` and `Type.isDeeplyConstBelow()`. Internal. */
  predicate isDeeplyConstBelow() { any() } // No subparts

  /**
   * The alignment of this type in bytes (on the machine where facts were
   * extracted).
   */
  int getAlignment() { usertypesize(this,_,result) }

  /**
   * Holds if this class is constructed from another class as a result of
   * template instantiation. It originates either from a class template or
   * from a class nested in a class template.
   */
  predicate isConstructedFrom(Class c) {
    class_instantiation(this, c)
  }

  /**
   * Gets a template argument used to instantiate this class from a class
   * template. When called on a class template, this will return a template
   * parameter.
   */
  Type getATemplateArgument() {
    exists(int i | this.getTemplateArgument(i) = result )
  }

  /** Gets the number of template arguments for this class. */
  int getNumberOfTemplateArguments() {
    result = count(int i | exists(getTemplateArgument(i)))
  }

  /**
   * Gets the `i`th template argument used to instantiate this class from a
   * class template. When called on a class template, this will return the
   * `i`th template parameter.
   */
  Type getTemplateArgument(int i) {
    class_template_argument(this,i,result)
  }

  /**
   * Holds if or not this class is polymorphic (has a virtual function, or
   * inherits one).
   */
  predicate isPolymorphic() {
    exists(MemberFunction f | f.getDeclaringType() = getABaseClass*() and f.isVirtual())
  }

  /** Holds if this class involves a template parameter. */
  predicate involvesTemplateParameter() {
    getATemplateArgument().involvesTemplateParameter()
  }

  /** Holds if this class was declared 'final'. */
  predicate isFinal() {
    usertype_final(this)
  }

  /** Gets a link target which references this class. */
  LinkTarget getALinkTarget() {
    this = result.getAClass()
  }

  private Type getAFieldSubobjectType() {
    exists(Type t | t = this.getAField().getUnderlyingType() |
      result = stripArrayTypes(t)
    )
  }

  private Class getADirectOrVirtualBase() {
    // `result` is a direct base of `this`
    result.getADerivedClass() = this
    or
    // `result` is an indirect virtual base of `this`. The case where `result`
    // is a direct virtual base of `this` is included in the above clause, and
    // therefore we can use "+"-closure instead of "*"-closure here.
    result.(VirtualBaseClass)
          .getAVirtuallyDerivedClass()
          .getADerivedClass+() = this
  }

  /**
   * Holds if `this` can NOT access the destructor of class `c` on an object of
   * type `objectClass`. Note: this implementation is incomplete but will be
   * correct in most cases; it errs on the side of claiming that the destructor
   * is accessible.
   */
  pragma[inline]
  private predicate cannotAccessDestructor(Class c, Class objectClass) {
    // The destructor in our db, if any, is accessible. If there is no
    // destructor in our db, it usually means that there is a default
    // public one.
    exists(Destructor d | d = c.getAMemberFunction() |
                          not this.canAccessMember(d, objectClass))

    // The extractor doesn't seem to support the case of a deleted destructor,
    // so we ignore that. It is very much a corner case.

    // To implement this properly, there should be a predicate about whether
    // the implicit destructor is deleted, similar to
    // `implicitCopyConstructorDeleted`. See
    // http://en.cppreference.com/w/cpp/language/destructor#Deleted_implicitly-declared_destructor
  }

  private predicate cannotAccessCopyConstructorOnThis(Class c) {
    this.cannotAccessCopyConstructor(c, this)
  }

  private predicate cannotAccessCopyConstructorOnAny(Class c) {
    this.cannotAccessCopyConstructor(c, c)
  }

  /**
   * Holds if `this` can NOT access the copy constructor of class `c` in order
   * to construct an object of class `objectClass`. In practice, set
   * `objectClass` to `this` when access-checking a base subobject
   * initialization (like `class D : C { D(D& that) : C(that) { ... } }`). Set
   * `objectClass` to `c` for any other purpose (like `C y = x;`).
   */
  pragma[inline]
  private predicate cannotAccessCopyConstructor(Class c, Class objectClass) {
    // Pseudocode:
    //   if c has CopyConstructor cc
    //   then this.cannotAccess(cc)
    //   else this.implicitCopyConstructorDeleted()
    exists(CopyConstructor cc | cc = c.getAMemberFunction() |
           not this.canAccessMember(cc, objectClass))
    or
    (
      not exists(CopyConstructor cc | cc = c.getAMemberFunction()) and
      c.implicitCopyConstructorDeleted() // mutual recursion here
      // no access check in this case since the implicit member is always
      // public.
    )
  }

  private predicate cannotAccessCopyAssignmentOperatorOnThis(Class c) {
    this.cannotAccessCopyAssignmentOperator(c, this)
  }

  private predicate cannotAccessCopyAssignmentOperatorOnAny(Class c) {
    this.cannotAccessCopyAssignmentOperator(c, c)
  }

  /**
   * Holds if `this` can NOT access the copy assignment operator of class `c` on
   * an object of type `objectClass`, where `objectClass` is derived from or
   * equal to `c`. That is, whether the call `x.C::operator=(...)` is forbidden
   * when the type of `x` is `objectClass`, and `c` has the name `C`.
   */
  pragma[inline]
  private predicate cannotAccessCopyAssignmentOperator(Class c, Class objectClass) {
    // Pseudocode:
    //   if c has CopyAssignmentOperator ca
    //   then this.cannotAccess(ca)
    //   else this.implicitCopyAssignmentOperatorDeleted()
    exists(CopyAssignmentOperator ca | ca = c.getAMemberFunction() |
           not this.canAccessMember(ca, objectClass))
    or
    (
      not exists(CopyAssignmentOperator ca | ca = c.getAMemberFunction()) and
      c.implicitCopyAssignmentOperatorDeleted() // mutual recursion here
      // no access check in this case since the implicit member is always
      // public.
    )
  }
}

/**
 * A class derivation, for example the "public B" in
 * "class D : public B { ... };".
 */
class ClassDerivation extends Locatable,  @derivation {
  /**
   * Gets the class/struct from which we are actually deriving, resolving a
   * typedef if necessary.  For example, the base class in the following
   * would be B:
   *
   * struct B {};
   * typedef B T;
   * struct D : T {};
   */
  Class getBaseClass() {
    result = getBaseType().getUnderlyingType()
  }

  /**
   * Gets the type from which we are deriving, without resolving any
   * typedef. For example, the base type in the following would be T:
   *
   * struct B {};
   * typedef B T;
   * struct D : T {};
   */
  Type getBaseType() {
    derivations(this,_,_,result,_)
  }

  /**
   * Gets the class that is doing the deriving. For example, the derived
   * class in the following would be D:
   *
   * struct B {};
   * struct D : B {};
   */
  Class getDerivedClass() {
    derivations(this,result,_,_,_)
  }

  /**
   * Gets the index of the derivation in the derivation list for the
   * derived class (indexed from 0).  For example, the index of the
   * derivation of B2 in "struct D : B1, B2 { ... };" would be 1.
   */
  int getIndex() {
    derivations(this,_,result,_,_)
  }

  /** Gets a specifier (for example "public") applied to the derivation. */
  Specifier getASpecifier() {
    derspecifiers(this,result)
  }

  /** Holds if the derivation has specifier `s`. */
  predicate hasSpecifier(string s) {
    this.getASpecifier().hasName(s)
  }

  /** Gets the location of the derivation. */
  override Location getLocation() {
    derivations(this,_,_,_,result)
  }

  override string toString() {
    result = "derivation"
  }
}

/** A class that is directly enclosed by a function. */
class LocalClass extends Class {
  LocalClass() {
    isLocal()
  }

  override Function getEnclosingAccessHolder() {
    result = this.getEnclosingFunction()
  }
}

/**
 * A nested class [4140 9.7].
 */
class NestedClass extends Class {
  NestedClass() { member(_,_,this) }

  /** Holds if this member is private. */
  predicate isPrivate() { this.hasSpecifier("private") }

  /** Holds if this member is public. */
  predicate isProtected() { this.hasSpecifier("protected") }

  /** Holds if this member is public. */
  predicate isPublic() { this.hasSpecifier("public") }

}

/**
 * An "abstract class", in other words a class that contains at least one
 * pure virtual function.
 */
class AbstractClass extends Class {
  AbstractClass() {
    exists(PureVirtualFunction f| this.getAMemberFunction() = f)
  }
}

/**
 * A class template. (This class also finds partial specializations
 * of class templates).
 */
class TemplateClass extends Class {
  TemplateClass() { usertypes(this,_,6) }
  Class getAnInstantiation() { class_instantiation(result,this) }
}

/**
 * A class that is an instantiation of a template.
 */
class ClassTemplateInstantiation extends Class {
  ClassTemplateInstantiation() {
    exists(TemplateClass tc | tc.getAnInstantiation() = this)
  }
}

/**
 * A specialization of a class template.
 */
abstract class ClassTemplateSpecialization extends Class {
  /**
   * Gets the primary template for the specialization, for example
   * S&lt;T,int> -> S&lt;T,U>.
   */
  TemplateClass getPrimaryTemplate() {
    // Ignoring template arguments, the primary template has the same name
    // as each of its specializations.
    result.getSimpleName() = getSimpleName()

    // It is in the same namespace as its specializations.
    and result.getNamespace() = getNamespace()

    // It is distinguished by the fact that each of its template arguments
    // is a distinct template parameter.
    and count(TemplateParameter tp | tp = result.getATemplateArgument()) =
        count(int i | exists(result.getTemplateArgument(i)))
  }
}

/**
 * A full specialization of a class template.
 */
class FullClassTemplateSpecialization extends ClassTemplateSpecialization {
  FullClassTemplateSpecialization() {
    // This class has template arguments, but none of them involves a template parameter.
    exists(getATemplateArgument())
    and not exists(Type ta | ta = getATemplateArgument() and ta.involvesTemplateParameter())

    // This class does not have any instantiations.
    and not exists(this.(TemplateClass).getAnInstantiation())

    // This class is not an instantiation of a class template.
    and not this instanceof ClassTemplateInstantiation
  }
}

/**
 * A partial specialization of a class template.
 */
class PartialClassTemplateSpecialization extends ClassTemplateSpecialization {
  PartialClassTemplateSpecialization() {
    /*
     * (a) At least one of this class's template arguments involves a
     *     template parameter in some respect, for example T, T*, etc.
     *
     * (b) It is not the case that the n template arguments of this class
     *     are a set of n distinct template parameters.
     *
     * template <typename T,U> class X {};      // class template
     * template <typename T> class X<T,T> {};   // partial class template specialization
     * template <typename T> class X<T,int> {}; // partial class template specialization
     * template <typename T> class Y {};        // class template
     * template <typename T> class Y<T*> {};    // partial class template specialization
     */
    exists(Type ta | ta = getATemplateArgument() and ta.involvesTemplateParameter())
    and count(TemplateParameter tp | tp = getATemplateArgument()) !=
        count(int i | exists(getTemplateArgument(i)))
  }
}

/**
 * An "interface", in other words a class that only contains pure virtual
 * functions.
 */
class Interface extends Class {
  Interface() {
    forex(Declaration m | m.getDeclaringType() = this.getABaseClass*() and not compgenerated(m) | m instanceof PureVirtualFunction)
  }
}

/**
 * A class derivation that is virtual, for example
 * "class X : --> virtual public Y &lt;--."
 */
class VirtualClassDerivation extends ClassDerivation {
  VirtualClassDerivation() {
    hasSpecifier("virtual")
  }
}

/**
 * A class that is the base of some virtual class derivation.
 */
class VirtualBaseClass extends Class {
  VirtualBaseClass() {
    exists(VirtualClassDerivation cd | cd.getBaseClass() = this)
  }

  /** A virtual class derivation of which this class is the base. */
  VirtualClassDerivation getAVirtualDerivation() {
    result.getBaseClass() = this
  }

  /** A class that is derived from this one using virtual inheritance. */
  Class getAVirtuallyDerivedClass() {
    result = getAVirtualDerivation().getDerivedClass()
  }
}

/**
 * The proxy class (where needed) associated with a template parameter, as
 * in the following code:
 *
 * template &lt;typename T>
 * struct S : T // the type of this T is a proxy class
 * {};
 */
class ProxyClass extends UserType {
  ProxyClass() {
    usertypes(this,_,9)
  }

  /** Gets the location of the proxy class. */
  override Location getLocation() {
    result = getTemplateParameter().getDefinitionLocation()
  }

  /** Gets the template parameter for which this is the proxy class. */
  TemplateParameter getTemplateParameter() {
    is_proxy_class_for(this,result)
  }
}

// Unpacks "array of ... of array of t" into t.
private Type stripArrayTypes(Type t) {
  not t instanceof ArrayType and result = t or
  result = stripArrayTypes(t.(ArrayType).getBaseType())
}
