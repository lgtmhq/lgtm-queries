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
 * A library for working with members of Java classes and interfaces,
 * that is, methods, constructors, fields and nested types.
 */

import Element
import Type
import Annotation
import Exception
import metrics.MetricField

/**
 * A common abstraction for type member declarations,
 * including methods, constructors, fields, and nested types.
 */
class Member extends Element, Annotatable, Modifiable, @member {
  Member() {
    declaresMember(_,this)
  }

  /** The type in which this member is declared. */
  RefType getDeclaringType() { declaresMember(result, this) }

  /** The qualified name of this member. */
  string getQualifiedName() {
    result = getDeclaringType().getName() + "." + getName()
  }

  /** Whether this member is package protected, that is, neither public nor private nor protected. */
  predicate isPackageProtected() {
    not isPrivate() and
    not isProtected() and
    not isPublic()
  }
}

/** A callable is a method or constructor. */
class Callable extends StmtParent, Member, @callable {
  /** A printable representation of this callable. */
  string toString() { result = Member.super.toString() }
  
  /**
   * The declared return type of this callable (`void` for
   * constructors).
   */
  Type getType() {
    constrs(this, _, _, result, _, _) or
    methods(this, _, _, result, _, _)
  }

  /**
   * A callee that may be called from this callable.
   *
   * DEPRECATED: use `getACallee` instead.
   */
  deprecated Callable getACall() { result = getACallee() }

  /**
   * A callee that may be called from this callable.
   */
  Callable getACallee() { this.calls(result) }

  /** The call site of a call from this callable to a callee. */
  Call getACallSite(Callable callee) {
    result.getCaller() = this and
    result.getCallee() = callee
  }
  
  /**
   * The bytecode method descriptor, encoding parameter and return types,
   * but not the name of the callable.
   */
  string getMethodDescriptor() {
    exists(string return | return = this.getType().getTypeDescriptor() |
      result = "(" + descriptorUpTo(this.getNumberOfParameters()) + ")" + return
    )
  }
  
  private string descriptorUpTo(int n) {
    (n = 0 and result = "") or
    exists(Parameter p | p = this.getParameter(n-1) |
      result = descriptorUpTo(n-1) + p.getType().getTypeDescriptor()
    )
  }

  /**
   * A constructor that may be called from this callable.
   *
   * DEPRECATED: use `getACallee` instead.
   */
  Constructor getAConstructorCall() {
    result = getACallee()
  }

  /** Whether this callable calls `target`. */
  predicate calls(Callable target) {
    exists (getACallSite(target))
  }

  /**
   * Whether this callable calls `target`
   * using a `super(...)` constructor call.
   */
  predicate callsSuper(Constructor target) {
    getACallSite(target) instanceof SuperConstructorInvocationStmt
  }

  /**
   * Whether this callable calls `target`
   * using a `this(...)` constructor call.
   */
  predicate callsThis(Constructor target) { 
    getACallSite(target) instanceof ThisConstructorInvocationStmt
  }

  /**
   * Whether this callable calls `target`
   * using a `super` method call.
   */
  predicate callsSuper(Method target) {
    getACallSite(target) instanceof SuperMethodAccess
  }

  /**
   * Whether this callable calls `c` using
   * either a `super(...)` constructor call
   * or a `this(...)` constructor call.
   */
  predicate callsConstructor(Constructor c) {
    this.callsSuper(c) or this.callsThis(c)
  }

  /**
   * Whether this callable may call the specified callable,
   * taking overriding into account.
   */
  predicate polyCalls(Callable m) {
    this.calls(m) or
    exists(Method mSuper, VirtualMethodAccess c | 
      c.getCaller() = this and c.getMethod() = mSuper |
      m.(Method).overrides(mSuper)
    )
  }

  /**
   * Whether field `f` may be assigned a value
   * within the body of this callable.
   */
  predicate writes(Field f) {
    f.getAnAccess().(LValue).getEnclosingCallable() = this
  }

  /**
   * Whether field `f` may be read
   * within the body of this callable.
   */
  predicate reads(Field f) {
    f.getAnAccess().(RValue).getEnclosingCallable() = this
  }

  /**
   * Whether field `f` may be either read or written
   * within the body of this callable.
   */
  predicate accesses(Field f) { this.writes(f) or this.reads(f) }

  /** A field accessed in this callable. */
  Field getAnAccess() { this.accesses(result) }

  /** The type of a formal parameter of this callable. */
  Type getAParamType() { result = getParameterType(_) }

  /** Whether this callable does not have any formal parameters. */
  predicate hasNoParameters() { not exists(getAParameter()) }

  /** The number of formal parameters of this callable. */
  int getNumberOfParameters() { 
    result = count(getAParameter())
  }

  /** A formal parameter of this callable. */
  Parameter getAParameter() { result.getCallable() = this }

  /** The formal parameter at the specified (zero-based) position. */
  Parameter getParameter(int n) { params(result, _, _, n, this, _) }

  /** The type of the formal parameter at the specified (zero-based) position. */
  Type getParameterType(int n) { params(_, _, result, n, this, _) }

  /**
   * The signature of this callable, including its name and the types of all its parameters,
   * identified by their simple (unqualified) names.
   *
   * Use `getSignature` to obtain a signature including fully qualified type names.
   */
  string getStringSignature() {
    result = this.getName() + this.paramsString()
  }

  /** A parenthesized string containing all parameter types of this callable, separated by a comma. */
  string paramsString() {
    exists(int n | n = getNumberOfParameters() | 
      n = 0 and result = "()"
      or
      n > 0 and result = "(" + this.paramUpTo(n-1) + ")"
    )
  }

  /**
   * A string containing the parameter types of this callable
   * from left to right, up to (and including) the `n`-th parameter.
   */
  private string paramUpTo(int n) {
    n = 0 and result = getParameterType(0).toString()
    or
    n > 0 and result = paramUpTo(n-1) + ", " + getParameterType(n)
  }

  /** Whether this callable has the specified string signature. */
  predicate hasStringSignature(string sig) {
    sig = this.getStringSignature()
  }

  /** An exception that occurs in the `throws` clause of this callable. */
  Exception getAnException() { exceptions(result,_,this) }

  /** An exception type that occurs in the `throws` clause of this callable. */
  RefType getAThrownExceptionType() { result = getAnException().getType() }

  /** A call site that references this callable. */
  Call getAReference() {
    result.getCallee() = this 
  }

  /** The path to the icon used when displaying query results. */
  string getIconPath() { result = "icons/method.png" }

  /** The body of this callable, if any. */
  Block getBody() { result.getParent() = this }

  /**
   * The source declaration of this callable.
   *
   * For parameterized instances of generic methods, the
   * source declaration is the corresponding generic method.
   *
   * For non-parameterized callables declared inside a parameterized
   * instance of a generic type, the source declaration is the
   * corresponding callable in the generic type.
   *
   * For all other callables, the source declaration is the callable itself.
   */
  Callable getSourceDeclaration() { result = this }

  /** Whether this callable is the same as its source declaration. */
  predicate isSourceDeclaration() { this.getSourceDeclaration() = this }

  /** Cast this callable to a class that provides access to metrics information. */
  MetricCallable getMetrics() { result = this }

  /** Whether the last parameter of this callable is a varargs (variable arity) parameter. */
  predicate isVarargs() { this.getAParameter().isVarargs() }

  /**
   * The signature of this callable, where all types in the signature have a fully-qualified name.
   *
   * For example, method `void m(String s)` has the signature `m(java.lang.String)`.
   */
  string getSignature() {
    constrs(this, _, result, _, _, _) or
    methods(this, _, result, _, _, _)
  }
}

/**
 * Whether callable `c` has a parameter of type `t`
 * at (zero-based) position `pos`.
 *
 * For example, `p(A x, B y)` has a parameter of type `B` at position 1.
 *
 * DEPRECATED: use `Callable.getParameterType` instead.
 */
deprecated
predicate hasParam(Callable c, Type t, int pos) {
  t = c.getParameterType(pos)
}

/**
 * Whether callable `c` has signature `sig`,
 * where all types in the signature have a fully-qualified name.
 *
 * For example, method `void m(String s)` has the signature
 * `m(java.lang.String)`.
 *
 * DEPRECATED: use `Callable.getSignature` instead.
 */
deprecated
predicate hasSignature(Callable c, string sig) {
  sig = c.getSignature()
}

/**
 * Whether callable `c` has return type `t`.
 *
 * DEPRECATED: use `Callable.getType` instead.
 */
deprecated
predicate returnsType(Callable c, Type t) {
  t = c.getType()
}

/**
 * Whether method `m` is neither private nor static, and hence
 * could be inherited.
 *
 * DEPRECATED: use `Method.isInheritable` instead.
 */
deprecated
predicate inheritableMethod(Method m) {
  m.isInheritable()
}

/**
 * Whether methods `m1` and `m2` have the same signature.
 *
 * DEPRECATED: use `Method.getSignature` instead.
 */
deprecated
predicate hasSameSignature(Method m1, Method m2) {
  m1.getSignature() = m2.getSignature()
}

/** Whether method `m1` overrides method `m2`. */
private
predicate overrides(Method m1, Method m2) {
  exists (RefType t1, RefType t2 | overridesIgnoringAccess(m1, t1, m2, t2) |
    m2.isPublic() or
    m2.isProtected() or
    m2.isPackageProtected() and t1.getPackage() = t2.getPackage()
  )
}

/**
 * Auxiliary predicate: whether method `m1` overrides method `m2`,
 * ignoring any access modifiers. Additionally, this predicate binds
 * `t1` to the type declaring `m1` and `t2` to the type declaring `m2`.
 */
pragma[noopt]
predicate overridesIgnoringAccess(Method m1, RefType t1, Method m2, RefType t2) {
  exists(string sig |
    inheritableMethodWithSignature(sig, t1, m1) and
    hasSubtype+(t2,t1) and
    inheritableMethodWithSignature(sig, t2, m2)
  )
}

private predicate inheritableMethodWithSignature(string sig, RefType t, Method m) {
  declaresMethod(t, m) and
  sig = m.getSignature() and
  m.isInheritable()
}


/** A method is a particular kind of callable. */
class Method extends Callable, @method {
  /** Whether this method (directly) overrides the specified callable. */
  predicate overrides(Method m) { overrides(this, m) }

  /** A method (directly or transitively) overridden by this method. */
  Method getAnOverride() {
    this.overrides+(result)
  }

  string getSignature() { methods(this,_,result,_,_,_) }

  /**
   * Whether this method and method `m` are declared in the same type
   * and have the same parameter types.
   */
  predicate sameParamTypes(Method m) {
   // `this` and `m` are different methods,
   this != m and
   // `this` and `m` are declared in the same type,
   this.getDeclaringType() = m.getDeclaringType() and
   // `this` and `m` are of the same arity, and
   this.getNumberOfParameters() = m.getNumberOfParameters() and
   // there does not exist a pair of parameters whose types differ.
   not exists(int n | this.getParameterType(n) != m.getParameterType(n))
  }

  /**
   * The path to the icon used when displaying query results.
   *
   * A different icon is used depending on the access modifier of this method.
   */
  string getIconPath() {
    this.isPrivate() and result = "icons/privatemethod.png" or
    this.isProtected() and result = "icons/protectedmethod.png" or
    this.isPublic() and result = "icons/publicmethod.png" or
    this.isPackageProtected() and result = "icons/method.png"
  }

  Method getSourceDeclaration() { methods(this,_,_,_,_,result) }

  /**
   * All the methods that could possibly be called when this method
   * is called: the method itself and all its overriding methods (if any).
   *
   * Only includes method implementations, not abstract or interface methods.
   * Native methods are included, since they have an implementation (just not in Java).
   */
  Method getAPossibleImplementation() {
    exists(Method overriding | overriding.overrides*(this) |
      result = overriding.getSourceDeclaration() and
      (exists(result.getBody()) or result.hasModifier("native"))
    )
  }
  
  MethodAccess getAReference() {
    result = Callable.super.getAReference()
  }

  predicate isPublic() {
    Callable.super.isPublic() or
    // JLS 9.4: Every method declaration in the body of an interface is implicitly public.
    getDeclaringType() instanceof Interface
  }

  predicate isAbstract() {
    Callable.super.isAbstract() or
    // JLS 9.4: An interface method lacking a `default` modifier or a `static` modifier
    // is implicitly abstract.
    (this.getDeclaringType() instanceof Interface and
     not this.isDefault() and not this.isStatic())
  }

  predicate isStrictfp() {
    Callable.super.isStrictfp() or
    // JLS 8.1.1.3, JLS 9.1.1.2
    getDeclaringType().isStrictfp()
  }

  /**
   * Whether this method is neither private nor static, and hence
   * could be inherited.
   */
  predicate isInheritable() {
    not isPrivate() and not isStatic()
  }
}


/**
 * A _setter_ method is a method with the following properties:
 *
 * - it has exactly one parameter,
 * - its body contains exactly one statement
 *   that assigns the value of the method parameter to a field
 *   declared in the same type as the method.
 */
class SetterMethod extends Method {
  SetterMethod() {
    this.getNumberOfParameters() = 1 and
    exists (ExprStmt s, Assignment a |
      s = this.getBody().(SingletonBlock).getStmt() and a = s.getExpr() |
      exists (Field f | f.getDeclaringType() = this.getDeclaringType() |
        a.getDest() = f.getAnAccess() and
        a.getSource() = this.getAParameter().getAnAccess()
      )
    )
  }

  /** The field assigned by this setter method. */
  Field getField() {
    exists(Assignment a | a.getEnclosingCallable() = this |
      a.getDest() = result.getAnAccess()
    )
  }
}

/**
 * A _getter_ method is a method with the following properties:
 *
 * - it has no parameters,
 * - its body contains exactly one statement
 *   that returns the value of a field.
 */
class GetterMethod extends Method {
  GetterMethod() {
    this.hasNoParameters() and
    exists(ReturnStmt s, Field f | s = this.getBody().(SingletonBlock).getStmt() |
      s.getResult() = f.getAnAccess()
    )
  }

  /** The field whose value is returned by this getter method. */
  Field getField() {
    exists(ReturnStmt r | r.getEnclosingCallable() = this |
      r.getResult() = result.getAnAccess()
    )
  }
}

/**
 * A finalizer method, with name `finalize`,
 * return type `void` and modifier `protected`.
 */
class FinalizeMethod extends Method {
  FinalizeMethod() {
    this.hasName("finalize") and 
    this.getType().hasName("void") and 
    this.isProtected()
  }
}

/** A constructor is a particular kind of callable. */
class Constructor extends Callable, @constructor {
  /** Whether this is a default constructor, not explicitly declared in source code. */
  predicate isDefaultConstructor() { isDefConstr(this) }

  /** The path to the icon used when displaying query results. */
  string getIconPath() { result = "icons/constructor.png" }

  Constructor getSourceDeclaration() { constrs(this,_,_,_,_,result) }

  string getSignature() { constrs(this,_,result,_,_,_) }
}

/**
 * A compiler-generated initializer method (could be static or
 * non-static), which is used to hold (static or non-static) field
 * initializers, as well as explicit initializer blocks.
 */
abstract class InitializerMethod extends Method {}

/**
 * A static initializer is a method that contains all static
 * field initializations and static initializer blocks.
 */
class StaticInitializer extends InitializerMethod {
  StaticInitializer() {
    hasName("<clinit>")
  }
}

/**
 * An instance initializer is a method that contains field initializations
 * and explicit instance initializer blocks.
 */
class InstanceInitializer extends InitializerMethod {
  InstanceInitializer() {
    this.hasName("<obinit>")
  }
}

/**
 * Whether field `f` has type `t`.
 *
 * DEPRECATED: use `Field.getType` instead.
 */
deprecated
predicate hasType(Field f, Type t) {
  t = f.getType()
}

/** A field declaration that declares one or more class or instance fields. */
class FieldDeclaration extends ExprParent, @fielddecl, Annotatable {
  /** The access to the type of the field(s) in this declaration. */
  Expr getTypeAccess() { result.getParent() = this }

  /** A field declared in this declaration. */
  Field getAField() { fieldDeclaredIn(result, this, _) }

  /** The field declared at the specified (zero-based) position in this declaration */
  Field getField(int idx) { fieldDeclaredIn(result, this, idx) }

  /** The number of fields declared in this declaration. */
  int getNumField() { result = max(int idx | fieldDeclaredIn(_, this, idx) | idx) + 1 }

  string toString() {
    if this.getNumField() = 0 then
      result = this.getTypeAccess() + " " + this.getField(0) + ";"
    else
      result = this.getTypeAccess() + " " + this.getField(0) + ", ...;"
  }
}

/** A class or instance field. */
class Field extends Member, ExprParent, @field, Variable {
  string toString() { result = Member.super.toString() }

  /** The declared type of this field. */
  Type getType() { fields(this, _, result, _, _) }

  /** The type in which this field is declared. */
  RefType getDeclaringType() { declaresField(result,this) }

  /**
   * The field declaration in which this field is declared.
   *
   * Note that this declaration is only available if the field occurs in source code.
   */
  FieldDeclaration getDeclaration() { result.getAField() = this }

  /** The path to the icon used when displaying query results. */
  string getIconPath() { result = "icons/field.png" }

  /** The initializer expression of this field, if any. */
  Expr getInitializer() {
    exists(AssignExpr e | e.getDest() = this.getAnAccess() and e.getSource() = result |
      result.getEnclosingCallable() instanceof InitializerMethod
    )
  }

  /**
   * The source declaration of this field.
   *
   * For fields that are members of a parameterized
   * instance of a generic type, the source declaration is the
   * corresponding field in the generic type.
   *
   * For all other fields, the source declaration is the field itself.
   */
  Field getSourceDeclaration() { fields(this,_,_,_,result) }

  /** Whether this field is the same as its source declaration. */
  predicate isSourceDeclaration() { this.getSourceDeclaration() = this }

  predicate isPublic() {
    Member.super.isPublic() or
    // JLS 9.3: Every field declaration in the body of an interface is
    // implicitly public, static, and final
    getDeclaringType() instanceof Interface
  }

  predicate isStatic() {
    Member.super.isStatic() or
    // JLS 9.3: Every field declaration in the body of an interface is
    // implicitly public, static, and final
    this.getDeclaringType() instanceof Interface
  }

  predicate isFinal() {
    Member.super.isFinal() or
    // JLS 9.3: Every field declaration in the body of an interface is
    // implicitly public, static, and final
    this.getDeclaringType() instanceof Interface
  }

  /** Cast this field to a class that provides access to metrics information. */
  MetricField getMetrics() { result = this }
}

/** An instance field. */
class InstanceField extends Field {
  InstanceField() {
    not this.isStatic()
  }
}
