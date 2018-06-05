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

import semmle.code.cpp.Class
private import semmle.code.cpp.internal.Type

/**
 * An Objective C class.
 */
class ObjectiveClass extends Class {
  ObjectiveClass() { usertypes(this,_,10) }
}

/**
 * An Objective C protocol.
 */
class Protocol extends Class {
  Protocol() { usertypes(this,_,11) }

  /**
   * Holds if the type implements the protocol, either because the type
   * itself does, or because it is a type conforming to the protocol.
   */
  predicate isImplementedBy(Type t) {
    // Base case
    exists (TypeConformingToProtocol pctp
    | pctp = t and pctp.getAProtocol() = this)
    or
    // Base case
    t.(Class).getABaseClass*() = this
    or
    // Look through typedef and decltype:
    this.isImplementedBy(t.getUnderlyingType())
    or
    // Look through `const` and friends:
    exists(SpecifiedType s | s = t and this.isImplementedBy(s.getBaseType()))
  }
}

/**
 * A type which conforms to a protocol. Use `getAProtocol` to get a
 * protocol that this type conforms to.
 */
class TypeConformingToProtocol extends DerivedType {
  TypeConformingToProtocol() { derivedtypes(this,_,9,_) }

  /** Gets a protocol that this type conforms to. */
  Protocol getAProtocol() { conforming_to_protocols(this, result) }

  /** Gets the size of this type. */
  override int getSize() { result = this.getBaseType().getSize() }
}

/**
 * An Objective C `@autoreleasepool` statement, for example
 * `@autoreleasepool { int x; int y; }`.
 */
class AutoReleasePoolStmt extends Stmt, @stmt_at_autoreleasepool_block {
  override string toString() { result = "@autoreleasepool { ... }" }

  /** Gets the body statement of this `@autoreleasepool` statement. */
  Stmt getStmt() { result = this.getChild(0) }

  override predicate mayBeImpure() {
    this.getStmt().mayBeImpure()
  }

  override predicate mayBeGloballyImpure() {
    this.getStmt().mayBeGloballyImpure()
  }
}

/**
 * An Objective C `@synchronized statement`, for example
 * `@synchronized (x) { [x complicationOperation]; }`.
 */
class SynchronizedStmt extends Stmt, @stmt_at_synchronized {
  override string toString() { result = "@synchronized (...) { ... }" }

  /** Gets the expression which gives the object to be locked. */
  Expr getLockedObject() { result = this.getChild(0) }

  /** Gets the body statement of this `@synchronized` statement. */
  Stmt getStmt() { result = this.getChild(1) }
}

/**
 * An Objective C for-in statement.
 */
class ForInStmt extends Loop, @stmt_objc_for_in {
  /**
   * Gets the condition expression of the `while` statement that the
   * `for...in` statement desugars into.
   */
  override Expr getCondition() { objc_for_in(this, _, result, _) }

  override Expr getControllingExpr() { result = this.getCondition() }

  /** Gets the collection that the loop iterates over. */
  Expr getCollection() { objc_for_in(this, result, _, _) }

  /** Gets the body of the loop. */
  Stmt getStmt() { objc_for_in(this, _, _, result) }

  override string toString() { result = "for(... in ...) ..." }
}

/**
 * An Objective C category or class extension.
 */
class Category extends Class {
  Category() { usertypes(this,_,12) }
}

/**
 * An Objective C class extension.
 */
class ClassExtension extends Category {
  ClassExtension() { getName().matches("%()") }
}

/**
 * An Objective C try statement.
 */
class ObjcTryStmt extends TryStmt {
  ObjcTryStmt() { is_objc_try_stmt(this) }

  override string toString() { result = "@try { ... }" }

  /** Gets the finally clause of this try statement, if any. */
  FinallyBlock getFinallyClause() { result = this.getChild(_) }
}

/**
 * An Objective C `@finally` block.
 */
class FinallyBlock extends Block {
  FinallyBlock() { isfinally(this) }

  /** Gets the try statement corresponding to this finally block. */
  ObjcTryStmt getTryStmt() {
    result.getFinallyClause() = this
  }
}

/**
 * An Objective C `@property`.
 */
class Property extends Declaration, @property {
  /** Gets the name of this property. */
  override string getName() { properties(this, _, result, _) }

  /**
   * Gets nothing (provided for compatibility with Declaration).
   *
   * For the attribute list following the `@property` keyword, use
   * `getAnAttribute()`.
   */
  override Specifier getASpecifier() { none() }

  /**
   * Gets an attribute of this property (such as `readonly`, `nonatomic`,
   * or `getter=isEnabled`).
   */
  Attribute getAnAttribute() { property_attribute(this, result) }

  override Location getADeclarationLocation() { result = getLocation() }
  override Location getDefinitionLocation() { result = getLocation() }
  override Location getLocation() { property_decl_location(this, result) }

  /** Gets the type of this property. */
  Type getType() { properties(this, unresolve(result), _, _) }

  /**
   * Gets the instance method which is called to get the value of this
   * property.
   */
  MemberFunction getGetter() { properties(this, _, _, result) }

  /**
   * Gets the instance method which is called to set the value of this
   * property (if it is a writable property).
   */
  MemberFunction getSetter() { property_setter(this, result) }

  /**
   * Gets the instance variable which stores the property value (if this
   * property was explicitly or automatically `@synthesize`d).
   */
  MemberVariable getInstanceVariable() { property_synthesis(this, result) }
}
