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

import semmle.code.cpp.exprs.Expr
import semmle.code.cpp.Class
import semmle.code.cpp.ObjectiveC

/**
 * An Objective C message expression, for example `[myColor changeColorToRed:5.0 green:2.0 blue:6.0]`.
 */
class MessageExpr extends Expr, Call, @msgexpr {
  override string toString() {
    result = "[... ...]"
  }

  /**
   * Gets the selector of this message expression, for example `-changeColorToRed:green:blue:`.
   */
  string getSelector() {
    msgexpr_selector(this, result)
  }

  /**
   * Gets the function invoked by this message expression, as inferred by the compiler.
   *
   * If the compiler could infer the type of the receiver, and that type had a method
   * whose name matched the selector, then the result of this predicate is said method.
   * Otherwise this predicate has no result.
   *
   * In all cases, actual function dispatch isn't performed until runtime, but the
   * lack of a static target is often cause for concern.
   */
  MemberFunction getStaticTarget() {
    funbind(this, result)
  }

  /**
   * Provided for compatibility with Call. It is the same as the static target.
   */
  override MemberFunction getTarget() {
    result = getStaticTarget()
  }

  /**
   * Holds if the compiler could infer a function as the target of this message.
   *
   * In all cases, actual function dispatch isn't performed until runtime, but the
   * lack of a static target is often cause for concern.
   */
  predicate hasStaticTarget() {
    exists(getStaticTarget())
  }

  /**
   * Gets the number of arguments passed by this message expression.
   *
   * In most cases, this equals the number of colons in the selector, but this needn't be the
   * case for variadic methods like "-initWithFormat:", which can have more than one argument.
   */
  override int getNumberOfArguments() { result = count(this.getAnArgument()) }

  /**
   * Gets an argument passed by this message expression.
   */
  override Expr getAnArgument() {
    exists(int i | i >= 0 | result = this.getChild(i))
  }

  /**
   * Gets the nth argument passed by this message expression.
   *
   * The range of `n` is [`0` .. `getNumberOfArguments()`].
   */
  override Expr getArgument(int n) {
    result = this.getChild(n)
  }

  override int getPrecedence() { result = 16 }
}

/**
 * An Objective C message expression whose receiver is `super`, for example `[super init]`.
 */
class SuperMessageExpr extends MessageExpr, @msgexpr_super {
}

/**
 * An Objective C message expression whose receiver is the name of a class, and
 * is therefore calling a class method rather than an instance method. This occurs
 * most commonly for the "+alloc", "+new", and "+class" selectors.
 */
class ClassMessageExpr extends MessageExpr, @msgexpr_normal {
  ClassMessageExpr() {
    msgexpr_receiver_type(this, _)
  }

  /**
   * Gets the class which is the receiver of this message.
   */
  Type getReceiver() {
    msgexpr_receiver_type(this, result)
  }
}

/**
 * An Objective C message expression whose receiver is an expression (which includes the
 * common case of the receiver being "self").
 */
class ExprMessageExpr extends MessageExpr, @msgexpr_normal {
  ExprMessageExpr() {
    not this instanceof ClassMessageExpr
  }

  /**
   * Gets the expression which gives the receiver of this message.
   */
  Expr getReceiver() {
    result = this.getChild(-1)
  }

  /**
   * Gets the Objective C class of which the receiving expression is an instance.
   *
   * If the receiving expression has type `id` or type `id<P>` for some protocol `P`,
   * then there will be no result. If the receiving expression has type `C*` or type
   * `C<P>*` for some protocol `P`, then the result will be the type `C`.
   */
  ObjectiveClass getReceiverClass() {
    result = getAReceiverClassOrProtocol()
  }

  /**
   * Gets the Objective C classes and/or protocols which are statically implemented
   * by the receiving expression.
   *
   * If the receiving expression has type `id`, then there will be no result.
   * If the receiving expression has type `id<P>`, then `P` will be the sole result.
   * If the receiving expression has type `C*`, then `C` will be the sole result.
   * If the receiving expression has type `C<P>*`, then `C` and `P` will both be results.
   */
  Class getAReceiverClassOrProtocol() {
    exists(Type receiver |
      receiver = getReceiver().getUnderlyingType() |
      exists(Type base |
        base = receiver.(PointerType).getBaseType() or
        base = receiver.(TypeConformingToProtocol).getBaseType()
      |
        result = base.getUnderlyingType()
      ) or
      result = receiver.(TypeConformingToProtocol).getAProtocol()
    )
  }
}

/**
 * An access to an Objective C property using dot syntax.
 *
 * Such accesses are de-sugared into a message expression to the property's getter or setter.
 */
class PropertyAccess extends ExprMessageExpr {
  PropertyAccess() {
    msgexpr_for_property(this)
  }

  /**
   * Gets the property being accessed by this expression.
   */
  Property getProperty() {
    result.getSetter() = getStaticTarget() or
    result.getGetter() = getStaticTarget()
  }
}

/**
 * An Objective C `@selector` expression, for example `@selector(driveForDistance:)`.
 */
class AtSelectorExpr extends Expr, @atselectorexpr {
  override string toString() {
    result = "@selector(...)"
  }

  /**
   * Gets the selector of this `@selector` expression, for example `driveForDistance:`.
   */
  string getSelector() {
    atselectorexpr_selector(this, result)
  }
}

/**
 * An Objective C `@protocol` expression, for example `@protocol(SomeProtocol)`.
 */
class AtProtocolExpr extends Expr, @atprotocolexpr {
  override string toString() {
    result = "@protocol(...)"
  }

  /**
   * Gets the protocol of this `@protocol` expression, for example `SomeProtocol`.
   */
  Protocol getProtocol() {
    atprotocolexpr_protocol(this, result)
  }
}

/**
 * An Objective C `@encode` expression, for example `@encode(int *)`.
 */
class AtEncodeExpr extends Expr, @atencodeexpr {
  override string toString() {
    result = "@encode(...)"
  }

  /**
   * Gets the type this `@encode` expression encodes, for example `int *`.
   */
  Type getEncodedType() {
    atencodeexpr_type(this, result)
  }
}

/**
 * An Objective C throw expression.
 */
class ObjcThrowExpr extends ThrowExpr {
  ObjcThrowExpr() { is_objc_throw(this) }

  override string toString() { result = "@throw ..." }
}

/**
 * An Objective C throw expression with no argument (which causes the
 * current exception to be re-thrown).
 */
class ObjcReThrowExpr extends ReThrowExpr, ObjcThrowExpr {
  override string toString() { result = "re-@throw exception " }
}

/**
 * An Objective C @ expression which boxes a single value, such as @(22).
 */
class AtExpr extends UnaryOperation, @objc_box_expr {
  override string toString() { result = "@(...)" }

  override string getOperator() { result = "@" }
}

/**
 * An Objective C @[...] literal.
 */
class ArrayLiteral extends Expr, @objc_array_literal {
  /** Gets a textual representation of this array literal. */
  override string toString() { result = "@[...]" }
 
  /** An element of the array */
  Expr getElement(int i) { result = getChild(i) }
}

/**
 * An Objective C @{...} literal.
 */
class DictionaryLiteral extends Expr, @objc_dictionary_literal {
  /** Gets a textual representation of this dictionary literal. */
  override string toString() { result = "@{...}" }
}

/**
 * An Objective C @"..." string literal.
 */
class ObjCLiteralString extends TextLiteral {
  ObjCLiteralString() {
    objc_string(this)
  }
}

/**
 * An Objective C/C++ overloaded subscripting access expression.
 *
 * Either
 *     obj[idx]
 * or
 *     obj[idx] = expr
 */
class SubscriptExpr extends Expr, @objc_subscriptexpr {
  /**
   * Gets the object expression being subscripted.
   */
  Expr getSubscriptBase() { result = this.getChild(0) }

  /**
   * Gets the expression giving the index into the object.
   */
  Expr getSubscriptIndex() { result = this.getChild(1) }

  /**
   * Gets the expression being assigned (if this is an assignment).
   */
  Expr getAssignedExpr() { result = this.getChild(2) }

  override string toString() { result = "object subscript" }
}

/**
 * An Objective C _cmd expression.
 */
class CmdExpr extends Expr, @cmdaccess {
  override string toString() { result = "_cmd" }

  override predicate mayBeImpure() {
    none()
  }
  override predicate mayBeGloballyImpure() {
    none()
  }
}
