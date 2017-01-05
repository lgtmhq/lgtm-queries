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
 * QL classes for working with expressions.
 */

import Locations
import AST
import Regexp

/** An expression. */
class Expr extends @expr, ExprOrStmt {
  /** Get the statement in which this expression appears. */
  Stmt getEnclosingStmt() {
    enclosingStmt(this, result)
  }
  
  /** Get the function (if any) in which this expression appears. */
  Function getEnclosingFunction() {
    result = getContainer()
  }
  
  /** Get the statement container (function or toplevel) in which
   * this expression appears. */
  StmtContainer getContainer() {
    exprContainers(this, result)
  }
  
  /** Get this expression, with any surrounding parentheses removed. */
  Expr stripParens() {
    result = this
  }

  /** If this expression evaluates to a constant integer value, return it. */
  int getIntValue() {
    none()
  }

  /** If this expression evaluates to a constant string value, return it. */
  string getStringValue() {
    none()
  }

  /** Is this expression impure, that is, could its evaluation have side effects? */
  predicate isImpure() {
    any()
  }

  /** Is this expression pure, that is, is its evaluation guaranteed to be side effect-free? */
  predicate isPure() {
    not isImpure()
  }

  /**
   * Get the kind of this expression, which is an integer
   * value representing the expression's node type.
   *
   * _Note_: The mapping from node types to integers is considered an implementation detail
   * and may change between versions of the extractor.
   */
  int getKind() {
     exprs(this, result, _, _, _)
  }

  /**
   * Get the JSDoc comment associated with this expression or its parent statement, if any.
   */
  JSDoc getDocumentation() {
    result = getOwnDocumentation() or
    // if there is no JSDoc attached to the expression itself, check the enclosing property or statement
    (not exists(getOwnDocumentation()) and
     if getParent() instanceof Property then
       result = getParent().(Property).getDocumentation()
     else
       result = getEnclosingStmt().getDocumentation())
  }

  /** Get a JSDoc comment that is immediately before this expression (ignoring parentheses). */
  private JSDoc getOwnDocumentation() {
    exists (Token tk | tk = result.getComment().getNextToken() |
      tk = this.getFirstToken() or exists (Expr p | p.stripParens() = this | tk = p.getFirstToken())
    )
  }
  
  string toString() {
    exprs(this, _, _, _, result)
  }

  /**
   * Get the expression that is parent of this expression in the AST, if any.
   *
   * Note that for property names and property values the associated object expression or pattern
   * is returned, skipping the property node itself (which is not an expression).
   */
  Expr getParentExpr() {
    this = result.getAChildExpr() or
    exists (Property prop |
      result = prop.getParent() and
      this = prop.getAChildExpr()
    )
  }
}

/** An identifier. */
class Identifier extends @identifier, Expr {
  /** Get the name of this identifier. */
  string getName() {
    literals(result, _, this)
  }

  predicate isImpure() {
    none()
  }
}

/**
 * A statement or property label, that is, an identifier that
 * does not refer to a variable.
 */
class Label extends @label, Identifier {
}

/** A literal. */
class Literal extends @literal, Expr {
  /** Get the value of this literal, as a string. */
  string getValue() {
    literals(result, _, this)
  }
  
  /** Get the raw source text of this literal. For string literals,
   * this includes quotes. */
  string getRawValue() {
    literals(_, result, this)
  }
  
  predicate isImpure() {
    none()
  }
}

/** A parenthesized expression. */
class ParExpr extends @parexpr, Expr {
  /** Get the expression within parentheses. */
  Expr getExpression() {
    result = this.getChildExpr(0)
  }
  
  Expr stripParens() {
    result = getExpression().stripParens()
  }

  int getIntValue() {
    result = getExpression().getIntValue()
  }
  
  predicate isImpure() {
    getExpression().isImpure()
  }
}

/** A `null` literal. */
class NullLiteral extends @nullliteral, Literal {}

/** A Boolean literal, that is, either `true` or `false`. */
class BooleanLiteral extends @booleanliteral, Literal {}

/** A numeric literal. */
class NumberLiteral extends @numberliteral, Literal {
  /** Get the integer value of this literal. */
  int getIntValue() {
    result = getValue().toInt()
  }
  
  /** Get the floating point value of this literal. */
  int getFloatValue() {
    result = getValue().toFloat()
  }
}

/** A string literal. */
class StringLiteral extends @stringliteral, Literal {
  string getStringValue() {
    result = getValue()
  }
}

/** A regular expression literal. */
class RegExpLiteral extends @regexpliteral, Literal, RegExpParent {
  string toString() {
    result = Literal.super.toString()
  }
  
  /** Get the flags of this regular expression. */
  string getFlags() {
    result = getValue().regexpCapture(".*/(\\w*)$", 1)
  }
  
  /** Does this regular expression have an `m` flag? */
  predicate isMultiline() {
    getFlags().matches("%m%")
  }
  
  /** Does this regular expression have a `g` flag? */
  predicate isGlobal() {
    getFlags().matches("%g%")
  }
  
  /** Does this regular expression have an `i` flag? */
  predicate isIgnoreCase() {
    getFlags().matches("%i%")
  }
}

/** A `this` expression. */
class ThisExpr extends @thisexpr, Expr {
  predicate isImpure() {
    none()
  }
}

/** An array literal. */
class ArrayExpr extends @arrayexpr, Expr {
  /** Get the i-th element of this array literal. */
  Expr getElement(int i) {
    result = this.getChildExpr(i)
  }
  
  /** Get some element of this array literal. */
  Expr getAnElement() {
    result = this.getAChildExpr()
  }
  
  /** Get the number of elements in this array literal. */
  int getSize() {
    arraySize(this, result)
  }
  
  /** Does this array literal include a trailing comma after the
   * last element? */
  predicate hasTrailingComma() {
    this.getLastToken().getPreviousToken().getValue() = ","
  }
  
  /** Is the i-th element of this array literal omitted? */
  predicate elementIsOmitted(int i) {
    i in [0..getSize()-1] and
    not exists (getElement(i))
  }
  
  /** Does this array literal have an omitted element? */
  predicate hasOmittedElement() {
    elementIsOmitted(_)
  }
  
  predicate isImpure() {
    getAnElement().isImpure()
  }
}

/** An object literal. */
class ObjectExpr extends @objexpr, Expr {
  /** Get the i-th property in this object literal. */
  Property getProperty(int i) {
    properties(result, this, i, _, _)
  }
  
  /** Get some property in this object literal. */
  Property getAProperty() {
    exists (int i | result = this.getProperty(i))
  }
  
  /** Get the number of properties in this object literal. */
  int getNumProperty() {
    result = count(this.getAProperty())
  }
  
  /** Get the property with the given name, if any. */
  Property getPropertyByName(string name) {
    result = this.getAProperty() and
    result.getName() = name
  }
  
  /** Does this object literal include a trailing comma after the
   * last property? */
  predicate hasTrailingComma() {
    this.getLastToken().getPreviousToken().getValue() = ","
  }
  
  predicate isImpure() {
    getAProperty().isImpure()
  }
}

/**
 * A property definition in an object literal, which may be either
 * a value property, a property getter, or a property setter.
 */
class Property extends @property, ASTNode {
  Property() {
    // filter out property patterns and JSX attributes
    exists (ObjectExpr obj | properties(this, obj, _, _, _))
  }

  /**
   * Get the expression specifying the name of the property. For normal
   * properties, this is either an identifier, a string literal, or a
   * numeric literal; for computed properties it can be an arbitrary
   * expression.
   *
   * For spread properties, the name is not defined.
   */
  Expr getNameExpr() {
    result = this.getChildExpr(0)
  }
  
  /** Get the expression specifying the initial value of the property. */
  Expr getInit() {
    result = this.getChildExpr(1)
  }
  
  /** Get the name of this property. */
  string getName() {
    result = ((Identifier)getNameExpr()).getName() or
    result = ((Literal)getNameExpr()).getValue()
  }
  
  /** Is the name of this property computed? */
  predicate isComputed() {
    isComputed(this)
  }

  /** Is this property defined using method syntax? */
  predicate isMethod() {
    isMethod(this)
  }

  /** Is this property defined using shorthand syntax? */
  predicate isShorthand() {
    getNameExpr().getLocation() = getInit().getLocation()
  }
  
  /** Get the object literal this property belongs to. */
  ObjectExpr getObjectExpr() {
    properties(this, result, _, _, _)
  }

  /** Get the (0-based) index at which this property appears in its enclosing literal. */
  int getIndex() {
    this = getObjectExpr().getProperty(result)
  }

  /** Get the JSDoc comment for this property, if any. */
  JSDoc getDocumentation() {
    result.getComment().getNextToken() = getFirstToken()
  }
  
  /** Get the function or toplevel in which this property occurs. */
  StmtContainer getContainer() {
    result = getObjectExpr().getContainer()
  }

  /**
   * Is this property impure, that is, could the evaluation of its name or
   * its initializer expression have side effects?
   */
  predicate isImpure() {
    (isComputed() and getNameExpr().isImpure()) or
    getInit().isImpure()
  }

  string toString() {
    properties(this, _, _, _, result)
  }

  CFGNode getFirstCFGNode() {
    result = getNameExpr().getFirstCFGNode() or
    not exists(getNameExpr()) and result = getInit().getFirstCFGNode()
  }

  /**
   * Get the kind of this expression, which is an opaque integer
   * value indicating whether this property is a value property,
   * a property getter, or a property setter.
   */
  int getKind() {
    properties(this, _, _, result, _)
  }

  /**
   * The `i`-th decorator applied to this property.
   *
   * For example, the property `@A @B x: 42` has
   * `@A` as its 0-th decorator, and `@B` as its first decorator.
   */
  Decorator getDecorator(int i) {
    result = getChildExpr(-(i+1))
  }

  /**
   * A decorator applied to this property, if any.
   *
   * For example, the property `@A @B x: 42` has
   * decorators `@A` and `@B`.
   */
  Decorator getADecorator() {
    result = getDecorator(_)
  }
}

/** A value property in an object literal. */
class ValueProperty extends Property, @value_property {
}

/** A property getter or setter in an object literal. */
class PropertyAccessor extends Property, @property_accessor {
  /* covariant override to reflect the fact that accessors are functions */
  FunctionExpr getInit() {
    result = Property.super.getInit()
  }
}

/** A property getter in an object literal. */
class PropertyGetter extends PropertyAccessor, @property_getter {
}

/** A property setter in an object literal. */
class PropertySetter extends PropertyAccessor, @property_setter {
}

/**
 * A spread property in an object literal, such as `...others` in
 * `{ x: 42, ...others }`. The value of a spread property is always
 * a `SpreadElement`.
 */
class SpreadProperty extends Property {
  SpreadProperty() {
    not exists(getNameExpr())
  }
}

/** A function expression. */
class FunctionExpr extends @functionexpr, Expr, Function {
  /** Get the name of this function expression, if any. */
  string getName() {
    result = getId().getName()
  }
  
  /** Is this function expression a property setter? */
  predicate isSetter() {
    exists (PropertySetter s | s.getInit() = this)
  }

  /** Is this function expression a property getter? */
  predicate isGetter() {
    exists (PropertyGetter g | g.getInit() = this)
  }
  
  /** Is this function expression a property accessor? */
  predicate isAccessor() {
    exists (PropertyAccessor acc | acc.getInit() = this)
  }

  /** Get the JSDoc documentation for this function, if any. */
  JSDoc getDocumentation() {
    result = Expr.super.getDocumentation()
  }
  
  Stmt getEnclosingStmt() {
    result = Expr.super.getEnclosingStmt()
  }

  StmtContainer getEnclosingContainer() {
    result = Expr.super.getContainer()
  }
  
  predicate isImpure() {
    none()
  }

  string toString() {
    result = Expr.super.toString()
  }
}

/** An arrow expression. */
class ArrowFunctionExpr extends @arrowfunctionexpr, Expr, Function {
  /** Get the statement in which this expression appears. */
  Stmt getEnclosingStmt() {
    result = Expr.super.getEnclosingStmt()
  }

  StmtContainer getEnclosingContainer() {
    result = Expr.super.getContainer()
  }
  
  /** Get the JSDoc documentation for this function, if any. */
  JSDoc getDocumentation() {
    result = Expr.super.getDocumentation()
  }
  
  predicate isImpure() {
    none()
  }

  string toString() {
    result = Expr.super.toString()
  }
}

/** A sequence expression (also known as comma expression). */
class SeqExpr extends @seqexpr, Expr {
  /** Get the i-th expression in this sequence. */
  Expr getOperand(int i) {
    result = getChildExpr(i)
  }
  
  /** Get some expression in this sequence. */
  Expr getAnOperand() {
    result = getOperand(_)
  }
  
  /** Get the number of expressions in this sequence. */
  int getNumOperands() {
    result = count(getOperand(_))
  }

  /** Get the last expression in this sequence. */
  Expr getLastOperand() {
    result = getOperand(getNumOperands()-1)
  }
  
  predicate isImpure() {
    getAnOperand().isImpure()
  }

  string getStringValue() {
    result = getLastOperand().getStringValue()
  }
}

/** A conditional expression. */
class ConditionalExpr extends @conditionalexpr, Expr {
  /** Get the condition expression of this conditional. */
  Expr getCondition() {
    result = getChildExpr(0)
  }
  
  /** Get the "then" expression of this conditional. */
  Expr getConsequent() {
    result = getChildExpr(1)
  }
  
  /** Get the "else" expression of this conditional. */
  Expr getAlternate() {
    result = getChildExpr(2)
  }
 
  /** Get either the "then" or the "else" expression of this conditional. */
  Expr getABranch() {
    result = getConsequent() or result = getAlternate()
  }
  
  predicate isImpure() {
    getCondition().isImpure() or
    getABranch().isImpure()
  }
}

/** An invocation expression, that is, either a function call or
 * a `new` expression. */
class InvokeExpr extends @invokeexpr, Expr {
  /** Get the expression specifying the function to be called. */
  Expr getCallee() {
    result = this.getChildExpr(-1)
  }
  
  /** Return the name of the function or method being invoked, if it can be determined. */
  string getCalleeName() {
    exists (Expr callee | callee = getCallee().stripParens() |
      result = ((Identifier)callee).getName() or
      result = ((PropAccess)callee).getPropertyName()
    )
  }
  
  /** Get the i-th argument of this invocation. */
  Expr getArgument(int i) {
    i >= 0 and result = this.getChildExpr(i)
  }
  
  /** Get some argument of this invocation. */
  Expr getAnArgument() {
    result = getArgument(_)
  }
  
  /** Get the number of arguments of this invocation. */
  int getNumArgument() {
    result = count(getAnArgument())
  }

  CFGNode getFirstCFGNode() {
    result = getCallee().getFirstCFGNode()
  }

  /** Does the argument list of this function have a trailing comma? */
  predicate hasTrailingComma() {
    // check whether the last token of this invocation is a closing
    // parenthesis, which itself is preceded by a comma
    exists (PunctuatorToken rparen | rparen.getValue() = ")" |
      rparen = getLastToken() and
      rparen.getPreviousToken().getValue() = ","
    )
  }
}

/** A `new` expression. */
class NewExpr extends @newexpr, InvokeExpr {}

/** A function call expression. */
class CallExpr extends @callexpr, InvokeExpr {
  /** Get the expression specifying the receiver on which the function
   * is invoked, if any. */
  Expr getReceiver() {
    result = ((PropAccess)getCallee()).getBase()
  }
}

/** A method call expression. */
class MethodCallExpr extends CallExpr {
  MethodCallExpr() {
    getCallee().stripParens() instanceof PropAccess
  }

  /**
   * Get the property access referencing the method to be invoked.
   */
  private PropAccess getMethodRef() {
    result = getCallee().stripParens()
  }

  /**
   * Get the receiver expression of this method call.
   */
  Expr getReceiver() {
    result = getMethodRef().getBase()
  }

  /**
   * Get the name of the invoked method, if it can be determined.
   */
  string getMethodName() {
    result = getMethodRef().getPropertyName()
  }
}

/** A property access, that is, either a dot expression of the form
 * `e.f` or an index expression of the form `e[p]`. */
class PropAccess extends @propaccess, Expr {
  /** Get the base expression on which the property is accessed. */
  Expr getBase() {
    result = getChildExpr(0)
  }
  
  /** Get the name of the accessed property, if it can be determined. */
  string getPropertyName() {
    none()
  }

  /** Get the qualified name of the accessed property, if it can be determined. */
  string getQualifiedName() {
    exists (string basename |
      basename = getBase().(Identifier).getName() or
      basename = getBase().(PropAccess).getQualifiedName() |
      result = basename + "." + getPropertyName()
    )
  }

  CFGNode getFirstCFGNode() {
    result = getBase().getFirstCFGNode()
  }
}

/** A dot expression. */
class DotExpr extends @dotexpr, PropAccess {
  string getPropertyName() {
    result = ((Identifier)getChildExpr(1)).getName()
  }
  
  /** Get the identifier specifying the name of the accessed property. */
  Identifier getProperty() {
   result = getChildExpr(1)
  }
  
  predicate isImpure() {
    getBase().isImpure()
  }
}

/** An index expression (also known as computed property access). */
class IndexExpr extends @indexexpr, PropAccess {
  /** Get the expression specifying the name of the accessed property. */
  Expr getIndex() {
    result = getChildExpr(1)
  }
  
  string getPropertyName() {
    result = ((Literal)getIndex()).getValue()
  }
  
  predicate isImpure() {
    getBase().isImpure() or
    getIndex().isImpure()
  }
}

/* Unary operators */

/** An expression with a unary operator. */
class UnaryExpr extends @unaryexpr, Expr {
  /** Get the operand of the unary operator. */
  Expr getOperand() {
    result = getChildExpr(0)
  }
  
  /** Get the operator of this expression. */
  string getOperator() {
    none()
  }
  
  predicate isImpure() {
    getOperand().isImpure()
  }

  CFGNode getFirstCFGNode() {
    result = getOperand().getFirstCFGNode()
  }
}

/** An arithmetic negation expression (also known as unary minus). */
class NegExpr extends @negexpr, UnaryExpr {
  string getOperator() {
    result = "-"
  }
}

/** A unary plus expression. */
class PlusExpr extends @plusexpr, UnaryExpr {
  string getOperator() {
    result = "+"
  }
}

/** A logical negation expression. */
class LogNotExpr extends @lognotexpr, UnaryExpr {
  string getOperator() {
    result = "!"
  }
}

/** A bitwise negation expression. */
class BitNotExpr extends @bitnotexpr, UnaryExpr {
  string getOperator() {
    result = "~"
  }
}

/** A `typeof` expression. */
class TypeofExpr extends @typeofexpr, UnaryExpr {
  string getOperator() {
    result = "typeof"
  }
}

/** A `void` expression. */
class VoidExpr extends @voidexpr, UnaryExpr {
  string getOperator() {
    result = "void"
  }
}

/** A `delete` expression. */
class DeleteExpr extends @deleteexpr, UnaryExpr {
  string getOperator() {
    result = "delete"
  }
  
  predicate isImpure() {
    any()
  }
}

/** A spread element. */
class SpreadElement extends @spreadelement, UnaryExpr {
  string getOperator() {
    result = "..."
  }
}

/* Binary Operators */

/** An expression with a binary operator. */
class BinaryExpr extends @binaryexpr, Expr {
  /** Get the left operand of the binary operator. */
  Expr getLeftOperand() {
    result = getChildExpr(0)
  }
  
  /** Get the right operand of the binary operator. */
  Expr getRightOperand() {
    result = getChildExpr(1)
  }
  
  /** Get some operand of the binary operator. */
  Expr getAnOperand() {
    result = getAChildExpr()
  }

  /** Are e and f (in either order) the two operands of this expression? */
  predicate hasOperands(Expr e, Expr f) {
    e = getAnOperand() and
    f = getAnOperand() and
    e != f
  }
  
  /** Get the operator of this expression. */
  string getOperator() {
    none()
  }
  
  predicate isImpure() {
    getAnOperand().isImpure()
  }

  CFGNode getFirstCFGNode() {
    result = getLeftOperand().getFirstCFGNode()
  }
}

/** A comparison expression, that is, either an equality test
 * (`==`, `!=`, `===`, `!==`) or a relational expression
 * (`<`, `<=`, `>=`, `>`). */
class Comparison extends @comparison, BinaryExpr {}

/** An equality test using `==`, `!=`, `===` or `!==`. */
class EqualityTest extends @equalitytest, Comparison {}

/** An equality test using `==`. */
class EqExpr extends @eqexpr, EqualityTest {
  string getOperator() {
    result = "=="
  }
}

/** An inequality test using `!=`. */
class NEqExpr extends @neqexpr, EqualityTest {
  string getOperator() {
    result = "!="
  }
}

/** A strict equality test using `===`. */
class StrictEqExpr extends @eqqexpr, EqualityTest {
  string getOperator() {
    result = "==="
  }
}

/** A strict inequality test using `!==`. */
class StrictNEqExpr extends @neqqexpr, EqualityTest {
  string getOperator() {
    result = "!=="
  }
}

/** A less-than expression. */
class LTExpr extends @ltexpr, Comparison {
  string getOperator() {
    result = "<"
  }
}

/** A less-than-or-equal expression. */
class LEExpr extends @leexpr, Comparison {
  string getOperator() {
    result = "<="
  }
}

/** A greater-than expression. */
class GTExpr extends @gtexpr, Comparison {
  string getOperator() {
    result = ">"
  }
}

/** A greater-than-or-equal expression. */
class GEExpr extends @geexpr, Comparison {
  string getOperator() {
    result = ">="
  }
}

/** A left-shift expression using `<<`. */
class LShiftExpr extends @lshiftexpr, BinaryExpr {
  string getOperator() {
    result = "<<"
  }
}

/** A right-shift expression using `>>`. */
class RShiftExpr extends @rshiftexpr, BinaryExpr {
  string getOperator() {
    result = ">>"
  }
}

/** An unsigned right-shift expression using `>>>`. */
class URShiftExpr extends @urshiftexpr, BinaryExpr {
  string getOperator() {
    result = ">>>"
  }
}

/** An addition expression. */
class AddExpr extends @addexpr, BinaryExpr {
  string getOperator() {
    result = "+"
  }

  string getStringValue() {
    result = getLeftOperand().getStringValue() + getRightOperand().getStringValue()
  }
}

/** A subtraction expression. */
class SubExpr extends @subexpr, BinaryExpr {
  string getOperator() {
    result = "-"
  }
}

/** A multiplication expression. */
class MulExpr extends @mulexpr, BinaryExpr {
  string getOperator() {
    result = "*"
  }
}

/** A division expression. */
class DivExpr extends @divexpr, BinaryExpr {
  string getOperator() {
    result = "/"
  }
}

/** A modulo expression. */
class ModExpr extends @modexpr, BinaryExpr {
  string getOperator() {
    result = "%"
  }
}

/** An exponentiation expression. */
class ExpExpr extends @expexpr, BinaryExpr {
  string getOperator() {
    result = "**"
  }
}

/** A bitwise or expression. */
class BitOrExpr extends @bitorexpr, BinaryExpr {
  string getOperator() {
    result = "|"
  }
}

/** An exclusive-or expression. */
class XOrExpr extends @xorexpr, BinaryExpr {
  string getOperator() {
    result = "^"
  }
}

/** A bitwise and expression. */
class BitAndExpr extends @bitandexpr, BinaryExpr {
  string getOperator() {
    result = "&"
  }
}

/** An `in` expression. */
class InExpr extends @inexpr, BinaryExpr {
  string getOperator() {
    result = "in"
  }
}

/** An `instanceof` expression. */
class InstanceofExpr extends @instanceofexpr, BinaryExpr {
  string getOperator() {
    result = "instanceof"
  }
}

/** A logical and expression. */
class LogAndExpr extends @logandexpr, BinaryExpr {
  string getOperator() {
    result = "&&"
  }

  CFGNode getFirstCFGNode() { result = this }
}

/** A logical or expression. */
class LogOrExpr extends @logorexpr, BinaryExpr {
  string getOperator() {
    result = "||"
  }

  CFGNode getFirstCFGNode() { result = this }
}

/** A logical binary expression, that is, either a logical
 * or or a logical and expression. */
class LogicalBinaryExpr extends BinaryExpr {
  LogicalBinaryExpr() {
    this instanceof LogAndExpr or
    this instanceof LogOrExpr
  }
}

/** A bitwise binary expression, that is, either a bitwise
 * and, a bitwise or, or an exclusive-or expression. */
class BitwiseBinaryExpr extends BinaryExpr {
  BitwiseBinaryExpr() {
    this instanceof BitAndExpr or
    this instanceof BitOrExpr or
    this instanceof XOrExpr
  }
}

/** A shift expression. */
class ShiftExpr extends BinaryExpr {
  ShiftExpr() {
    this instanceof LShiftExpr or
    this instanceof RShiftExpr or
    this instanceof URShiftExpr
  }
}

/* Assignments */

/** An assignment expression, either compound or simple. */
class Assignment extends @assignment, Expr {
  /** Get the left hand side of this assignment. */
  Expr getLhs() {
    result = getChildExpr(0)
  }
  
  /** Get the right hand side of this assignment. */
  Expr getRhs() {
    result = getChildExpr(1)
  }

  /** Get the variable or property this assignment writes to, if any. */
  Expr getTarget() {
    result = getLhs().stripParens()
  }

  CFGNode getFirstCFGNode() {
    result = getLhs().getFirstCFGNode()
  }
}

/** A simple assignment expression. */
class AssignExpr extends @assignexpr, Assignment {}

/** A compound assign expression. */
abstract class CompoundAssignExpr extends Assignment {}

/** A compound add-assign expression. */
class AssignAddExpr extends @assignaddexpr, CompoundAssignExpr {}

/** A compound subtract-assign expression. */
class AssignSubExpr extends @assignsubexpr, CompoundAssignExpr {}

/** A compound multiply-assign expression. */
class AssignMulExpr extends @assignmulexpr, CompoundAssignExpr {}

/** A compound divide-assign expression. */
class AssignDivExpr extends @assigndivexpr, CompoundAssignExpr {}

/** A compound modulo-assign expression. */
class AssignModExpr extends @assignmodexpr, CompoundAssignExpr {}

/** A compound exponentiate-assign expression. */
class AssignExpExpr extends @assignexpexpr, CompoundAssignExpr {}

/** A compound left-shift-assign expression. */
class AssignLShiftExpr extends @assignlshiftexpr, CompoundAssignExpr {}

/** A compound right-shift-assign expression. */
class AssignRShiftExpr extends @assignrshiftexpr, CompoundAssignExpr {}

/** A compound unsigned-right-shift-assign expression. */
class AssignURShiftExpr extends @assignurshiftexpr, CompoundAssignExpr {}

/** A compound bitwise-or-assign expression. */
class AssignOrExpr extends @assignorexpr, CompoundAssignExpr {}

/** A compound exclusive-or-assign expression. */
class AssignXOrExpr extends @assignxorexpr, CompoundAssignExpr {}

/** A compound bitwise-and-assign expression. */
class AssignAndExpr extends @assignandexpr, CompoundAssignExpr {}

/* Update operators */

/** An update expression, that is, an increment or decrement expression. */
class UpdateExpr extends @updateexpr, Expr {
  /** Get the operand of the update .*/
  Expr getOperand() {
    result = getChildExpr(0)
  }
  
  /** Is this a prefix increment or prefix decrement? */
  predicate isPrefix() {
    none()
  }
  
  /** Get the operator of this update expression. */
  string getOperator() {
    none()
  }

  CFGNode getFirstCFGNode() {
    result = getOperand().getFirstCFGNode()
  }
}

/** A prefix increment expression. */
class PreIncExpr extends @preincexpr, UpdateExpr {
  predicate isPrefix() {
    any()
  }
  
  string getOperator() {
    result = "++"
  }
}

/** A postfix increment expression. */
class PostIncExpr extends @postincexpr, UpdateExpr {
  string getOperator() {
    result = "++"
  }
}

/** A prefix decrement expression. */
class PreDecExpr extends @predecexpr, UpdateExpr {
  predicate isPrefix() {
    any()
  }
  
  string getOperator() {
    result = "--"
  }
}

/** A postfix decrement expression. */
class PostDecExpr extends @postdecexpr, UpdateExpr {
  string getOperator() {
    result = "--"
  }
}

/** A yield expression. */
class YieldExpr extends @yieldexpr, Expr {
  /** Get the operand of the yield expression. */
  Expr getOperand() {
    result = getChildExpr(0)
  }

  /** Is this a `yield*` expression? */
  predicate isDelegating() {
    isDelegating(this)
  }

  predicate isImpure() {
    any()
  }

  CFGNode getFirstCFGNode() {
    result = getOperand().getFirstCFGNode()
  }
}

/**
 * A comprehension expression, that is, either an array comprehension
 * expression or a generator expression.
 */
class ComprehensionExpr extends @comprehensionexpr, Expr {
  /** Get the n'th comprehension block in this comprehension. */
  ComprehensionBlock getBlock(int n) {
    exists (int idx |
      result = getChildExpr(idx) and
      idx > 0 and
      n = idx-1
    )
  }

  /** Get some comprehension block in this comprehension. */
  ComprehensionBlock getABlock() {
    result = getBlock(_)
  }

  /** Get the number of comprehension blocks in this comprehension. */
  int getNumBlock() {
    result = count(getABlock())
  }

  /** Get the n'th filter expression in this comprehension. */
  Expr getFilter(int n) {
    exists (int idx |
      result = getChildExpr(idx) and
      idx < 0 and
      n = -idx-1
    )
  }

  /** Get some filter expression in this comprehension. */
  Expr getAFilter() {
    result = getFilter(_)
  }

  /** Get the number of filter expressions in this comprehension. */
  int getNumFilter() {
    result = count(getAFilter())
  }

  /** Get the body expression of this comprehension. */
  Expr getBody() {
    result = getChildExpr(0)
  }

  predicate isImpure() {
    getABlock().isImpure() or
    getAFilter().isImpure() or
    getBody().isImpure()
  }

  /** Is this a legacy postfix comprehension expression? */
  predicate isPostfix() {
    exists (Token tk | tk = getFirstToken().getNextToken() |
      not tk.getValue().regexpMatch("if|for")
    )
  }
}

/** An array comprehension expression. */
class ArrayComprehensionExpr extends @arraycomprehensionexpr, ComprehensionExpr {
}

/** A generator expression. */
class GeneratorExpr extends @generatorexpr, ComprehensionExpr {
}

/** A comprehension block. */
class ComprehensionBlock extends @comprehensionblock, Expr {
  /** Get the iterating variable or pattern of this comprehension block. */
  BindingPattern getIterator() {
    result = getChildExpr(0)
  }

  /** Get the domain over which this comprehension block iterates. */
  Expr getDomain() {
    result = getChildExpr(1)
  }

  predicate isImpure() {
    getIterator().isImpure() or
    getDomain().isImpure()
  }
}

/** A for-in comprehension block. */
class ForInComprehensionBlock extends @forincomprehensionblock, ComprehensionBlock {
}

/** A for-of comprehension block. */
class ForOfComprehensionBlock extends @forofcomprehensionblock, ComprehensionBlock {
}

/** A binary arithmetic expression using `+`, `-`, `/`, or `%`. */
class ArithmeticExpr extends BinaryExpr {
  ArithmeticExpr() {
    this instanceof AddExpr or
    this instanceof SubExpr or
    this instanceof MulExpr or
    this instanceof DivExpr or
    this instanceof ModExpr
  }
}

/** A logical expression using `&&`, `||`, or `!`. */
class LogicalExpr extends Expr {
  LogicalExpr() {
    this instanceof LogicalBinaryExpr or
    this instanceof LogNotExpr
  }
}

/** A bitwise expression using `&`, `|`, `^`, `~`, `<<`, `>>`, or `>>>`. */
class BitwiseExpr extends Expr {
  BitwiseExpr() {
    this instanceof BitwiseBinaryExpr or
    this instanceof BitNotExpr or
    this instanceof ShiftExpr
  }
}

/** A strict equality test using `!==` or `===`. */
class StrictEqualityTest extends EqualityTest {
  StrictEqualityTest() {
    this instanceof StrictEqExpr or
    this instanceof StrictNEqExpr
  }
}

/** A non-strict equality test using `!=` or `==`. */
class NonStrictEqualityTest extends EqualityTest {
  NonStrictEqualityTest() {
    this instanceof EqExpr or
    this instanceof NEqExpr
  }
}

/** A relational comparison using `<`, `<=`, `>=`, or `>`. */
class RelationalComparison extends Comparison {
  RelationalComparison() {
    this instanceof LTExpr or
    this instanceof LEExpr or
    this instanceof GEExpr or
    this instanceof GTExpr
  }

  /**
   * Get the lesser operand of this comparison, that is, the left operand for
   * a `<` or `<=` comparison, and the right operand for `>=` or `>`.
   */
  Expr getLesserOperand() {
    (this instanceof LTExpr or this instanceof LEExpr) and result = getLeftOperand() or
    (this instanceof GTExpr or this instanceof GEExpr) and result = getRightOperand()
  }

  /**
   * Get the greater operand of this comparison, that is, the right operand for
   * a `<` or `<=` comparison, and the left operand for `>=` or `>`.
   */
  Expr getGreaterOperand() {
    result = getAnOperand() and result != getLesserOperand()
  }
}

/** A (pre or post) increment expression. */
class IncExpr extends UpdateExpr {
  IncExpr() { this instanceof PreIncExpr or this instanceof PostIncExpr }
}

/** A (pre or post) decrement expression. */
class DecExpr extends UpdateExpr {
  DecExpr() { this instanceof PreDecExpr or this instanceof PostDecExpr }
}


/** An old-style let expression of the form `let(vardecls) expr`. */
class LegacyLetExpr extends Expr, @legacy_letexpr {
  /** Get the i-th declarator in this let expression. */
  VariableDeclarator getDecl(int i) {
    result = getChildExpr(i) and i >= 0
  }
  
  /** Get some declarator in this declaration statement. */
  VariableDeclarator getADecl() {
    result = getDecl(_)
  }

  /** Get the expression this let expression scopes over. */
  Expr getBody() {
    result = getChildExpr(-1)
  }
}

/**
 * A helper predicate that binds `invk` to an immediate invocation of
 * function `f`, and kind to a string describing how `invk`
 * invokes `f`:
 *
 * - if `invk` is a direct function call, `kind` is `"direct"`;
 * - if `invk` is a reflective function call through `call` or `apply`,
 *   `kind` is `"call"` or `"apply"`, respectively.
 */
private predicate iife(InvokeExpr invk, Function f, string kind) {
  // direct call
  f = invk.getCallee().stripParens() and kind = "direct" or
  // reflective call
  exists (MethodCallExpr mce | mce = invk |
    f = mce.getReceiver().stripParens() and
    kind = mce.getMethodName() and
    (kind = "call" or kind = "apply")
  )
}

/** An immediately invoked function expression (IIFE). */
class ImmediatelyInvokedFunctionExpr extends Function {
  ImmediatelyInvokedFunctionExpr() {
    iife(_, this, _)
  }

  /** Get the invocation of this IIFE. */
  InvokeExpr getInvocation() {
    iife(result, this, _)
  }

  /** Bind p to a parameter of the IIFE and arg to the corresponding argument. */
  predicate argumentPassing(SimpleParameter p, Expr arg) {
    exists (int i, InvokeExpr invk, string kind |
      p = getParameter(i) and not p.isRestParameter() and
      iife(invk, this, kind) |
      kind = "direct" and arg = invk.getArgument(i) or
      kind = "call" and arg = invk.getArgument(i+1)
    )
  }
}

/** An await expression. */
class AwaitExpr extends @awaitexpr, Expr {
  /** Get the operand of the await expression. */
  Expr getOperand() {
    result = getChildExpr(0)
  }

  predicate isImpure() {
    any()
  }

  CFGNode getFirstCFGNode() {
    result = getOperand().getFirstCFGNode()
  }
}

/**
 * A `function.sent` expression.
 *
 * Inside a generator function, `function.sent` evaluates to the value passed
 * to the generator by the `next` method that most recently resumed execution
 * of the generator.
 */
class FunctionSentExpr extends @functionsentexpr, Expr {
  predicate isImpure() {
    none()
  }
}

/**
 * A decorator applied to a class, property or member definition.
 *
 * For example, in the class declaration `@A class C { }`,
 * `@A` is a decorator applied to class `C`.
 */
class Decorator extends @decorator, Expr {
  /**
   * The element the decorator is applied to.
   *
   * For example, in the class declaration `@A class C { }`,
   * the element decorator `@A` is applied to is `C`.
   */
  Decoratable getElement() {
    this = result.getADecorator()
  }

  /**
   * The expression of the decorator.
   *
   * For example, the decorator `@A` has expression `A`,
   * and `@testable(true)` has expression `testable(true)`.
   */
  Expr getExpression() {
    result = getChildExpr(0)
  }

  CFGNode getFirstCFGNode() {
    result = getExpression().getFirstCFGNode()
  }
}

/**
 * A program element to which decorators can be applied,
 * that is, a class, a property or a member definition.
 */
class Decoratable extends ASTNode {
  Decoratable() {
    this instanceof Class or
    this instanceof Property or
    this instanceof MemberDefinition
  }

  /**
   * The `i`-th decorator applied to this element.
   */
  Decorator getDecorator(int i) {
    result = this.(Class).getDecorator(i) or
    result = this.(Property).getDecorator(i) or
    result = this.(MemberDefinition).getDecorator(i)
  }

  /**
   * A decorator applied to this element, if any.
   */
  Decorator getADecorator() {
    result = this.getDecorator(_)
  }
}

/**
 * A function bind expression either of the form `b::f`, or of the
 * form `::b.f`.
 */
class FunctionBindExpr extends @bindexpr, Expr {
  /**
   * The object of the function bind expression; undefined for
   * expressions of the form `::b.f`.
   */
  Expr getObject() {
    result = getChildExpr(0)
  }

  /**
   * The callee of the function bind expression.
   */
  Expr getCallee() {
    result = getChildExpr(1)
  }

  CFGNode getFirstCFGNode() {
    result = getObject().getFirstCFGNode() or
    not exists(getObject()) and result = getCallee().getFirstCFGNode()
  }
}