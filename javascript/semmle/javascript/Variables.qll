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

/** Provides classes for modeling program variables. */

import Expr
import Locations
import Functions

/** A scope in which variables can be declared. */
class Scope extends @scope {
  /** Gets a textual representation of this element. */
  string toString() {
    none()
  }

  /** Gets the scope in which this scope is nested, if any. */
  Scope getOuterScope() {
    scopenesting(this, result)
  }

  /** Gets a scope nested in this one, if any. */
  Scope getAnInnerScope() {
    result.getOuterScope() = this
  }

  /** Gets the program element this scope is associated with, if any. */
  ASTNode getScopeElement() {
    scopenodes(result, this)
  }

  /** Gets the location of the program element this scope is associated with, if any. */
  Location getLocation() {
    result = getScopeElement().getLocation()
  }

  /** Gets a variable declared in this scope. */
  Variable getAVariable() {
    result.getScope() = this
  }

  /** Gets the variable with the given name declared in this scope. */
  Variable getVariable(string name) {
    result = getAVariable() and
    result.getName() = name
  }
}

/** The global scope. */
class GlobalScope extends Scope, @globalscope {
  override string toString() {
    result = "global scope"
  }
}

/**
 * A scope induced by a Node.js or ES2015 module
 */
class ModuleScope extends Scope, @modulescope {
  /** Gets the module that induces this scope. */
  Module getModule() {
    result = getScopeElement()
  }

  override string toString() {
    result = "module scope"
  }
}

/** A scope induced by a function. */
class FunctionScope extends Scope, @functionscope {
  /** Gets the function that induces this scope. */
  Function getFunction() {
    result = getScopeElement()
  }

  override string toString() {
    result = "function scope"
  }
}

/** A scope induced by a catch clause. */
class CatchScope extends Scope, @catchscope {
  /** Gets the catch clause that induces this scope. */
  CatchClause getCatchClause() {
    result = getScopeElement()
  }

  override string toString() {
    result = "catch scope"
  }
}

/** A scope induced by a block of statements. */
class BlockScope extends Scope, @blockscope {
  /** Gets the block of statements that induces this scope. */
  BlockStmt getBlock() {
    result = getScopeElement()
  }

  override string toString() {
    result = "block scope"
  }
}

/** A scope induced by a `for` statement. */
class ForScope extends Scope, @forscope {
  /** Gets the `for` statement that induces this scope. */
  ForStmt getLoop() {
    result = getScopeElement()
  }

  override string toString() {
    result = "for scope"
  }
}

/** A scope induced by a `for`-`in` or `for`-`of` statement. */
class ForInScope extends Scope, @forinscope {
  /** Gets the `for`-`in` or `for`-`of` statement that induces this scope. */
  EnhancedForLoop getLoop() {
    result = getScopeElement()
  }

  override string toString() {
    result = "for-in scope"
  }
}

/** A scope induced by a comprehension block. */
class ComprehensionBlockScope extends Scope, @comprehensionblockscope {
  /** Gets the comprehension block that induces this scope. */
  ComprehensionBlock getComprehensionBlock() {
    result = getScopeElement()
  }

  override string toString() {
    result = "comprehension block scope"
  }
}

/** A variable declared in a scope. */
class Variable extends @variable {
  /** Gets the name of this variable. */
  string getName() {
    variables(this, result, _)
  }

  /** Gets the scope this variable is declared in. */
  Scope getScope() {
    variables(this, _, result)
  }

  /** Holds if this is a global variable. */
  predicate isGlobal() {
    getScope() instanceof GlobalScope
  }

  /**
   * Holds if this is a local variable.
   *
   * Parameters and `arguments` variables are considered to be local.
   */
  predicate isLocal() {
    not isGlobal()
  }

  /** Holds if this variable is a parameter. */
  predicate isParameter() {
    exists (Parameter p | p.getAVariable() = this)
  }

  /** Gets an access to this variable. */
  VarAccess getAnAccess() {
    result.getVariable() = this
  }

  /** Gets a declaration declaring this variable, if any. */
  VarDecl getADeclaration() {
    result.getVariable() = this
  }

  /** Gets a declaration statement declaring this variable, if any. */
  DeclStmt getADeclarationStatement() {
    result.getADecl().getBindingPattern().getAVariable() = this
  }

  /** Gets an expression that is directly stored in this variable. */
  Expr getAnAssignedValue() {
    // result is an expression that this variable is initialized to
    exists (VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getVariable() = this |
      result = vd.getInit()
    ) or
    // if this variable represents a function binding, return the function
    exists (Function fn | fn.getVariable() = this | result = fn) or
    // there is an assignment to this variable
    exists (Assignment assgn | assgn.getLhs() = getAnAccess() and assgn.getRhs() = result)
  }

  /**
   * Holds if this variable is captured in the closure of a nested function.
   *
   * Global variables are always considered to be captured.
   */
  predicate isCaptured() {
    this instanceof GlobalVariable or
    getAnAccess().getContainer() != this.(LocalVariable).getDeclaringContainer()
  }

  /** Holds if there is a declaration of this variable in `tl`. */
  predicate declaredIn(TopLevel tl) {
    getADeclaration().getTopLevel() = tl
  }

  /** Gets a textual representation of this element. */
  string toString() {
    result = getName()
  }
}

/** An `arguments` variable of a function. */
class ArgumentsVariable extends Variable {
  ArgumentsVariable() {
    isArgumentsObject(this)
  }

  override FunctionScope getScope() {
    result = Variable.super.getScope()
  }

  /** Gets the function declaring this 'arguments' variable. */
  Function getFunction() {
    result = getScope().getFunction()
  }
}

/**
 * DEPRECATED: Use `ArgumentsVariable` instead.
 *
 * An `arguments` variable of a function.
 */
deprecated class ArgumentsObject extends ArgumentsVariable {}

/** An identifier that refers to a variable, either in a declaration or in a variable access. */
abstract class VarRef extends @varref, Identifier, BindingPattern {
  /** Gets the variable this identifier refers to. */
  abstract Variable getVariable();

  override VarRef getABindingVarRef() { result = this }
}

/** An identifier that refers to a variable in a non-declaring position. */
class VarAccess extends @varaccess, VarRef {
  override Variable getVariable() {
    bind(this, result)
  }

  override predicate isLValue() {
    exists (Assignment assgn | assgn.getTarget() = this) or
    exists (UpdateExpr upd | upd.getOperand().stripParens() = this) or
    exists (EnhancedForLoop efl | efl.getIterator() = this) or
    exists (BindingPattern p | this = p.getABindingVarRef() and p.isLValue())
  }

  override Variable getAVariable() {
    result = getVariable()
  }
}

/** A global variable. */
class GlobalVariable extends Variable {
  GlobalVariable() {
    isGlobal()
  }
}

/** A local variable or a parameter. */
class LocalVariable extends Variable {
  LocalVariable() {
    isLocal()
  }

  /**
   * Gets the function or toplevel in which this variable is declared;
   * `arguments` variables are taken to be implicitly declared in the function
   * to which they belong.
   *
   * Note that for a function expression `function f() { ... }` the variable
   * `f` is declared in the function itself, while for a function statement
   * it is declared in the enclosing container.
   */
  StmtContainer getDeclaringContainer() {
    this = result.getScope().getAVariable() or
    exists (VarDecl d | d = getADeclaration() |
      if d = any(FunctionDeclStmt fds).getId() then
        exists (FunctionDeclStmt fds | d = fds.getId() |
          result = fds.getEnclosingContainer()
        )
      else
        result = d.getContainer()
    )
  }
}

/** A local variable that is not captured. */
class PurelyLocalVariable extends LocalVariable {
  PurelyLocalVariable() {
    not isCaptured()
  }
}

/** An identifier that refers to a global variable. */
class GlobalVarAccess extends VarAccess {
  GlobalVarAccess() {
    getVariable().isGlobal()
  }
}

/**
 * A binding pattern, i.e., either an identifier or a destructuring pattern.
 *
 * Binding patterns can appear on the left hand side of assignments or in
 * variable or parameter declarations. They bind one or more variables to
 * values, either by means of a regular assignment as in `x = 42`, or
 * through a destructuring assignment as in `[x, y] = a`; see Chapter 12 of
 * the ECMAScript standard for more details.
 */
class BindingPattern extends @pattern, Expr {
  /** Gets a variable reference in binding position within this pattern. */
  VarRef getABindingVarRef() { none() }

  /** Gets a variable bound by this pattern. */
  Variable getAVariable() { result = getABindingVarRef().getVariable() }

  /** Holds if this pattern appears in an l-value position. */
  predicate isLValue() {
    any()
  }
}

/** A destructuring pattern, that is, either an array pattern or an object pattern. */
abstract class DestructuringPattern extends BindingPattern {
}

/** An identifier that declares a variable. */
class VarDecl extends @vardecl, VarRef {
  override Variable getVariable() {
    decl(this, result)
  }

  override predicate isLValue() {
    exists (VariableDeclarator vd | vd.getBindingPattern() = this |
      exists (vd.getInit()) or
      exists (EnhancedForLoop efl | this = efl.getIterator())
    ) or
    exists (BindingPattern p | this = p.getABindingVarRef() and p.isLValue())
  }
}

/** An identifier that declares a global variable. */
class GlobalVarDecl extends VarDecl {
  GlobalVarDecl() {
    getVariable() instanceof GlobalVariable
  }
}

/** An array pattern. */
class ArrayPattern extends DestructuringPattern, @arraypattern {
  /** Gets the `i`th element of this array pattern. */
  Expr getElement(int i) {
    i >= 0 and
    result = this.getChildExpr(i)
  }

  /** Gets an element of this array pattern. */
  Expr getAnElement() {
    exists (int i | i >= -1 | result = this.getChildExpr(i))
  }

  /** Gets the default expression for the `i`th element of this array pattern, if any. */
  Expr getDefault(int i) {
    i in [0..getSize()-1] and
    result = getChildExpr(-2 - i)
  }

  /** Holds if the `i`th element of this array pattern has a default expression. */
  predicate hasDefault(int i) {
    exists(getDefault(i))
  }

  /** Gets the rest pattern of this array pattern, if any. */
  Expr getRest() {
    result = getChildExpr(-1)
  }

  /** Holds if this array pattern has a rest pattern. */
  predicate hasRest() {
    exists(getRest())
  }

  /** Gets the number of elements in this array pattern, not including any rest pattern. */
  int getSize() {
    arraySize(this, result)
  }

  /** Holds if the `i`th element of this array pattern is omitted. */
  predicate elementIsOmitted(int i) {
    i in [0..getSize()-1] and
    not exists (getElement(i))
  }

  /** Holds if this array pattern has an omitted element. */
  predicate hasOmittedElement() {
    elementIsOmitted(_)
  }

  override predicate isImpure() {
    getAnElement().isImpure()
  }

  override VarRef getABindingVarRef() {
    result = getAnElement().(BindingPattern).getABindingVarRef()
  }
}

/** An object pattern. */
class ObjectPattern extends DestructuringPattern, @objectpattern {
  /** Gets the `i`th property pattern in this object pattern. */
  PropertyPattern getPropertyPattern(int i) {
    properties(result, this, i, _, _)
  }

  /** Gets a property pattern in this object pattern. */
  PropertyPattern getAPropertyPattern() {
    result = this.getPropertyPattern(_)
  }

  /** Gets the number of property patterns in this object pattern. */
  int getNumProperty() {
    result = count(this.getAPropertyPattern())
  }

  /** Gets the property pattern with the given name, if any. */
  PropertyPattern getPropertyPatternByName(string name) {
    result = this.getAPropertyPattern() and
    result.getName() = name
  }

  /** Gets the rest property pattern of this object pattern, if any. */
  Expr getRest() {
    result = getChildExpr(-1)
  }

  override predicate isImpure() {
    getAPropertyPattern().isImpure()
  }

  override VarRef getABindingVarRef() {
    result = getAPropertyPattern().getValuePattern().(BindingPattern).getABindingVarRef() or
    result = getRest().(BindingPattern).getABindingVarRef()
  }
}

/** A property pattern in an object pattern. */
class PropertyPattern extends @property, ASTNode {
  PropertyPattern() {
    // filter out ordinary properties
    exists (ObjectPattern obj | properties(this, obj, _, _, _))
  }

  /** Holds if the name of this property pattern is computed. */
  predicate isComputed() {
    isComputed(this)
  }

  /** Gets the expression specifying the name of the matched property. */
  Expr getNameExpr() {
    result = this.getChildExpr(0)
  }

  /** Gets the expression the matched property value is assigned to. */
  Expr getValuePattern() {
    result = this.getChildExpr(1)
  }

  /** Gets the default value of this property pattern, if any. */
  Expr getDefault() {
    result = this.getChildExpr(2)
  }

  /** Holds if this property pattern is a shorthand pattern. */
  predicate isShorthand() {
    getNameExpr().getLocation() = getValuePattern().getLocation()
  }

  /** Gets the name of the property matched by this pattern. */
  string getName() {
    (not isComputed() and
     result = ((Identifier)getNameExpr()).getName()) or
    result = ((Literal)getNameExpr()).getValue()
  }

  /** Gets the object pattern this property pattern belongs to. */
  ObjectPattern getObjectPattern() {
    properties(this, result, _, _, _)
  }

  /** Gets the nearest enclosing function or toplevel in which this property pattern occurs. */
  StmtContainer getContainer() {
    result = getObjectPattern().getContainer()
  }

  /** Holds if this pattern is impure, that is, if its evaluation could have side effects. */
  predicate isImpure() {
    (isComputed() and getNameExpr().isImpure()) or
    getValuePattern().isImpure()
  }

  override string toString() {
    properties(this, _, _, _, result)
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getNameExpr().getFirstControlFlowNode()
  }
}

/** A variable declarator declaring a local or global variable. */
class VariableDeclarator extends Expr, @vardeclarator {
  /** Gets the pattern specifying the declared variable(s). */
  BindingPattern getBindingPattern() {
    result = this.getChildExpr(0)
  }

  /** Gets the expression specifying the initial value of the declared variable(s), if any. */
  Expr getInit() {
    result = this.getChildExpr(1)
  }

  /** Gets the declaration statement this declarator belongs to, if any. */
  DeclStmt getDeclStmt() {
    this = result.getADecl()
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getBindingPattern().getFirstControlFlowNode()
  }
}

/**
 * A program element that declares parameters, that is, either a function or
 * a catch clause.
 */
class Parameterized extends @parameterized, ASTNode {
  /** Gets a parameter declared by this element. */
  Parameter getAParameter() {
    this = result.getParent()
  }

  /** Gets the number of parameters declared by this element. */
  int getNumParameter() {
    result = count(getAParameter())
  }

  /** Gets a variable of the given name that is a parameter of this element. */
  Variable getParameterVariable(string name) {
    result = getAParameter().getAVariable() and
    result.getName() = name
  }

  /** Gets the JSDoc comment attached to this element, if any. */
  abstract JSDoc getDocumentation();
}

/** A parameter declaration. */
class Parameter extends BindingPattern {
  Parameter() {
    exists (Parameterized p, int n |
      this = p.getChildExpr(n) and
      n >= 0
    )
  }

  /**
   * Gets the index of this parameter within the parameter list of its
   * declaring entity.
   */
  int getIndex() {
    exists (Parameterized p | this = p.getChildExpr(result))
  }

  /** Gets the element declaring this parameter. */
  override Parameterized getParent() {
    result = super.getParent()
  }

  /** Gets the default expression for this parameter, if any. */
  Expr getDefault() {
    exists (Function f, int n | this = f.getParameter(n) | result = f.getChildExpr(-(n+3)))
  }

  /** Holds if this parameter is a rest parameter. */
  predicate isRestParameter() {
    exists (Function f, int n | this = f.getParameter(n) |
      n = f.getNumParameter()-1 and
      f.hasRestParameter()
    )
  }

  override predicate isLValue() {
    any()
  }
}

/** A parameter declaration that is not an object or array pattern. */
class SimpleParameter extends Parameter, VarDecl {
  override predicate isLValue() { Parameter.super.isLValue() }
}
