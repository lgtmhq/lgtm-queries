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

import Expr
import Locations
import Functions

/** A scope in which variables can be declared. */
class Scope extends @scope {
  string toString() {
    none()
  }
  
  /** Get the scope in which this scope is nested, if any. */
  Scope getOuterScope() {
  	scopenesting(this, result)
  }
  
  /** Get a scope nested in this one, if any. */
  Scope getAnInnerScope() {
  	result.getOuterScope() = this
  }
  
  /** Get the program element this scope is associated with, if any. */
  ASTNode getScopeElement() {
  	scopenodes(result, this)
  }
  
  /** Get the location of the program element this scope is associated with, if any. */
  Location getLocation() {
    result = getScopeElement().getLocation()
  }

  /** Is there a strict mode declaration in this scope? */
  predicate isStrict() {
    exists (StrictModeDecl smd | this = smd.getScope())
  }
  
  /** Get a variable declared in this scope. */
  Variable getAVariable() {
    result.getScope() = this
  }
  
  /** Get the variable with the given name declared in this scope. */
  Variable getVariable(string name) {
  	result = getAVariable() and
  	result.getName() = name
  }
}

/** The global scope. */
class GlobalScope extends Scope, @globalscope {
  string toString() {
    result = "global scope"
  }
}

/**
 * The scope induced by a Node.js or ES6 module
 */
class ModuleScope extends Scope, @modulescope {
  /** Get the module to which this scope belongs. */
  Module getModule() {
    result = getScopeElement()
  }

  string toString() {
    result = "module scope"
  }
}

/** A scope induced by a function. */
class FunctionScope extends Scope, @functionscope {
  /** Get the function inducing this scope. */
  Function getFunction() {
    result = getScopeElement()
  }
  
  string toString() {
    result = "function scope"
  }
}

/** A scope induced by a catch clause. */
class CatchScope extends Scope, @catchscope {
  /** Get the catch scope inducing this scope. */
  CatchClause getCatchClause() {
    result = getScopeElement()
  }
  
  string toString() {
    result = "catch scope"
  }
}

/** A scope induced by a block of statements. */
class BlockScope extends Scope, @blockscope {
  /** Get the block of statements inducing this scope. */
  BlockStmt getBlock() {
    result = getScopeElement()
  }

  string toString() {
    result = "block scope"
  }
}

/** A scope induced by a for statements. */
class ForScope extends Scope, @forscope {
  /** Get the for statement inducing this scope. */
  ForStmt getLoop() {
    result = getScopeElement()
  }

  string toString() {
    result = "for scope"
  }
}

/** A scope induced by a for-in or for-of statements. */
class ForInScope extends Scope, @forinscope {
  /** Get the for-in or for-of statement inducing this scope. */
  EnhancedForLoop getLoop() {
    result = getScopeElement()
  }

  string toString() {
    result = "for-in scope"
  }
}

/** A scope induced by a comprehension block. */
class ComprehensionBlockScope extends Scope, @comprehensionblockscope {
  /** Get the comprehension block inducing this scope. */
  ComprehensionBlock getComprehensionBlock() {
    result = getScopeElement()
  }

  string toString() {
    result = "comprehension block scope"
  }
}

/** A variable declared in a scope. */
class Variable extends @variable {
  /** Get the name of this variable. */
  string getName() {
    variables(this, result, _)
  }
  
  /** Get the scope this variable is declared in. */
  Scope getScope() {
    variables(this, _, result)
  }
  
  /** Is this a global variable? */
  predicate isGlobal() {
    getScope() instanceof GlobalScope
  }

  /** Is this a local variable or a parameter? */
  predicate isLocal() {
    not isGlobal()
  }

  /** Is this variable a parameter? */
  predicate isParameter() {
    exists (Parameter p | p.getAVariable() = this)
  }

  /** Get an access to this variable. */
  VarAccess getAnAccess() {
  	result.getVariable() = this
  }
  
  /** Get a declaration declaring this variable, if any. */
  VarDecl getADeclaration() {
  	result.getVariable() = this
  }

  /** Get a declaration statement declaring this variable, if any. */
  DeclStmt getADeclarationStatement() {
    result.getADecl().getBindingPattern().getAVariable() = this
  }
  
  /** Get an expression that is directly stored in this variable. */
  Expr getAnAssignedValue() {
    // result is an expression that this variable is initialized to
    exists (VariableDeclarator vd | vd.getBindingPattern().(VarDecl).getVariable() = this | result = vd.getInit()) or
    // if this variable represents a function binding, return the function
    exists (Function fn | fn.getVariable() = this | result = fn) or
    // there is an assignment to this variable
    exists (Assignment assgn | assgn.getLhs() = getAnAccess() and assgn.getRhs() = result)
  }

  /** Is this variable ever captured in the closure of a nested function? */
  predicate isCaptured() {
    exists (Function f | f = getAnAccess().getContainer() |
      this instanceof GlobalVariable or
      this.(LocalVariable).getScope() = f.getScope().getOuterScope+()
    )
  }

  /** Is there any declaration of this variable in `tl`? */
  predicate declaredIn(TopLevel tl) {
    getADeclaration().getTopLevel() = tl
  }
  
  string toString() {
    result = getName()
  }
}

/** An 'arguments' variable implicitly declared by a function. */
class ArgumentsObject extends Variable {
  ArgumentsObject() {
    isArgumentsObject(this)
  }
  
  FunctionScope getScope() {
    result = Variable.super.getScope()
  }

  /** Get the function declaring this 'arguments' variable. */
  Function getFunction() {
    result = getScope().getFunction()
  }
}

/** An identifier that refers to a variable, either in a declaration or in a variable read/write. */
abstract class VarRef extends @varref, Identifier, BindingPattern {
  /** Get the variable this identifier refers to. */
  abstract Variable getVariable();

  VarRef getABindingVarRef() { result = this }

  predicate isImpure() { Identifier.super.isImpure() }
}

/** An identifier that refers to a variable in a non-declaring position. */
class VarAccess extends @varaccess, VarRef {
  Variable getVariable() {
    bind(this, result)
  }

  predicate isLValue() {
    exists (Assignment assgn | assgn.getTarget() = this) or
    exists (UpdateExpr upd | upd.getOperand().stripParens() = this) or
    exists (EnhancedForLoop efl | efl.getIterator() = this) or
    exists (BindingPattern p | this = p.getABindingVarRef() and p.isLValue())
  }

  Variable getAVariable() {
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
}

/** A local variable or parameter that is not captured. */
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
  /** Get a variable reference in binding position within this pattern; overridden by subclasses. */
  VarRef getABindingVarRef() { none() }

  /** Get a variable bound by this pattern. */
  Variable getAVariable() { result = getABindingVarRef().getVariable() }

  /** Is this pattern used in an l-value position? */
  predicate isLValue() {
    any()
  }
}

/** A destructuring pattern, i.e., either an array pattern or an object pattern. */
abstract class DestructuringPattern extends BindingPattern {
}

/** An identifier that declares a variable. */
class VarDecl extends @vardecl, VarRef {
  Variable getVariable() {
    decl(this, result)
  }

  predicate isLValue() {
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
  /** Get the i-th element of this array pattern. */
  Expr getElement(int i) {
    i >= 0 and
    result = this.getChildExpr(i)
  }
  
  /** Get some element of this array pattern. */
  Expr getAnElement() {
    exists (int i | i >= -1 | result = this.getChildExpr(i))
  }

  /** Get the default expression for the i-th element of this array pattern, if any. */
  Expr getDefault(int i) {
    i in [0..getSize()-1] and
    result = getChildExpr(-2 - i)
  }

  /** Does the i-th element of this array pattern have a default expression? */
  predicate hasDefault(int i) {
    exists(getDefault(i))
  }

  /** Get the rest pattern of this array pattern, if any. */
  Expr getRest() {
    result = getChildExpr(-1)
  }

  /** Does this array pattern have a rest pattern? */
  predicate hasRest() {
    exists(getRest())
  }
  
  /** Get the number of elements in this array pattern, not including any rest pattern. */
  int getSize() {
    arraySize(this, result)
  }
  
  /** Is the i-th element of this array pattern omitted? */
  predicate elementIsOmitted(int i) {
    i in [0..getSize()-1] and
    not exists (getElement(i))
  }
  
  /** Does this array pattern have an omitted element? */
  predicate hasOmittedElement() {
    elementIsOmitted(_)
  }

  predicate isImpure() {
    getAnElement().isImpure()
  }

  VarRef getABindingVarRef() {
    result = getAnElement().(BindingPattern).getABindingVarRef()
  }
}

/** An object pattern. */
class ObjectPattern extends DestructuringPattern, @objectpattern {
  /** Get the i-th property pattern in this object pattern. */
  PropertyPattern getPropertyPattern(int i) {
    properties(result, this, i, _, _)
  }
  
  /** Get some property pattern in this object pattern. */
  PropertyPattern getAPropertyPattern() {
    result = this.getPropertyPattern(_)
  }
  
  /** Get the number of property patterns in this object pattern. */
  int getNumProperty() {
    result = count(this.getAPropertyPattern())
  }
  
  /** Get the property pattern with the given name, if any. */
  PropertyPattern getPropertyPatternByName(string name) {
    result = this.getAPropertyPattern() and
    result.getName() = name
  }

  predicate isImpure() {
    getAPropertyPattern().isImpure()
  }

  VarRef getABindingVarRef() {
    result = getAPropertyPattern().getValuePattern().(BindingPattern).getABindingVarRef()
  }
}

/** A property pattern in an object pattern. */
class PropertyPattern extends @property, ASTNode {
  PropertyPattern() {
    // filter out ordinary properties
    exists (ObjectPattern obj | properties(this, obj, _, _, _))
  }

  /** Is the name of this property pattern computed? */
  predicate isComputed() {
    isComputed(this)
  }

  /** Get the expression specifying the name of the matched property. */
  Expr getNameExpr() {
    result = this.getChildExpr(0)
  }

  /** Get the expression the matched property value is assigned to. */
  Expr getValuePattern() {
    result = this.getChildExpr(1)
  }

  /** Get the default value of this property pattern, if any. */
  Expr getDefault() {
    result = this.getChildExpr(2)
  }

  /** Is this property pattern a shorthand pattern? */
  predicate isShorthand() {
    getNameExpr().getLocation() = getValuePattern().getLocation()
  }
  
  /** Get the name of the property matched by this pattern. */
  string getName() {
    (not isComputed() and
     result = ((Identifier)getNameExpr()).getName()) or
    result = ((Literal)getNameExpr()).getValue()
  }
  
  /** Get the object pattern this property pattern belongs to. */
  ObjectPattern getObjectPattern() {
    properties(this, result, _, _, _)
  }

  /** Get the nearest enclosing function or toplevel in which this property pattern occurs. */
  StmtContainer getContainer() {
    result = getObjectPattern().getContainer()
  }

  /** Is this pattern impure, that is, could its evaluation have side effects? */
  predicate isImpure() {
    (isComputed() and getNameExpr().isImpure()) or
    getValuePattern().isImpure()
  }

  string toString() {
    properties(this, _, _, _, result)
  }
}

/** A variable declarator declaring a local or global variable. */
class VariableDeclarator extends Expr, @vardeclarator {
	/** Get the pattern specifying the declared variable(s). */
	BindingPattern getBindingPattern() {
		result = this.getChildExpr(0)
  }
	
	/** Get the expression specifying the initial value of the declared variable, if any. */
	Expr getInit() {
		result = this.getChildExpr(1)
	}

	/** Get the declaration statement this declarator belongs to, if any. */
	DeclStmt getDeclStmt() {
		this = result.getADecl()
	}

  CFGNode getFirstCFGNode() {
    if exists(getInit()) then
      result = getInit().getFirstCFGNode()
    else
      result = this
  }
}

/** A syntactic entity that declares parameters, that is, either a function or
 * a catch clause. */
class Parameterized extends @parameterized, ASTNode {
  /** Get a parameter declared by this entity. */
	Parameter getAParameter() {
		this = result.getParent()
	}
	
	/** Get the number of parameters declared by this entity. */
	int getNumParameter() {
		result = count(getAParameter())
	}

	/** Get a variable of the given name that is a parameter of this entity. */
	Variable getParameterVariable(string name) {
		result = getAParameter().getAVariable() and
		result.getName() = name
	}

	/** Get a JSDoc comment attached to this entity, if any. */
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
   * Get the index of this parameter within the parameter list of its
   * declaring entity.
   */
  int getIndex() {
    exists (Parameterized p | this = p.getChildExpr(result))
  }
  
  /** Get the entity declaring this parameter. */
  Parameterized getParent() {
    result = super.getParent()
  }

  /** Get the default expression for this parameter, if any. */
  Expr getDefault() {
    exists (Function f, int n | this = f.getParameter(n) | result = f.getChildExpr(-(n+3)))
  }

  /** Is this parameter a rest parameter? */
  predicate isRestParameter() {
    exists (Function f, int n | this = f.getParameter(n) |
      n = f.getNumParameter()-1 and
      f.hasRestParameter()
    )
  }

  predicate isLValue() {
    any()
  }
}

/** A parameter declaration that is not an object or array pattern. */
class SimpleParameter extends Parameter, VarDecl {
  /** Get the entity declaring this parameter. */
  Parameterized getParent() { result = Parameter.super.getParent() }

  predicate isImpure() { VarDecl.super.isImpure() }
  VarRef getABindingVarRef() { result = VarDecl.super.getABindingVarRef() }
  predicate isLValue() { Parameter.super.isLValue() }
}

/** Is e a variable reference or property access referring to the global variable g? */
predicate accessesGlobal(Expr e, string g) {
  // direct global variable access
  ((GlobalVarAccess)e).getName() = g or
  
  // property access through 'window'
  exists (PropAccess pacc |
    pacc = e and
    accessesGlobal(pacc.getBase(), "window") and
    pacc.getPropertyName() = g
  )
}
