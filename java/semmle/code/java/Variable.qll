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
 * A library for working with Java variables and their declarations.
 */

import Element

/** A variable is a field, a local variable or a parameter. */
class Variable extends @variable, Annotatable, Element, Modifiable {
  /** The type of this variable. */
  /*abstract*/ Type getType() { none() }

  /** An access to this variable. */
  VarAccess getAnAccess() { variableBinding(result,this) }

  /** An expression on the right-hand side of an assignment to this variable. */
  Expr getAnAssignedValue() {
    exists(LocalVariableDeclExpr e | e.getVariable() = this and result = e.getInit())
    or
    exists(AssignExpr e | e.getDest().getProperExpr() = this.getAnAccess() and result = e.getSource())
  }
  
  /** The initializer expression of this variable. */
  Expr getInitializer() {
    none()
  }

  /** A printable representation of this variable together with its type. */
  string pp() {
    result = this.getType().getName() + " " + this.getName() 
  }
}

/** A locally scoped variable, i.e. either a local variable or a parameter. */
abstract class LocalScopeVariable extends Variable {
}

/** A local variable declaration */
class LocalVariableDecl extends @localvar, LocalScopeVariable {
  /** The type of this local variable. */
  Type getType() { localvars(this,_,result,_) }
  
  /** The expression declaring this variable. */
  LocalVariableDeclExpr getDeclExpr() { localvars(this, _, _, result) }

  /** The parent of this declaration. */
  Expr getParent() { localvars(this,_,_,result) }

  /** The callable in which this declaration occurs. */
  Callable getCallable() { result = this.getParent().getEnclosingCallable() }

  /** The callable in which this declaration occurs. */
  Callable getEnclosingCallable() { result = getCallable() }

  /** A printable representation of this local variable declaration. */
  string toString() { result = this.getType().getName() + " " + this.getName() }

  /** The initializer expression of this local variable declaration. */
  Expr getInitializer() {
    result = getDeclExpr().getInit()
  }
}

/** A formal parameter of a callable. */
class Parameter extends Element, @param, LocalScopeVariable {
  /** The type of this formal parameter. */
  Type getType() { params(this,_,result,_,_,_) }

  /** Whether the parameter is never assigned a value in the body of the callable. */
  predicate isEffectivelyFinal() { not exists(getAnAssignedValue()) }

  /** The (zero-based) index of this formal parameter. */
  int getPosition() { params(this,_,_,result,_,_) }

  /** The callable that declares this formal parameter. */
  Callable getCallable() { params(this,_,_,_,result,_) }

  /** The source declaration of this formal parameter. */
  Parameter getSourceDeclaration() { params(this,_,_,_,_,result) }

  /** Whether this formal parameter is the same as its source declaration. */
  predicate isSourceDeclaration() { this.getSourceDeclaration() = this }
  
  /** Whether this formal parameter is a variable arity parameter. */
  predicate isVarargs() {
    isVarargsParam(this)
  }

  /** A call to the callable that declares this formal parameter. */
  pragma[noinline]
  private Call getACall() {
    result = getCallable().getAReference()
  }

  /**
   * An argument for this parameter in any call to the callable that declares this formal
   * parameter.
   *
   * Varargs parameters will have no results for this method.
   */
  Expr getAnArgument() {
    not isVarargs() and
    exists(Call c |
      c = getACall() |
      result = c.getArgument(getPosition())
    )
  }
}
