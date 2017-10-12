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

/** Provides classes for working with functions. */

import Locations
import Stmt
import Variables
import AST
import BasicBlocks

/** A function as defined either by a function declaration or a function expression. */
class Function extends @function, Parameterized, StmtContainer {
  /** Gets the `i`th parameter of this function. */
  Parameter getParameter(int i) {
    result = getChildExpr(i)
  }

  /** Gets a parameter of this function. */
  override Parameter getAParameter() {
    exists (int idx | result = getParameter(idx))
  }

  /** Gets the parameter named `name` of this function, if any. */
  SimpleParameter getParameterByName(string name) {
    result = getAParameter() and
    result.getName() = name
  }

  /** Gets the identifier specifying the name of this function, if any. */
  VarDecl getId() {
   result = getChildExpr(-1)
  }

  /** Gets the name of this function, if any. */
  string getName() {
    result = getId().getName()
  }

  /** Gets the variable holding this function. */
  Variable getVariable() {
    result = getId().getVariable()
  }

  /** Gets the `arguments` variable of this function, if any. */
  ArgumentsVariable getArgumentsVariable() {
    result.getFunction() = this
  }

  /** Holds if the body of this function refers to the function's `arguments` variable. */
  predicate usesArgumentsObject() {
    exists (getArgumentsVariable().getAnAccess())
  }

  /**
   * Holds if this function declares a parameter or local variable named `arguments`.
   */
  predicate declaresArguments() {
    exists(getScope().getVariable("arguments").getADeclaration())
  }
  
  /** Gets the statement enclosing this function, if any. */
  Stmt getEnclosingStmt() {
    none()
  }
  
  /** Gets the body of this function. */
  override ExprOrStmt getBody() {
    result = getChild(-2)
  }

  /** Gets the `i`th statement in the body of this function. */
  Stmt getBodyStmt(int i) {
    result = getBody().(BlockStmt).getStmt(i)
  }

  /** Gets a statement in the body of this function. */
  Stmt getABodyStmt() {
    result = getBodyStmt(_)
  }

  /** Gets the number of statements in the body of this function. */
  int getNumBodyStmt() {
    result = count(getABodyStmt())
  }

  /** Holds if this function is a generator function. */
  predicate isGenerator() {
    isGenerator(this)
  }

  /** Holds if the last parameter of this function is a rest parameter. */
  predicate hasRestParameter() {
    hasRestParameter(this)
  }

  /**
   * Gets the last token of this function's parameter list, not including
   * the closing parenthesis, if any.
   */
  private Token lastTokenOfParameterList() {
    // if there are any parameters, it's the last token of the last parameter
    exists (Parameter lastParam | lastParam = getParameter(getNumParameter()-1) |
      result = lastParam.getDefault().getLastToken() or
      not exists(lastParam.getDefault()) and result = lastParam.getLastToken()
    )
    or
    // otherwise we have an empty parameter list `()`, and
    // we want to return the opening parenthesis
    not exists(getAParameter()) and
    (
      // if the function has a name, the opening parenthesis comes right after it
      result = getId().getLastToken().getNextToken() or
      // otherwise this must be an arrow function with no parameters, so the opening
      // parenthesis is the very first token of the function
      not exists(getId()) and result = getFirstToken()
    )
  }

  /** Holds if the parameter list of this function has a trailing comma. */
  predicate hasTrailingComma() {
    lastTokenOfParameterList().getNextToken().getValue() = ","
  }

  /** Holds if this function is an asynchronous function. */
  predicate isAsync() {
    isAsync(this)
  }

  /** Gets the enclosing function or toplevel of this function. */
  override StmtContainer getEnclosingContainer() {
    result = getEnclosingStmt().getContainer()
  }

  /** Gets the number of lines in this function. */
  int getNumberOfLines() {
    numlines(this, result, _, _)
  }

  /** Gets the number of lines containing code in this function. */
  int getNumberOfLinesOfCode() {
    numlines(this, _, result, _)
  }

  /** Gets the number of lines containing comments in this function. */
  int getNumberOfLinesOfComments() {
    numlines(this, _, _, result)
  }

  /** Gets the cyclomatic complexity of this function. */
  int getCyclomaticComplexity() {
    result = 2 +
      sum (Expr nd | nd.getContainer() = this and nd.isBranch() |
                     strictcount(nd.getASuccessor()) - 1)
  }

  /** Gets the JSDoc documentation for this function, if any. */
  override JSDoc getDocumentation() {
    none()
  }

  override predicate isStrict() {
    // check for explicit strict mode directive
    exists (StrictModeDecl smd | this = smd.getContainer())
    or
    // check for enclosing strict function
    StmtContainer.super.isStrict()
    or
    // all parts of a class definition are strict code
    this.getParent*() = any(ClassDefinition cd).getSuperClass() or
    this = any(MethodDefinition md).getBody()
  }

  /** Gets a return statement in the body of this function, if any. */
  ReturnStmt getAReturnStmt() {
    result.getContainer() = this
  }

  /** Gets an expression that could be returned by this function, if any. */
  Expr getAReturnedExpr() {
    result = getBody() or
    result = getAReturnStmt().getExpr()
  }

  /**
   * Gets the function whose `this` binding a `this` expression in this function refers to,
   * which is the nearest enclosing non-arrow function.
   */
  Function getThisBinder() {
    result = this
  }

  /**
   * Holds if this function has a mapped `arguments` variable whose indices are aliased
   * with the function's parameters.
   *
   * A function has a mapped `arguments` variable if it is non-strict, and has no rest
   * parameter, no parameter default values, and no destructuring parameters.
   */
  predicate hasMappedArgumentsVariable() {
    exists (getArgumentsVariable()) and
    not isStrict() and
    forall (Parameter p | p = getAParameter() |
      p instanceof SimpleParameter and not exists(p.getDefault())
    ) and
    not hasRestParameter()
  }

  /**
   * Gets a description of this function.
   *
   * For named functions such as `function f() { ... }`, this is just the declared
   * name. For functions assigned to variables or properties (including class
   * members), this is the name of the variable or property. If no meaningful name
   * can be inferred, the result is "anonymous function".
   */
  string describe() {
    if exists(inferNameFromVarDef()) then
      result = inferNameFromVarDef()
    else if exists(inferNameFromProp()) then
      result = inferNameFromProp()
    else if exists(inferNameFromMemberDef()) then
      result = inferNameFromMemberDef()
    else
      result = "anonymous function"
  }

  /**
   * Gets a description of this function, based on its declared name or the name
   * of the variable it is assigned to, if any.
   */
  private string inferNameFromVarDef() {
    // in ambiguous cases like `var f = function g() {}`, prefer `g` to `f`
    if exists(getName()) then
      result = "function " + getName()
    else exists (VarDef vd | this = vd.getSource() |
      result = "function " + vd.getTarget().(VarRef).getName()
    )
  }

  /**
   * Gets a description of this function, based on the name of the property
   * it is assigned to, if any.
   */
  private string inferNameFromProp() {
    exists (Property p, string n | this = p.getInit() and n = p.getName() |
      p instanceof PropertyGetter and result = "getter for property " + n or
      p instanceof PropertySetter and result = "setter for property " + n or
      p instanceof ValueProperty and result = "method " + n
    )
  }

  /**
   * Gets a description of this function, based on the name of the class
   * member it is assigned to, if any.
   */
  private string inferNameFromMemberDef() {
    exists (ClassDefinition c, string n, MemberDefinition m, string classpp |
      m = c.getMember(n) and this = m.getInit() and classpp = c.describe() |
      if m instanceof ConstructorDefinition then
        if m.(ConstructorDefinition).isSynthetic() then
          result = "default constructor of " + classpp
        else
          result = "constructor of " + classpp
      else
        if m instanceof GetterMethodDefinition then
          result = "getter method for property " + n + " of " + classpp
        else if m instanceof SetterMethodDefinition then
          result = "setter method for property " + n + " of " + classpp
        else
          result = "method " + n + " of " + classpp
    )
  }

  /**
   * Holds if this function has a body.
   *
   * A TypeScript function has no body if it is ambient, abstract, or an overload signature.
   * 
   * A JavaScript function always has a body.
   */
  predicate hasBody() {
    exists (getBody())
  }

  /**
   * Holds if this function is part of an abstract class member.
   */
  predicate isAbstract() {
      exists (MethodDefinition md | this = md.getBody() | md.isAbstract())
  }
}

/**
 * A method defined in a class or object expression.
 */
class Method extends FunctionExpr {
  Method() {
    exists (MethodDefinition md | this = md.getBody())
    or
    exists (ValueProperty p | p.isMethod() | this = p.getInit())
  }
}

/**
 * A constructor defined in a class.
 */
class Constructor extends FunctionExpr {
  Constructor() {
    exists (ConstructorDefinition cd | this = cd.getBody())
  }
}
