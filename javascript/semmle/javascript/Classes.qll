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

import Stmt

/**
 * A class declaration, that is, either a class declaration statement or a
 * class expression.
 */
abstract class ClassDefinition extends @classdecl, ASTNode {
  /** Get the identifier naming this class, if any. */
  VarDecl getIdentifier() {
    result = getChildExpr(0)
  }

  /** Get the name of this class, if any. */
  string getName() {
    result = getIdentifier().getName()
  }

  /** Get the expression denoting the super class, if any. */
  Expr getSuperClass() {
    result = getChildExpr(1)
  }

  /** Get the class declared by this class declaration statement. */
  Class getDefinedClass() {
    this = result.getDefinition()
  }

  /** Get the nearest enclosing function or toplevel in which this class occurs. */
  abstract StmtContainer getContainer();
}

/**
 * A class declaration statement.
 */
class ClassDeclStmt extends @classdeclstmt, ClassDefinition, Stmt {
  string toString() { result = Stmt.super.toString() }

  /** Get the nearest enclosing function or toplevel in which this class occurs. */
  StmtContainer getContainer() { result = Stmt.super.getContainer() }
}

/**
 * A class expression.
 */
class ClassExpr extends @classexpr, ClassDefinition, Expr {
  predicate isImpure() {
    none()
  }

  string toString() { result = Expr.super.toString() }

  /** Get the nearest enclosing function or toplevel in which this class occurs. */
  StmtContainer getContainer() { result = Expr.super.getContainer() }
}

/**
 * A class defined by a class declaration statement or a class expression.
 */
class Class extends @class, ASTNode {
  /** Get the definition defining this class. */
  ClassDefinition getDefinition() {
    classes(this, result, _)
  }

  /** Get a method declared in this class. */
  MethodDefinition getAMethod() {
    result.getDeclaringClass() = this
  }

  /** Get the method of the given name declared in this class. */
  MethodDefinition getMethod(string name) {
    result = getAMethod() and
    result.getName() = name
  }

  /**
   * Get the constructor of this class.
   *
   * Note that every class has a constructor: if no explicit constructor
   * is declared, it has a synthetic default constructor.
   */
  ConstructorDefinition getConstructor() {
    result = getAMethod()
  }

  string toString() {
    classes(this, _, result)
  }
}

/**
 * A `super` expression.
 */
class SuperExpr extends @superexpr, Expr {
  predicate isImpure() {
    none()
  }
}

/**
 * A `new.target` expression.
 *
 * When a function `f` is invoked as `new f()`, then `new.target` inside
 * `f` evaluates to `f` ; on the other hand, when `f` is invoked without
 * `new`, it evaluates to `undefined`.
 *
 * See also ECMAScript 2015 Language Specification, Chapter 12.3.8.
 */
class NewTargetExpr extends @newtargetexpr, Expr {
  predicate isImpure() {
    none()
  }
}

/**
 * The scope induced by a named class expression.
 */
class ClassExprScope extends @classexprscope, Scope {
}

/**
 * A method definition in a class.
 */
class MethodDefinition extends @property, ASTNode {
  MethodDefinition() {
    // filter out property patterns and object properties
    exists (Class cl | properties(this, cl, _, _, _))
  }

  /**
   * Is this method static?
   */
  predicate isStatic() {
    isStatic(this)
  }

  /**
   * Get the expression specifying the name of the method
   */
  Expr getNameExpr() {
    result = getChildExpr(0)
  }

  /**
   * Get the body of this method.
   */
  FunctionExpr getBody() {
    result = getChildExpr(1)
  }

  /** Get the name of this method. */
  string getName() {
    result = getNameExpr().(Literal).getValue() or
    not isComputed() and result = getNameExpr().(Identifier).getName()
  }
  
  /** Is the name of this method computed? */
  predicate isComputed() {
    isComputed(this)
  }

  /** Get the class this method belongs to. */
  Class getDeclaringClass() {
    properties(this, result, _, _, _)
  }

  /** Get the JSDoc comment for this method, if any. */
  JSDoc getDocumentation() {
    result.getComment().getNextToken() = getFirstToken()
  }
  
  /** Get the nearest enclosing function or toplevel in which this method occurs. */
  StmtContainer getContainer() {
    result = getDeclaringClass().getDefinition().getContainer()
  }

  /** Deprecated; use `hasImpureNameExpr()` instead. */
  deprecated predicate isImpure() {
    hasImpureNameExpr()
  }

  /** Is the name of this method computed by an impure expression? */
  predicate hasImpureNameExpr() {
    isComputed() and getNameExpr().isImpure()
  }
  
  string toString() {
    properties(this, _, _, _, result)
  }

  CFGNode getFirstCFGNode() {
    result = getNameExpr().getFirstCFGNode()
  }
}

/**
 * A constructor definition in a class.
 */
class ConstructorDefinition extends MethodDefinition {
  ConstructorDefinition() {
    not isComputed() and
    getName() = "constructor"
  }

  /** Is this a synthetic default constructor? */
  predicate isSynthetic() {
    getLocation().isEmpty()
  }
}

/**
 * An accessor method definition in a class.
 */
abstract class AccessorMethodDefinition extends MethodDefinition {
}

/**
 * A getter method definition in a class.
 */
class GetterMethodDefinition extends AccessorMethodDefinition, @property_getter {
}

/**
 * A setter method definition in a class.
 */
class SetterMethodDefinition extends AccessorMethodDefinition, @property_setter {
}
