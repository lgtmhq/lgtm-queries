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
 * Provides classes for working with ECMAScript 2015 classes.
 *
 * Class declarations and class expressions are modeled by (QL) classes `ClassDeclaration`
 * and `ClassExpression`, respectively, which are both subclasses of `ClassDefinition`.
 * Each `ClassDefinition` has an associated `Class`, which models the class being defined.
 */

import Stmt

/**
 * A class definition, that is, either a class declaration statement or a
 * class expression.
 */
abstract class ClassDefinition extends @classdecl, ASTNode {
  /** Gets the identifier naming the defined class, if any. */
  VarDecl getIdentifier() {
    result = getChildExpr(0)
  }

  /** Gets the name of the defined class, if any. */
  string getName() {
    result = getIdentifier().getName()
  }

  /** Gets the expression denoting the super class of the defined class, if any. */
  Expr getSuperClass() {
    result = getChildExpr(1)
  }

  /** Gets the class defined by this class definition. */
  Class getDefinedClass() {
    this = result.getDefinition()
  }

  /** Gets the nearest enclosing function or toplevel in which this class definition occurs. */
  abstract StmtContainer getContainer();
}

/**
 * A class declaration statement.
 */
class ClassDeclStmt extends @classdeclstmt, ClassDefinition, Stmt {
  /** Gets the nearest enclosing function or toplevel in which this class declaration occurs. */
  override StmtContainer getContainer() { result = Stmt.super.getContainer() }
}

/**
 * A class expression.
 */
class ClassExpr extends @classexpr, ClassDefinition, Expr {
  override predicate isImpure() {
    none()
  }

  /** Gets the nearest enclosing function or toplevel in which this class expression occurs. */
  override StmtContainer getContainer() { result = Expr.super.getContainer() }
}

/**
 * A class defined by a class declaration.
 */
class Class extends @class, ASTNode {
  /** Gets the definition defining this class. */
  ClassDefinition getDefinition() {
    classes(this, result, _)
  }

  /** Gets a member declared in this class. */
  MemberDefinition getAMember() {
    result.getDeclaringClass() = this
  }

  /** Gets the member with the given name declared in this class. */
  MemberDefinition getMember(string name) {
    result = getAMember() and
    result.getName() = name
  }

  /** Gets a method declared in this class. */
  MethodDefinition getAMethod() {
    result = getAMember()
  }

  /** Gets the method with the given name declared in this class. */
  MethodDefinition getMethod(string name) {
    result = getMember(name)
  }

  /** Gets a field declared in this class. */
  FieldDefinition getAField() {
    result = getAMember()
  }

  /** Gets the field with the given name declared in this class. */
  FieldDefinition getField(string name) {
    result = getMember(name)
  }

  /**
   * Gets the constructor of this class.
   *
   * Note that every class has a constructor: if no explicit constructor
   * is declared, it has a synthetic default constructor.
   */
  ConstructorDefinition getConstructor() {
    result = getAMethod()
  }

  /**
   * Gets the `i`th decorator applied to this class.
   *
   * For example, the class `@A @B class C {}` has
   * `@A` as its 0th decorator, and `@B` as its first decorator.
   */
  Decorator getDecorator(int i) {
    result = getDefinition().getChildExpr(-(i+1))
  }

  /**
   * Gets a decorator applied to this class, if any.
   *
   * For example, the class `@A @B class C {}` has
   * decorators `@A` and `@B`.
   */
  Decorator getADecorator() {
    result = getDecorator(_)
  }

  /** Gets the expression denoting the super class of this class, if any. */
  Expr getSuperClass() {
    result = getDefinition().getSuperClass()
  }

  /**
   * Gets a description of this class.
   *
   * For named classes such as `class C { ... }`, this is just the declared
   * name. For classes assigned to variables, this is the name of the variable.
   * If no meaningful name can be inferred, the result is "anonymous class".
   */
  string describe() {
    if exists(inferNameFromVarDef()) then
      result = inferNameFromVarDef()
    else
      result = "anonymous class"
  }

  /**
   * Gets a description of this class, based on its declared name or the name
   * of the variable it is assigned to, if any.
   */
  private string inferNameFromVarDef() {
    exists (ClassDefinition cd | cd = getDefinition() |
      // in ambiguous cases like `let C = class D {}`, prefer `D` to `C`
      if exists(cd.getName()) then
        result = "class " + cd.getName()
      else exists (VarDef vd | getDefinition() = vd.getSource() |
        result = "class " + vd.getTarget().(VarRef).getName()
      )
    )
  }

  override string toString() {
    classes(this, _, result)
  }
}

/**
 * A `super` expression.
 */
class SuperExpr extends @superexpr, Expr {
  override predicate isImpure() {
    none()
  }

  /**
   * Gets the function whose `super` binding this expression refers to,
   * which is the nearest enclosing non-arrow function.
   */
  Function getBinder() {
    result = getEnclosingFunction().getThisBinder()
  }
}

/**
 * A `super(...)` call.
 */
class SuperCall extends CallExpr {
  SuperCall() {
    getCallee().stripParens() instanceof SuperExpr
  }

  /**
   * Gets the function whose `super` binding this call refers to,
   * which is the nearest enclosing non-arrow function.
   */
  Function getBinder() {
    result = getCallee().stripParens().(SuperExpr).getBinder()
  }
}

/**
 * A property access on `super`.
 */
class SuperPropAccess extends PropAccess {
  SuperPropAccess() {
    getBase().stripParens() instanceof SuperExpr
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
  override predicate isImpure() {
    none()
  }
}

/**
 * A scope induced by a named class expression.
 */
class ClassExprScope extends @classexprscope, Scope {
  override string toString() {
    result = "class expression scope"
  }
}

/**
 * A member definition in a class, that is, either a method definition or a field definition.
 */
class MemberDefinition extends @property, ASTNode {
  MemberDefinition() {
    // filter out property patterns and object properties
    exists (Class cl | properties(this, cl, _, _, _))
  }

  /**
   * Holds if this member is static.
   */
  predicate isStatic() {
    isStatic(this)
  }

  /**
   * Gets the expression specifying the name of this member.
   */
  Expr getNameExpr() {
    result = getChildExpr(0)
  }

  /**
   * Gets the expression specifying the initial value of the class member;
   * for methods and constructors this is always a function, for fields
   * it may not be defined.
   */
  Expr getInit() {
    result = getChildExpr(1)
  }

  /** Gets the name of this member. */
  string getName() {
    result = getNameExpr().(Literal).getValue() or
    not isComputed() and result = getNameExpr().(Identifier).getName()
  }

  /** Holds if the name of this member is computed. */
  predicate isComputed() {
    isComputed(this)
  }

  /** Gets the class this member belongs to. */
  Class getDeclaringClass() {
    properties(this, result, _, _, _)
  }

  /** Gets the JSDoc comment for this member, if any. */
  JSDoc getDocumentation() {
    result.getComment().getNextToken() = getFirstToken()
  }

  /** Gets the nearest enclosing function or toplevel in which this member occurs. */
  StmtContainer getContainer() {
    result = getDeclaringClass().getDefinition().getContainer()
  }

  /** Holds if the name of this member is computed by an impure expression. */
  predicate hasImpureNameExpr() {
    isComputed() and getNameExpr().isImpure()
  }

  /**
   * Gets the `i`th decorator applied to this member.
   *
   * For example, a method of the form `@A @B m() { ... }` has
   * `@A` as its 0th decorator and `@B` as its first decorator.
   */
  Decorator getDecorator(int i) {
    result = getChildExpr(-(i+1))
  }

  /**
   * Gets a decorator applied to this member.
   *
   * For example, a method of the form `@A @B m() { ... }` has
   * decorators `@A` and `@B`.
   */
  Decorator getADecorator() {
    result = getDecorator(_)
  }

  override string toString() {
    properties(this, _, _, _, result)
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getNameExpr().getFirstControlFlowNode()
  }
}

/**
 * A method definition in a class.
 */
class MethodDefinition extends MemberDefinition {
  MethodDefinition() {
    isMethod(this)
  }

  /**
   * Gets the body of this method.
   */
  FunctionExpr getBody() {
    result = getChildExpr(1)
  }
}

/**
 * A constructor definition in a class.
 */
class ConstructorDefinition extends MethodDefinition {
  ConstructorDefinition() {
    not isComputed() and not isStatic() and
    getName() = "constructor"
  }

  /** Holds if this is a synthetic default constructor. */
  predicate isSynthetic() {
    getLocation().isEmpty()
  }
}

/**
 * A function generated by the extractor to implement
 * a synthetic default constructor.
 */
class SyntheticConstructor extends Function {
  SyntheticConstructor() {
    this = any(ConstructorDefinition cd | cd.isSynthetic() | cd.getBody())
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

/**
 * A field definition in a class.
 */
class FieldDefinition extends MemberDefinition {
  FieldDefinition() {
    not isMethod(this)
  }
}
