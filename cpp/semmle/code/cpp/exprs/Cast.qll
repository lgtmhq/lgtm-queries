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

/**
 * A C/C++ cast expression or similar unary expression that doesn't affect the logical value of its operand.
 *
 * Instances of this class are not present in the main AST which is navigated by parent/child links. Instead,
 * instances of this class are attached to nodes in the main AST via special conversion links.
 */
abstract class Conversion extends Expr {
  /** Gets the expression being converted. */
  Expr getExpr() { result.getConversion() = this }

  /** Holds if this conversion is an implicit conversion. */
  predicate isImplicit() { this.isCompilerGenerated() }

  override predicate mayBeImpure() {
    this.getExpr().mayBeImpure()
  }
  override predicate mayBeGloballyImpure() {
    this.getExpr().mayBeGloballyImpure()
  }
}

/**
 * A C/C++ cast expression.
 *
 * To get the type which the expression is being cast to, use getType().
 */
abstract class Cast extends Conversion {
}

/**
 * A cast expression in C, or a C-style cast expression in C++.
 */
class CStyleCast extends Cast, @c_style_cast {
  override string toString() { result = "(" + this.getType().getName() + ")..." }

  override int getPrecedence() { result = 15 }
}

/**
 * A C++ `static_cast` expression.
 */
class StaticCast extends Cast, @static_cast {
  override string toString() { result = "static_cast<" + this.getType().getName() + ">..." }

  override int getPrecedence() { result = 16 }
}

/**
 * A C++ `const_cast` expression.
 */
class ConstCast extends Cast, @const_cast {
  override string toString() { result = "const_cast<" + this.getType().getName() + ">..." }

  override int getPrecedence() { result = 16 }
}

/**
 * A C++ `reinterpret_cast` expression.
 */
class ReinterpretCast extends Cast, @reinterpret_cast {
  override string toString() { result = "reinterpret_cast<" + this.getType().getName() + ">..." }

  override int getPrecedence() { result = 16 }
}

/**
 * A C++ `dynamic_cast` expression.
 */
class DynamicCast extends Cast, @dynamic_cast {
  override string toString() { result = "dynamic_cast<" + this.getType().getName() + ">..." }

  override int getPrecedence() { result = 16 }
}

/**
 * A C++ `typeid` expression which provides runtime type information
 * about an expression or type.
 */
class TypeidOperator extends Expr, @type_id {
  /**
   * Gets the type that is returned by this typeid expression.
   * 
   * For example in the following code the `typeid` returns the
   * type `MyClass *`. 
   * 
   * ```
   * MyClass *ptr;
   * 
   * printf("the type of ptr is: %s\n", typeid(ptr).name);
   * ```
   */
  Type getResultType() { typeid_bind(this,result) }

  /**
   * DEPRECATED: Use `getResultType()` instead.
   *
   * Gets the type that is returned by this typeid expression.
   */
  deprecated Type getSpecifiedType() { result = this.getResultType() }

  /**
   * Gets the contained expression, if any (if this typeid contains
   * a type rather than an expression, there is no result).
   */
  Expr getExpr() { result = this.getChild(0) }

  override string toString() { result = "typeid ..." }

  override int getPrecedence() { result = 16 }

  override predicate mayBeImpure() {
    this.getExpr().mayBeImpure()
  }
  override predicate mayBeGloballyImpure() {
    this.getExpr().mayBeGloballyImpure()
  }
}

/**
 * A C++11 `sizeof...` expression which determines the size of a template parameter pack.
 *
 * This expression only appears in templates themselves - in any actual
 * instantiations, "sizeof...(x)" will be replaced by its integer value.
 */
class SizeofPackOperator extends Expr, @sizeof_pack {
  override string toString() { result = "sizeof...(...)" }

  override predicate mayBeImpure() {
    none()
  }
  override predicate mayBeGloballyImpure() {
    none()
  }
}

/**
 * A C/C++ sizeof expression.
 */
abstract class SizeofOperator extends Expr, @runtime_sizeof {
  override int getPrecedence() { result = 15 }
}

/**
 * A C/C++ sizeof expression whose operand is an expression.
 */
class SizeofExprOperator extends SizeofOperator {
  SizeofExprOperator() { exists(Expr e | this.getChild(0) = e) }

  /** Gets the contained expression. */
  Expr getExprOperand() { result = this.getChild(0) }

  /**
   * DEPRECATED: Use `getExprOperand()` instead
   *
   * Gets the contained expression.
   * */
  deprecated Expr getExpr() { result = this.getExprOperand() }

  override string toString() { result = "sizeof(<expr>)" }

  override predicate mayBeImpure() {
    this.getExprOperand().mayBeImpure()
  }
  override predicate mayBeGloballyImpure() {
    this.getExprOperand().mayBeGloballyImpure()
  }
}

/**
 * A C/C++ sizeof expression whose operand is a type name.
 */
class SizeofTypeOperator extends SizeofOperator {
  SizeofTypeOperator() { sizeof_bind(this,_) }
  
  /** Gets the contained type. */
  Type getTypeOperand() { sizeof_bind(this,result) }

  /**
   * DEPRECATED: Use `getTypeOperand()` instead
   *
   * Gets the contained type.
   */
  deprecated Type getSpecifiedType() { result = this.getTypeOperand() }

  override string toString() { result = "sizeof(" + this.getTypeOperand().getName() + ")" }

  override predicate mayBeImpure() {
    none()
  }
  override predicate mayBeGloballyImpure() {
    none()
  }
}

/**
 * A C++11 `alignof` expression.
 */
abstract class AlignofOperator extends Expr, @runtime_alignof {
  override int getPrecedence() { result = 15 }
}

/**
 * A C++11 `alignof` expression whose operand is an expression.
 */
class AlignofExprOperator extends AlignofOperator {
  AlignofExprOperator() { exists(Expr e | this.getChild(0) = e) }

  /**
   * Gets the contained expression.
   */
  Expr getExprOperand() { result = this.getChild(0) }

  /**
   * DEPRECATED: Use `getExprOperand()` instead.
   */
  deprecated Expr getExpr() { result = this.getExprOperand() }

  override string toString() { result = "alignof(<expr>)" }
}

/**
 * A C++11 `alignof` expression whose operand is a type name.
 */
class AlignofTypeOperator extends AlignofOperator {
  AlignofTypeOperator() { sizeof_bind(this,_) }

  /** Gets the contained type. */
  Type getTypeOperand() { sizeof_bind(this,result) }

  /**
   * DEPRECATED: Use `getTypeOperand()` instead.
   */
  deprecated Type getSpecifiedType() { result = this.getTypeOperand() }

  override string toString() { result = "alignof(" + this.getTypeOperand().getName() + ")" }
}

/**
 * A C/C++ array to pointer conversion.
 */
class ArrayToPointerConversion extends Conversion, @array_to_pointer {
  /** Gets a textual representation of this conversion. */
  override string toString() { result = "array to pointer conversion" }

  override predicate mayBeImpure() {
    none()
  }
  override predicate mayBeGloballyImpure() {
    none()
  }
}
