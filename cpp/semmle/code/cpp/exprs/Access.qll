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
import semmle.code.cpp.Variable
import semmle.code.cpp.Enum

/**
 * A C/C++ access expression. This refers to a function, variable, or enum constant.
 */
abstract class Access extends Expr, NameQualifiableElement {
  /** Gets the accessed function, variable, or enum constant. */
  abstract Declaration getTarget();

  override predicate mayBeImpure() {
    none()
  }
  override predicate mayBeGloballyImpure() {
    none()
  }
 
  override string toString() { none() }
}

/**
 * A C/C++ enum constant access expression.
 */
class EnumConstantAccess extends Access, @varaccess {
  EnumConstantAccess() {
    exists(EnumConstant c | varbind(this, c))
  }
 
  /** Gets the accessed enum constant. */
  EnumConstant getTarget() { varbind(this, result) }

  /** Gets a textual representation of this enum constant access. */
  override string toString() { result = this.getTarget().getName() }
}

/**
 * A C/C++ variable access expression.
 */
class VariableAccess extends Access, @varaccess {
  VariableAccess() {
    not exists(EnumConstant c | varbind(this, c))
  }
 
  /** Gets the accessed variable. */
  Variable getTarget() { varbind(this, result) }
 
  /**
   * Holds if this variable access is providing an LValue in a meaningful way.
   * For example, this includes accesses on the left-hand side of an assignment.
   * It does not include accesses on the right-hand side of an assignment, even if they could appear on the left-hand side of some assignment.
   */
  predicate isUsedAsLValue() {
       exists(Assignment a | a.getLValue() = this)
    or exists(CrementOperation c | c.getOperand() = this)
    or exists(AddressOfExpr addof | addof.getOperand() = this)
    or exists(ReferenceToExpr rte | this.getConversion() = rte)
    or exists(ArrayToPointerConversion atpc | this.getConversion() = atpc)
  }
 
  /**
   * Holds if this variable access is in a position where it is (directly) modified,
   * for instance by an assignment or increment/decrement operator.
   */
  predicate isModified() {
       exists(Assignment a | a.getLValue() = this)
    or exists(CrementOperation c | c.getOperand() = this)
    or exists(FunctionCall c | c.getQualifier() = this and c.getTarget().hasName("operator="))
  }
 
  /** Holds if this variable access is an rvalue. */
  predicate isRValue() {
    not exists(AssignExpr ae | ae.getLValue() = this) and
    not exists(AddressOfExpr addof | addof.getOperand() = this) and
    not exists(ReferenceToExpr rte | this.getConversion() = rte) and
    not exists(ArrayToPointerConversion atpc | this.getConversion() = atpc)
  }

  /**
   * Gets the expression generating the variable being accessed.
   *
   * As a few examples:
   * For `ptr->x`, this gives `ptr`.
   * For `(*ptr).x`, this gives `(*ptr)`.
   * For `smart_ptr->x`, this gives the call to `operator->`.
   *
   * This applies mostly to FieldAccesses, but also to static member variables accessed
   * "through" a pointer. Note that it does NOT apply to static member variables accessed
   * through a type name, as in that case the type name is a qualifier on the variable
   * rather than a qualifier on the access.
   */
  Expr getQualifier() { this.getChild(-1) = result }

  /** Gets a textual representation of this variable access. */
  override string toString() {
    if exists(this.getTarget()) then
      result = this.getTarget().getName()
    else
      result = "variable access"
  }

  override predicate mayBeImpure() {
    this.getQualifier().mayBeImpure() or
    this.getTarget().getType().isVolatile()
  }
  override predicate mayBeGloballyImpure() {
    this.getQualifier().mayBeGloballyImpure() or
    this.getTarget().getType().isVolatile()
  }
 
  /**
   * Holds if this access is used to get the address of the underlying variable.
   * Either directly, `&x`, or indirectly, for example `T& y = x`.
   */
  predicate isAddressOfAccess() {
    exists(AddressOfExpr aoe |
      aoe.getOperand() = this
    )
    or
    getConversion+() instanceof ReferenceToExpr
  }
}

/**
 * A C/C++ field access expression.
 */
class FieldAccess extends VariableAccess {
  FieldAccess() { exists(Field f | varbind(this, f)) }

  /** Gets the accessed field. */
  Field getTarget() { result = super.getTarget() }
}

/**
 * A C/C++ function access expression.
 */
class FunctionAccess extends Access, @routineexpr {
  FunctionAccess() { not iscall(this,_) }
 
  /** Gets the accessed function. */
  Function getTarget() { funbind(this, result) }

  /** Gets a textual representation of this function access. */
  override string toString() {
    if exists(this.getTarget()) then
      result = this.getTarget().getName()
    else
      result = "function access"
  }
}

/**
 * An access to a parameter of a function signature for the purposes of a decltype.
 *
 * For example, given the following code:
 * ```
 *   template <typename L, typename R>
 *   auto add(L lhs, R rhs) -> decltype(lhs + rhs) {
 *     return lhs + rhs;
 *   }
 * ```
 * The return type of the function is a decltype, the expression of which contains
 * an add expression, which in turn has two ParamAccessForType children.
 */
class ParamAccessForType extends Expr, @param_ref {
  override string toString() {
    result = "param access"
  }
}

/**
 * An access to a type.  This occurs in certain contexts where a built-in
 * works on types directly rather than variables, expressions etc.
 */
class TypeName extends Expr, @type_operand {
  override string toString() {
    result = this.getType().getName()
  }
}

/**
 * A C/C++ array access expression.
 *
 * For calls to operator[], which look syntactically identical, see OverloadedArrayExpr.
 */
class ArrayExpr extends Expr, @subscriptexpr {
  /**
   * Gets the array or pointer expression being subscripted.
   *
   * This is arr in both arr[0] and 0[arr].
   */
  Expr getArrayBase() { result = this.getChild(0) }

  /**
   * Gets the expression giving the index into the array.
   *
   * This is 0 in both arr[0] and 0[arr].
   */
  Expr getArrayOffset() { result = this.getChild(1) }

  /**
   * Holds if this array access is in a position where it is (directly) modified,
   * for instance by an assignment or an increment/decrement operation.
   */
  predicate isModified() {
       exists(Assignment a | a.getLValue() = this)
    or exists(CrementOperation c | c.getOperand() = this)
    or exists(FunctionCall c | c.getQualifier() = this and c.getTarget().hasName("operator="))
  }

  override string toString() { result = "access to array" }

  override predicate mayBeImpure() {
    this.getArrayBase().mayBeImpure() or
    this.getArrayOffset().mayBeImpure() or
    this.getArrayBase().getFullyConverted().getType().(DerivedType).getBaseType().isVolatile() or
    this.getArrayOffset().getFullyConverted().getType().(DerivedType).getBaseType().isVolatile()
  }
  override predicate mayBeGloballyImpure() {
    this.getArrayBase().mayBeGloballyImpure() or
    this.getArrayOffset().mayBeGloballyImpure() or
    this.getArrayBase().getFullyConverted().getType().(DerivedType).getBaseType().isVolatile() or
    this.getArrayOffset().getFullyConverted().getType().(DerivedType).getBaseType().isVolatile()
  }
}
