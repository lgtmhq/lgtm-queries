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
 * INTERNAL: This is an internal library; its interface may change without notice.
 *
 * Provides classes for working with variable refinements.
 *
 * Variable refinements are expressions that appear in a guard node
 * (such as an `if` condition) and can be used to refine the information
 * derived about a variable by the flow analysis. Each refinement only
 * refines a single variable, and only certain simple constructs are
 * considered (primarily `typeof` expressions and comparisons).
 *
 * To perform the refinement, the expression is evaluated to a
 * `RefinementValue`, which is a more fine-grained version of `AbstractValue`
 * that distinguishes individual constants value. This evaluation takes place
 * in a context that restricts the value of the refined variable to a single
 * candidate value, which is one of the `AbstractValue`s that the flow analysis
 * infers for it.
 *
 * If the expression evaluates to a refinement value that represents `true`,
 * then the candidate value passes the refinement. Hence, it can be propagated
 * across a condition guard with outcome `true`.
 *
 * Conversely, if it evaluates to `false`, the candidate value can be propagated
 * across a condition guard with outcome `false`.
 *
 * Note that, like all abstract values, refinement values are overapproximations,
 * so the refinement can evaluate to both `true` and `false` for the same
 * candidate value.
 */

import javascript
private import AbstractValues
private import InferredTypes
private import Analysis

/**
 * An expression that has the right syntactic structure to be used to
 * refine the abstract values inferred for a variable.
 */
abstract class RefinementCandidate extends Expr {
  /**
   * Gets a variable that is referenced somewhere in this expression.
   */
  abstract SsaSourceVariable getARefinedVar();

  /**
   * Gets a refinement value inferred for this expression in context `ctxt`.
   */
  abstract pragma[nomagic] RefinementValue eval(RefinementContext ctxt);
}

/**
 * A refinement candidate that references at most one variable, and hence
 * can be used to refine the abstract values inferred for that variable.
 */
class Refinement extends Expr {
  Refinement() {
    this instanceof RefinementCandidate and
    count(this.(RefinementCandidate).getARefinedVar()) <= 1
  }

  /**
   * Gets the variable refined by this expression, if any.
   */
  SsaSourceVariable getRefinedVar() {
    result = this.(RefinementCandidate).getARefinedVar()
  }

  /**
   * Gets a refinement value inferred for this expression in context `ctxt`.
   */
  RefinementValue eval(RefinementContext ctxt) {
    result = this.(RefinementCandidate).eval(ctxt)
  }
}

/** A literal, viewed as a refinement expression. */
private class LiteralRefinement extends RefinementCandidate, Literal {
  override SsaSourceVariable getARefinedVar() {
    none()
  }

  override RefinementValue eval(RefinementContext ctxt) {
    ctxt.appliesTo(this) and result = eval()
  }

  /**
   * Gets the refinement value that represents this literal.
   */
  RefinementValue eval() {
    result = TAny()
  }
}

/** A `null` literal, viewed as a refinement expression. */
private class NullLiteralRefinement extends LiteralRefinement, NullLiteral {
  override RefinementValue eval() {
    result = TValueWithType(TTNull())
  }
}

/** A Boolean literal, viewed as a refinement expression. */
private class BoolRefinement extends LiteralRefinement, BooleanLiteral {
  override RefinementValue eval() {
    exists (boolean b | b.toString() = getValue() |
      result = TBoolConstant(b)
    )
  }
}

/** A string literal, viewed as a refinement expression. */
private class StringRefinement extends LiteralRefinement, StringLiteral {
  override RefinementValue eval() {
    result = TStringConstant(getValue())
  }
}

/** A numeric literal, viewed as a refinement expression. */
private class NumberRefinement extends LiteralRefinement, NumberLiteral {
  override RefinementValue eval() {
    result = TValueWithType(TTNumber())
  }
}

/** An integer literal, viewed as a refinement expression. */
private class IntRefinement extends NumberRefinement {
  IntRefinement() { exists(getValue().toInt()) }

  override RefinementValue eval() {
    result = TIntConstant(getValue().toInt())
  }
}

/** A variable use, viewed as a refinement expression. */
private class VariableRefinement extends RefinementCandidate, VarUse {
  VariableRefinement() {
    getVariable() instanceof SsaSourceVariable
  }

  override SsaSourceVariable getARefinedVar() {
    result = getVariable()
  }

  override RefinementValue eval(RefinementContext ctxt) {
    ctxt.appliesTo(this) and
    result = TValueWithType(ctxt.(VarRefinementContext).getAType())
  }
}

/** A parenthesized refinement expression. */
private class ParRefinement extends RefinementCandidate, ParExpr {
  ParRefinement() {
    getExpression() instanceof RefinementCandidate
  }

  override SsaSourceVariable getARefinedVar() {
    result = getExpression().(RefinementCandidate).getARefinedVar()
  }

  override RefinementValue eval(RefinementContext ctxt) {
    result = getExpression().(RefinementCandidate).eval(ctxt)
  }
}

/** A `typeof` refinement expression. */
private class TypeofRefinement extends RefinementCandidate, TypeofExpr {
  TypeofRefinement() {
    getOperand() instanceof RefinementCandidate
  }

  override SsaSourceVariable getARefinedVar() {
    result = getOperand().(RefinementCandidate).getARefinedVar()
  }

  override RefinementValue eval(RefinementContext ctxt) {
    exists (RefinementValue opVal |
      opVal = getOperand().(RefinementCandidate).eval(ctxt) and
      result = TStringConstant(opVal.typeof())
    )
  }
}

/** An equality test that can be used as a refinement expression. */
private class EqRefinement extends RefinementCandidate, EqualityTest {
  EqRefinement() {
    getLeftOperand() instanceof RefinementCandidate and
    getRightOperand() instanceof RefinementCandidate
  }

  override SsaSourceVariable getARefinedVar() {
    result = getLeftOperand().(RefinementCandidate).getARefinedVar() or
    result = getRightOperand().(RefinementCandidate).getARefinedVar()
  }

  override RefinementValue eval(RefinementContext ctxt) {
    exists (RefinementCandidate l, RefinementValue lv, RefinementCandidate r, RefinementValue rv |
      l = getLeftOperand() and r = getRightOperand() and
      lv = l.eval(ctxt) and rv = r.eval(ctxt) |
      // if both sides evaluate to a constant, compare them
      if exists(lv.getLiteral()) and exists(rv.getLiteral()) then
        exists (string ls, string rs, boolean b |
          ls = lv.getLiteral() and rs = rv.getLiteral() and result = TBoolConstant(b) |
          ls = rs and b = getPolarity() or
          ls != rs and b = getPolarity().booleanNot()
        )
      // otherwise give up
      else
        result = TValueWithType(TTBoolean())
    )
  }
}

/** An index expression that can be used as a refinement expression. */
private class IndexRefinement extends RefinementCandidate, IndexExpr {
  IndexRefinement() {
    getBase() instanceof RefinementCandidate and
    getIndex() instanceof RefinementCandidate
  }

  override SsaSourceVariable getARefinedVar() {
    result = getBase().(RefinementCandidate).getARefinedVar() or
    result = getIndex().(RefinementCandidate).getARefinedVar()
  }

  override RefinementValue eval(RefinementContext ctxt) {
    exists (RefinementCandidate base, RefinementValue baseVal,
            RefinementCandidate index, RefinementValue indexVal |
      base = getBase() and index = getIndex() and
      baseVal = base.eval(ctxt) and indexVal = index.eval(ctxt) |
      if exists(evalIndex(baseVal, indexVal)) then
        result = evalIndex(baseVal, indexVal)
      else
        result = TAny()
    )
  }
}

/**
 * Gets the abstract value representing the `i`th character of `s`,
 * if any.
 */
private bindingset[s, i]
RefinementValue evalIndex(StringConstant s, IntConstant i) {
  result = TStringConstant(s.getValue().charAt(i.getValue()))
}

/**
  * A context in which a refinement expression is analyzed.
 */
newtype TRefinementContext =
  /**
   * A refinement context associated with refinement `ref`, specifying that variable `var`
   * is assumed to have abstract value `val`.
   *
   * Each context keeps track of its associated `AnalyzedRefinement` node so that we can
   * restrict the `RefinementCandidate` expressions that it applies to: it should only
   * apply to those expressions that are syntactically nested inside the `AnalyzedRefinement`.
   */
  TVarRefinementContext(AnalyzedRefinement ref, SsaSourceVariable var, AbstractValue val) {
    var = ref.getSourceVariable() and
    val = ref.getAnInputRhsValue()
  }

/**
 * A context in which a refinement expression is analyzed.
 */
class RefinementContext extends TRefinementContext {
  /**
   * Holds if refinement expression `cand` might be analyzed in this context.
   */
  abstract predicate appliesTo(RefinementCandidate cand);

  /** Gets a textual representation of this element. */
  abstract string toString();
}

/**
 * A refinement context specifying that some variable is assumed to have one particular
 * abstract value.
 */
class VarRefinementContext extends RefinementContext, TVarRefinementContext {
  override predicate appliesTo(RefinementCandidate cand) {
    exists (AnalyzedRefinement ref, SsaSourceVariable var |
      this = TVarRefinementContext(ref, var, _) |
      cand = ref.getRefinement().getAChildExpr*() and
      not cand.getARefinedVar() != var
    )
  }

  /**
   * Gets a type corresponding to the abstract value the variable is assumed to have.
   */
  InferredType getAType() {
    exists (AbstractValue val | this = TVarRefinementContext(_, _, val) |
      result = val.getType()
    )
  }

  override string toString() {
    exists (Variable var, AbstractValue val | this = TVarRefinementContext(_, var, val) |
      result = "[" + var + " = " + val + "]"
    )
  }
}

/** Holds if `e` is nested inside a guard node. */
private predicate inGuard(Expr e) {
  e.getParentExpr*() = any(GuardControlFlowNode g).getTest()
}

/**
 * An abstract value of a refinement expression.
 */
private newtype TRefinementValue =
  /** An abstract value indicating that no refinement information is available. */
  TAny()
  or
  /** An abstract value representing all concrete values of type `tp`. */
  TValueWithType(InferredType tp)
  or
  /** An abstract value representing the Boolean value `b`. */
  TBoolConstant(boolean b) {
    b = true or b = false
  }
  or
  /**
   * An abstract value representing the string `s`.
   *
   * There are abstract values for every string literal appearing anywhere
   * in a guard node, as well as for `typeof` tags and their characters.
   */
  TStringConstant(string s) {
    s instanceof TypeofTag
    or
    s = any(StringRefinement sr | inGuard(sr)).getValue()
    or
    s = any(TypeofTag t).charAt(_)
  }
  or
  /**
   * An abstract value representing the integer `i`.
   *
   * There are abstract values for every integer literal appearing anywhere
   * in a guard node.
   */
  TIntConstant(int i) {
    i = any(IntRefinement ir | inGuard(ir)).getValue().toInt()
  }

/**
 * An abstract value of a refinement expression.
 */
class RefinementValue extends TRefinementValue {
  /** Gets a textual representation of this element. */
  abstract string toString();

  /**
   * Gets a representation of the constant value represented by this abstract value,
   * if any.
   *
   * For string constants, this is the string value surrounded by double quotes;
   * for non-string constants, it is the value itself.
   */
  abstract string getLiteral();

  /**
   * Gets the `typeof` tag of a concrete value represented by this abstract value.
   */
  abstract string typeof();

  /**
   * Gets the Boolean value of a concrete value represented by this abstract value.
   */
  abstract boolean getABooleanValue();
}

/** An abstract value indicating that no refinement information is available. */
private class AnyValue extends RefinementValue, TAny {
  override string toString() { result = "any value" }
  override string typeof() { result instanceof TypeofTag }
  override boolean getABooleanValue() { result = true or result = false }
  override string getLiteral() { none() }
}

/** An abstract value representing all concrete values of some `InferredType`. */
private class ValueWithType extends RefinementValue, TValueWithType {
  InferredType getType() { this = TValueWithType(result) }
  override string toString() { result = "any " + getType() }
  override string typeof() { result = getType().getTypeofTag() }
  override boolean getABooleanValue() { result = true or result = false }
  override string getLiteral() { none() }
}

/** An abstract value representing `null` or `undefined`. */
private class FalsyValueWithType extends ValueWithType {
  FalsyValueWithType() { getType() instanceof TTNull or getType() instanceof TTUndefined }
  override boolean getABooleanValue() { result = false }
  override string getLiteral() { result = getType().toString() }
}

/** An abstract value representing a Boolean constant. */
private class BoolConstant extends RefinementValue, TBoolConstant {
  /** Gets the Boolean value represented by this abstract value. */
  boolean getValue() { this = TBoolConstant(result) }

  override string toString() { result = getLiteral() }
  override string typeof() { result = "boolean" }
  override boolean getABooleanValue() { result = getValue() }
  override string getLiteral() { result = getValue().toString() }
}

/** An abstract value representing a string constant. */
private class StringConstant extends RefinementValue, TStringConstant {
  /** Gets the string represented by this abstract value. */
  string getValue() { this = TStringConstant(result) }

  override string toString() { result = getLiteral() }
  override string typeof() { result = "string" }
  override boolean getABooleanValue() {
    if getValue() = "" then
      result = false
    else
      result = true
  }
  override string getLiteral() { result = "'" + getValue() + "'" }
}

/** An abstract value representing an integer value. */
private class IntConstant extends RefinementValue, TIntConstant {
  /** Gets the integer value represented by this abstract value. */
  int getValue() { this = TIntConstant(result) }

  override string toString() { result = getLiteral() }
  override string typeof() { result = "number" }
  override boolean getABooleanValue() {
    if getValue() = 0 then
      result = false
    else
      result = true
  }
  override string getLiteral() { result = getValue().toString() }
}
