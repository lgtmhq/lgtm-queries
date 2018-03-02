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

/**
 * Provides predicates for giving improved type bounds on expressions.
 *
 * An inferred bound on the runtime type of an expression can be either exact
 * or merely an upper bound. Bounds are only reported if they are likely to be
 * better than the static bound, which can happen either if an inferred exact
 * type has a subtype or if an inferred upper bound passed through at least one
 * explicit or implicit cast that lost type information.
 */
import java
import semmle.code.java.dispatch.VirtualDispatch
import semmle.code.java.dataflow.internal.BaseSSA

private newtype TTypeFlowNode =
  TField(Field f) or
  TSsa(BaseSsaVariable ssa) or
  TExpr(Expr e) or
  TMethod(Method m)

/**
 * A `Field`, `BaseSsaVariable`, `Expr`, or `Method`.
 */
private class TypeFlowNode extends TTypeFlowNode {
  string toString() {
    result = asField().toString() or
    result = asSsa().toString() or
    result = asExpr().toString() or
    result = asMethod().toString()
  }
  Location getLocation() {
    result = asField().getLocation() or
    result = asSsa().getLocation() or
    result = asExpr().getLocation() or
    result = asMethod().getLocation()
  }
  Field asField() { this = TField(result) }
  BaseSsaVariable asSsa() { this = TSsa(result) }
  Expr asExpr() { this = TExpr(result) }
  Method asMethod() { this = TMethod(result) }
}

/**
 * Holds if `arg` is an argument for the parameter `p` in a private callable.
 */
private predicate privateParamArg(Parameter p, Argument arg) {
  p.getAnArgument() = arg and
  p.getCallable().isPrivate()
}

/**
 * Holds if data can flow from `n1` to `n2` in one step, and `n1` is not
 * necessarily functionally determined by `n2`.
 */
private predicate joinStep0(TypeFlowNode n1, TypeFlowNode n2) {
  n2.asExpr().(ConditionalExpr).getTrueExpr() = n1.asExpr() or
  n2.asExpr().(ConditionalExpr).getFalseExpr() = n1.asExpr() or
  n2.asField().getAnAssignedValue() = n1.asExpr() or
  n2.asSsa().(BaseSsaPhiNode).getAPhiInput() = n1.asSsa() or
  exists(ReturnStmt ret | n2.asMethod() = ret.getEnclosingCallable() and ret.getResult() = n1.asExpr()) or
  viableImpl_v1(n2.asExpr()) = n1.asMethod()
  or
  exists(Argument arg, Parameter p |
    privateParamArg(p, arg) and
    n1.asExpr() = arg and
    n2.asSsa().(BaseSsaImplicitInit).isParameterDefinition(p)
  )
}

/**
 * Holds if data can flow from `n1` to `n2` in one step, and `n1` is
 * functionally determined by `n2`.
 */
private predicate step(TypeFlowNode n1, TypeFlowNode n2) {
  n2.asExpr() = n1.asField().getAnAccess() or
  n2.asExpr() = n1.asSsa().getAUse() or
  n2.asExpr().(ParExpr).getExpr() = n1.asExpr() or
  n2.asExpr().(CastExpr).getExpr() = n1.asExpr() or
  n2.asExpr().(AssignExpr).getSource() = n1.asExpr() or
  n2.asSsa().(BaseSsaUpdate).getDefiningExpr().(VariableAssign).getSource() = n1.asExpr() or
  n2.asSsa().(BaseSsaImplicitInit).captures(n1.asSsa())
}

/**
 * Holds if `null` is the only value that flows to `n`.
 */
private predicate isNull(TypeFlowNode n) {
  n.asExpr() instanceof NullLiteral or
  exists(TypeFlowNode mid | isNull(mid) and step(mid, n)) or
  forex(TypeFlowNode mid | joinStep0(mid, n) | isNull(mid))
}

/**
 * Holds if data can flow from `n1` to `n2` in one step, `n1` is not necessarily
 * functionally determined by `n2`, and `n1` might take a non-null value.
 */
private predicate joinStep(TypeFlowNode n1, TypeFlowNode n2) {
  joinStep0(n1, n2) and not isNull(n1)
}

/**
 * Holds if the runtime type of `n` is exactly `t` and if this bound is a
 * non-trivial lower bound, that is, `t` has a subtype.
 */
private predicate exactType(TypeFlowNode n, RefType t) {
  exists(ClassInstanceExpr e |
    n.asExpr() = e and
    e.getType() = t and
    exists(RefType sub | sub.getASourceSupertype() = t.getSourceDeclaration())
  ) or
  exists(TypeFlowNode mid | exactType(mid, t) and step(mid, n)) or
  forex(TypeFlowNode mid | joinStep(mid, n) | exactType(mid, t))
}

/** Holds if `e` occurs in a position where type information is discarded. */
private predicate upcast(Expr e) {
  exists(RefType t1, RefType t2 |
    e.getType().getErasure() = t1 and
    t1.getASourceSupertype+() = t2
    |
    exists(Variable v | v.getAnAssignedValue() = e and t2 = v.getType().getErasure()) or
    exists(CastExpr c | c.getExpr() = e and t2 = c.getType().getErasure()) or
    exists(ReturnStmt ret | ret.getResult() = e and t2 = ret.getEnclosingCallable().getReturnType().getErasure()) or
    exists(Parameter p | privateParamArg(p, e) and t2 = p.getType().getErasure()) or
    exists(ConditionalExpr cond | cond.getTrueExpr() = e or cond.getFalseExpr() = e | t2 = cond.getType().getErasure())
  )
}

/** Gets the element type of an array or subtype of `Iterable`. */
private Type elementType(RefType t) {
  result = t.(Array).getComponentType() or
  exists(ParameterizedType it |
    it.getSourceDeclaration().hasQualifiedName("java.lang", "Iterable") and
    result = it.getATypeArgument() and
    t.extendsOrImplements*(it)
  )
}

/**
 * Holds if `v` is the iteration variable of an enhanced for statement, `t` is
 * the type of the elements being iterated over, and this type is more precise
 * than the type of `v`.
 */
private predicate upcastEnhancedForStmt(BaseSsaUpdate v, RefType t) {
  exists(EnhancedForStmt for, RefType t1, RefType t2 |
    for.getVariable() = v.getDefiningExpr() and
    v.getSourceVariable().getType().getErasure() = t2 and
    t = elementType(for.getExpr().getType()) and
    t.getErasure() = t1 and
    t1.getASourceSupertype+() = t2
  )
}

/**
 * Holds if `t` is a bound that holds on one of the incoming edges to `n` and
 * thus is a candidate bound for `n`.
 */
pragma[noinline]
private predicate typeFlowJoinCand(TypeFlowNode n, RefType t) {
  exists(TypeFlowNode mid | joinStep(mid, n) | typeFlow(mid, t))
}

/**
 * Holds if `t` is a candidate bound for `n` that is also valid for data coming
 * through the edge from `mid` to `n`.
 */
private predicate typeFlowJoinEdge(TypeFlowNode mid, TypeFlowNode n, RefType t) {
  joinStep(mid, n) and
  typeFlowJoinCand(n, t) and
  exists(RefType midtyp |
    exactType(mid, midtyp) or typeFlow(mid, midtyp)
    |
    midtyp.getASupertype*() = t
  )
}

/**
 * Holds if the runtime type of `n` is bounded by `t` and if this bound is
 * likely to be better than the static type of `n`.
 */
private predicate typeFlow(TypeFlowNode n, RefType t) {
  exists(Expr e | n.asExpr() = e and upcast(e) and t = e.getType()) or
  upcastEnhancedForStmt(n.asSsa(), t) or
  exists(TypeFlowNode mid | typeFlow(mid, t) and step(mid, n)) or
  forex(TypeFlowNode mid | joinStep(mid, n) | typeFlowJoinEdge(mid, n, t))
}

/**
 * Holds if we have a bound for `n` that is better than `t`.
 */
pragma[noinline]
private predicate irrelevantBound(TypeFlowNode n, RefType t) {
  exists(RefType bound |
    typeFlow(n, bound) and
    t = bound.getErasure().(RefType).getASourceSupertype+()
  )
}

/**
 * Holds if the runtime type of `n` is bounded by `t`, if this bound is likely
 * to be better than the static type of `n`, and if this the best such bound.
 */
private predicate bestTypeFlow(TypeFlowNode n, RefType t) {
  typeFlow(n, t) and
  not irrelevantBound(n, t.getErasure())
}

/**
 * Holds if the runtime type of `e` is bounded by `t` and if this bound is
 * likely to be better than the static type of `e`. The flag `exact` indicates
 * whether `t` is an exact bound or merely an upper bound.
 */
predicate exprTypeFlow(Expr e, RefType t, boolean exact) {
  exists(TypeFlowNode n, RefType srctype |
    n.asExpr() = e and
    (
      exactType(n, srctype) and exact = true
      or
      not exactType(n, _) and bestTypeFlow(n, srctype) and exact = false
    )
    |
    t = srctype.(BoundedType).getAnUltimateUpperBoundType() or
    t = srctype and not srctype instanceof BoundedType
  )
}
