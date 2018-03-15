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

private import cpp
private import DataFlowPrivate

Function viableImpl(MethodAccess ma) {
  result = ma.getTarget()
}

Function viableCallable(Call call) {
  result = call.getTarget()
}

/**
 * Holds if the call context `ctx` reduces the set of viable dispatch
 * targets of `ma` in `c`.
 */
predicate reducedViableImplInCallContext(MethodAccess ma, Callable c, Call ctx) {
  none()
}

/**
 * Gets a viable dispatch target of `ma` in the context `ctx`. This is
 * restricted to those `ma`s for which a context might make a difference.
 */
private Method viableImplInCallContext(MethodAccess ma, Call ctx) {
  // stub implementation
  result = viableImpl(ma) and
  viableCallable(ctx) = ma.getEnclosingFunction()
}

/**
 * Gets a viable dispatch target of `ma` in the context `ctx`. This is
 * restricted to those `ma`s for which the context makes a difference.
 */
Method prunedViableImplInCallContext(MethodAccess ma, Call ctx) {
  result = viableImplInCallContext(ma, ctx) and
  reducedViableImplInCallContext(ma, _, ctx)
}

/**
 * Holds if data might flow from `ma` to a return statement in some
 * configuration.
 */
private predicate maybeChainedReturn(MethodAccess ma) {
  exists(ReturnStmt ret |
    exists(ret.getExpr()) and
    ret.getEnclosingFunction() = ma.getEnclosingFunction() and
    not ma.getParent() instanceof ExprStmt
  )
}

/**
 * Holds if flow returning from `m` to `ma` might return further and if
 * this path restricts the set of call sites that can be returned to.
 */
predicate reducedViableImplInReturn(Method m, MethodAccess ma) {
  exists(int tgts, int ctxtgts |
    m = viableImpl(ma) and
    ctxtgts = count(Call ctx | m = viableImplInCallContext(ma, ctx)) and
    tgts = strictcount(Call ctx | viableCallable(ctx) = ma.getEnclosingFunction()) and
    ctxtgts < tgts
  ) and
  maybeChainedReturn(ma)
}

/**
 * Gets a viable dispatch target of `ma` in the context `ctx`. This is
 * restricted to those `ma`s and results for which the return flow from the
 * result to `ma` restricts the possible context `ctx`.
 */
Method prunedViableImplInCallContextReverse(MethodAccess ma, Call ctx) {
  result = viableImplInCallContext(ma, ctx) and
  reducedViableImplInReturn(result, ma)
}
