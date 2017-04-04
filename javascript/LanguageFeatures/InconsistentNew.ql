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
 * @name Inconsistent use of 'new'
 * @description If a function is intended to be a constructor, it should always
 *              be invoked with 'new'. Otherwise, it should always be invoked
 *              as a normal function, that is, without 'new'.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       language-features
 * @precision high
 */

import javascript
import semmle.javascript.flow.CallGraph
import semmle.javascript.RestrictedLocations

/**
 * Holds if `f` contains code to guard against being invoked without `new`.
 *
 * There are many ways to implement such a check, but ultimately `f` will
 * have to call itself using `new`, so that is what we look for.
 */
predicate guardsAgainstMissingNew(Function f) {
  exists (CallSite new |
    new.(NewExpr).getEnclosingFunction() = f and
    f = new.getACallee()
  )
}

/**
 * Holds if `callee` is a function that may be invoked at callsite `cs`,
 * where `imprecision` is a heuristic measure of how likely it is that `callee`
 * is only suggested as a potential callee due to imprecise analysis of global
 * variables and is not, in fact, a viable callee at all.
 */
predicate calls(CallSite cs, Function callee, int imprecision) {
  callee = cs.getACallee() and
  (
    // if global flow was used to derive the callee, we may be imprecise
    if cs.isIndefinite("global") then
      // callees within the same file are probably genuine
      callee.getFile() = cs.getFile() and imprecision = 0
      or
      // calls to global functions declared in an externs file are fairly
      // safe as well
      callee.inExternsFile() and imprecision = 1
      or
      // otherwise we make worst-case assumptions
      imprecision = 2
    else
      // no global flow, so no imprecision
      imprecision = 0
  )
}

/**
 * Gets a function that may be invoked at `cs`, preferring callees that
 * are less likely to be derived due to analysis imprecision.
 */
Function getALikelyCallee(CallSite cs) {
  calls(cs, result, min(int p | calls(cs, _, p)))
}

from Function f, NewExpr new, CallExpr call
where // externs are special, so don't flag them
      not f.inExternsFile() and
      // illegal constructor calls are flagged by query 'Illegal invocation',
      // so don't flag them
      not f instanceof Constructor and
      f = getALikelyCallee(new) and
      f = getALikelyCallee(call) and
      not guardsAgainstMissingNew(f) and
      not new.(CallSite).isUncertain() and
      not call.(CallSite).isUncertain() and
      // super constructor calls behave more like `new`, so don't flag them
      not call instanceof SuperCall
select (FirstLineOf)f, capitalize(f.describe()) + " is invoked as a constructor here $@, " +
      "and as a normal function here $@.", new, new.toString(), call, call.toString()
