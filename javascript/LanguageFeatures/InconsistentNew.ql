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
 * Gets a function that may be invoked at `cs` and that is in the same
 * file as `cs`.
 */
Function getACalleeInSameFile(CallSite cs) {
  result = cs.getACallee() and
  result.getFile() = cs.getFile()
}

/**
 * Gets a function that may be invoked at `cs`, preferring functions in
 * the same file over those in other files.
 */
Function getALikelyCallee(CallSite cs) {
  result = getACalleeInSameFile(cs)
  or
  not exists(getACalleeInSameFile(cs)) and result = cs.getACallee()
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
