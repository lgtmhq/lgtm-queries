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
 * @description If a function is intended to be a constructor, it should always be invoked with 'new'. Otherwise,
 *              it should always be invoked as a normal function, that is, without 'new'.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       language-features
 */

import javascript
import semmle.javascript.flow.CallGraph
import semmle.javascript.RestrictedLocations

/** Check whether f contains code to guard against missing 'new'. There are many ways to implement such
 * a check, but ultimately f will have to call itself using 'new', so that is what we look for.
 */
predicate guardsAgainstMissingNew(Function f) {
	exists (CallSite new |
		((NewExpr)new).getEnclosingFunction() = f and
		f = new.getACallee()
	)
}

from Function f, NewExpr new, CallExpr call
where // externs are special, so don't flag them
      not f.inExternsFile() and
      f = new.(CallSite).getACallee() and
      f = call.(CallSite).getACallee() and
      not guardsAgainstMissingNew(f) and
      not new.(CallSite).isUncertain() and
      not call.(CallSite).isUncertain()
select (FirstLineOf)f, "This function is invoked as a constructor here $@, and as a normal function here $@.",
          new, new.toString(), call, call.toString()