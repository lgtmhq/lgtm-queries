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
 * @name Illegal invocation
 * @description Attempting to invoke a method or an arrow function using 'new',
 *              or invoking a constructor as a function, will cause a runtime
 *              error.
 * @kind problem
 * @problem.severity error
 * @id js/illegal-invocation
 * @tags correctness
 *       language-features
 * @precision high
 */

import javascript
import semmle.javascript.flow.CallGraph

/**
 * Holds if `f` is a function of kind `fDesc` that cannot be invoked using `new`.
 */
predicate nonConstructible(Function f, string fDesc) {
  f instanceof Method and not f instanceof Constructor and
  fDesc = "a method"
  or
  f instanceof ArrowFunctionExpr and
  fDesc = "an arrow function" 
  or
  f.isGenerator() and
  fDesc = "a generator function"
  or
  f.isAsync() and
  fDesc = "an async function"
}

/**
 * Holds if call site `cs` may invoke function `callee` as specified by `how`.
 */
predicate calls(CallSite cs, Function callee, string how) {
  callee = cs.getACallee() and
  (
    cs instanceof CallExpr and not cs instanceof SuperCall and
    how = "as a function"
    or
    cs instanceof NewExpr and
    how = "using 'new'"
  )
}

/**
 * Holds if call site `cs` may illegally invoke function `callee` as specified by `how`;
 * `calleeDesc` describes what kind of function `callee` is.
 */
predicate illegalInvocation(CallSite cs, Function callee, string calleeDesc, string how) {
  calls(cs, callee, how) and
  (
    how = "as a function" and
    callee instanceof Constructor and
    calleeDesc = "a constructor"
    or
    how = "using 'new'" and
    nonConstructible(callee, calleeDesc)
  )
}

/**
 * Holds if `ce` has at least one call target that isn't a constructor.
 */
predicate isCallToFunction(CallExpr ce) {
  exists (Function f | f = ce.(CallSite).getACallee() |
    not f instanceof Constructor
  )
}

from CallSite cs, Function callee, string calleeDesc, string how
where illegalInvocation(cs, callee, calleeDesc, how) and
      // filter out some easy cases
      not isCallToFunction(cs) and
      // conservatively only flag call sites where _all_ callees are illegal
      forall (Function otherCallee | otherCallee = cs.getACallee() |
        illegalInvocation(cs, otherCallee, _, _)
      )
select cs, "Illegal invocation of $@ " + how + ".", callee, calleeDesc
