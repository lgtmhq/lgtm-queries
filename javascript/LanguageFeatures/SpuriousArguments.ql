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
 * @name Superfluous trailing arguments
 * @description A function is invoked with extra trailing arguments that are ignored.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       correctness
 *       language-features
 */

import javascript
import semmle.javascript.flow.CallGraph

/**
 * The function's name, or "(anonymous)" if it doesn't have one.
 */
string functionName(Function f) {
  if exists(f.getName()) then
    result = f.getName()
  else
    result = "(anonymous)"
}

/**
 * Check whether `fn` expects a fixed number of arguments, that is,
 * it neither uses `arguments` nor has a rest parameter.
 */
predicate isFixedArity(Function fn) {
  not fn.usesArgumentsObject() and
  not fn.hasRestParameter() and
  (fn instanceof ExternalFunction implies not fn.(ExternalFunction).isVarArgs())
}

/**
 * The maximum arity of any function that may be invoked at
 * call site `invk`. This is only defined if all potential
 * callees have a fixed arity.
 */
int maxArity(CallSite invk) {
  forall (Function callee | callee = invk.getACallee() | isFixedArity(callee)) and
  result = max(invk.getACallee().getNumParameter())
}

/**
 * Call site `invk` has more arguments than the maximum arity
 * of any function that it may invoke, and the first of those
 * arguments is `arg`. This predicate only holds for call sites
 * where callee information is complete.
 */
predicate firstSpuriousArgument(CallSite invk, Expr arg) {
  arg = invk.getArgument(maxArity(invk)) and
  not invk.isIncomplete()
}

/**
 * A list of spurious arguments passed at a call site.
 *
 * The list is represented by its first element (that is,
 * the first spurious argument), but `hasLocationInfo` is
 * overridden to cover all subsequent arguments as well.
 */
class SpuriousArguments extends Expr {
  SpuriousArguments() {
    firstSpuriousArgument(_, this)
  }

  /**
   * The call site at which the spurious arguments are passed.
   */
  CallSite getCall() {
    firstSpuriousArgument(result, this)
  }

  /**
   * The number of spurious arguments, that is, the number of
   * actual arguments minus the maximum number of arguments
   * expected by any potential callee.
   */
  int getCount() {
    result = getCall().getNumArgument() - maxArity(getCall())
  }

  predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
    this.getLocation().hasLocationInfo(filepath, bl, bc, _, _) and
    exists (Expr lastArg | lastArg = getCall().getArgument(getCall().getNumArgument()-1) |
      lastArg.getLocation().hasLocationInfo(_, _, _, el, ec)
    )
  }
}

from SpuriousArguments args, Function f, string arguments
where f = args.getCall().getACallee() and
      if args.getCount() = 1 then arguments = "argument" else arguments = "arguments"
select args, "Superfluous " + arguments + " passed to function $@.", f, functionName(f)