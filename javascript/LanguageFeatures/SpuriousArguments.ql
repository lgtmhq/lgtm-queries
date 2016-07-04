// Copyright 2016 Semmle Ltd.
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
 */

import default
import semmle.javascript.callgraph.Basic

/* the function's name, or "(anonymous)" if it doesn't have one */
string functionName(Function f) {
	if exists(f.getName()) then
		result = f.getName()
	else
		result = "(anonymous)"
}

from CallSite invk, Function f
where not invk.isIncomplete() and
      f = invk.getACallee() and
      forall (Function g | g = invk.getACallee() |
        invk.getNumArgument() > g.getNumParameter() and
        not g.usesArgumentsObject() and
        not g.hasRestParameter() and
        // if g is an external function, it is not a varargs function
        (g instanceof ExternalFunction implies not g.(ExternalFunction).isVarArgs())
      )
select invk, "Superfluous arguments passed to function $@.", f, functionName(f)
