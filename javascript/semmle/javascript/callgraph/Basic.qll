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
 * This is the simplest call graph builder. It only considers flow through variables,
 * not through properties. Consequently it only computes targets for function calls of the form
 * 'f()', not for method calls of the form 'e.m()'.
 */

import semmle.javascript.Expr
import FunctionFlow

/** Entry point for call graph construction. */
class CallSite extends InvokeExpr {
	private FunctionFlow getCalleeFlow() {
		result = getCallee()
	}
	
	Function getACallee() {
		result = getCalleeFlow().getAFunctionValue()
	}
	
	/**
	 * Is our approximation of possible callees for this call site incomplete due to untracked
	 * data flow? 
	 */
	predicate isIncomplete() {
		getCalleeFlow().isIncomplete()
	}
}
