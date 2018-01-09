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
 * @name Potentially inconsistent state update
 * @description Updating the state of a component based on the current value of
 *              'this.state' or 'this.props' may lead to inconsistent component
 *              state.
 * @kind problem
 * @problem.severity warning
 * @id js/react/inconsistent-state-update
 * @tags reliability
 *       frameworks/react
 * @precision very-high
 */

import semmle.javascript.frameworks.React

/**
 * Gets an unsafe property access, that is, an expression that reads (a property of)
 * `this.state` or `this.prop` on component `c`.
 */
PropReadNode getAnUnsafeAccess(ReactComponent c) {
  result = c.getAPropRead() or
  result = c.getAStateAccess()
}

/**
 * Gets at unsafe property access that is not the base of another unsafe property
 * access.
 */
PropRefNode getAnOutermostUnsafeAccess(ReactComponent c) {
  result = getAnUnsafeAccess(c)
  and
  not exists (PropAccess outer | outer = getAnUnsafeAccess(c) |
    result = outer.getBase()
  )
}

from ReactComponent c, MethodCallExpr setState, Expr getState
where setState.getReceiver() = c.getAThisAccess() and
      setState.getMethodName() = "setState" and
      getState = getAnOutermostUnsafeAccess(c) and
      getState.getParentExpr*() = setState.getArgument(0) and
      getState.getEnclosingFunction() = setState.getEnclosingFunction()
select setState, "Component state update uses $@.", getState, "potentially inconsistent value"