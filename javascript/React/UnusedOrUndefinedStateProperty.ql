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
 * @name Unused or undefined state property
 * @description  Unused or undefined component state properties may be a symptom of a bug and should be examined carefully.
 * @kind problem
 * @problem.severity warning
 * @id js/react/unused-or-undefined-state-property
 * @tags correctness
 *       reliability
 *       frameworks/react
 * @precision high
 */

import semmle.javascript.frameworks.React
import semmle.javascript.RestrictedLocations

/**
 * Gets the source for a value that will become the state object of `c`.
 */
DataFlow::SourceNode futureStateSource(ReactComponent c) {
  exists (Assignment def |
    // a direct definition: `this.state = o`
    c.getAStateSource().flowsToExpr(def.getLhs()) and
    result.flowsToExpr(def.getRhs())
  )
  or
  exists (MethodCallExpr mce, DataFlow::SourceNode arg0 |
    mce = c.getAMethodCall("setState") or
    mce = c.getAMethodCall("forceUpdate") |
    arg0.flowsToExpr(mce.getArgument(0)) and
    if arg0 instanceof DataFlow::FunctionNode then
      // setState with callback: `this.setState(() => {foo: 42})`
      result.flowsToExpr(arg0.(DataFlow::FunctionNode).getFunction().getAReturnedExpr())
    else
      // setState with object: `this.setState({foo: 42})`
      result = arg0
  )
  or
  c instanceof ES5Component and
  result.flowsToExpr(c.getInstanceMethod("getInitialState").getAReturnedExpr())
  or
  result.flowsToExpr(c.(ES2015Component).getField("state").getInit())
}

/**
 * Gets the source for a value that used to be the state object of `c`.
 */
DataFlow::SourceNode getAPastStateSource(ReactComponent c) {
  exists (DataFlow::FunctionNode callback, int stateParameterIndex |
    // "prevState" object as callback argument
    callback.getParameter(stateParameterIndex).flowsTo(result) |
    // setState: (prevState, props)
    callback = c.getAMethodCall("setState").flow().(DataFlow::CallNode).getCallback(0) and
    stateParameterIndex = 0
    or
    // componentDidUpdate: (prevProps, prevState)
    callback = c.getInstanceMethod("componentDidUpdate").flow() and
    stateParameterIndex = 1
  )
}

/**
 * Gets the source of a future, present or past state object of `c`.
 */
DataFlow::SourceNode potentialStateSource(ReactComponent c) {
  result = futureStateSource(c) or
  result = c.getAStateSource() or
  result = getAPastStateSource(c)
}

/**
 * Gets an access to a state property of `c`, both future, present or past state objects are considered.
 */
DataFlow::PropRef getAPotentialStateAccess(ReactComponent c) {
  potentialStateSource(c).flowsTo(result.getBase())
}

/**
 * Holds if the state object of `c` escapes from the scope of this file's query.
 */
predicate hasAStateEscape(ReactComponent c) {
  exists (InvokeExpr invk |
    not invk = c.getAMethodCall("setState") and
    potentialStateSource(c).flowsToExpr(invk.getAnArgument())
  )
}

/**
 * Holds if there exists a write for a state property of `c` that uses an unknown property name.
 */
predicate hasUnknownStatePropertyWrite(ReactComponent c) {
  exists (DataFlow::PropWrite pwn |
    pwn = getAPotentialStateAccess(c) and
    not exists (pwn.getPropertyName())
  ) or
  exists (DataFlow::SourceNode source |
    source = futureStateSource(c) and
    not source instanceof DataFlow::ObjectExprNode
  )
}

/**
 * Holds if there exists a read for a state property of `c` that uses an unknown property name.
 */
predicate hasUnknownStatePropertyRead(ReactComponent c) {
  exists (DataFlow::PropRead prn |
    prn = getAPotentialStateAccess(c) and
    not exists (prn.getPropertyName())
  ) or
  exists (SpreadElement spread |
    potentialStateSource(c).flowsToExpr(spread.getOperand())
  )
}

/**
 * Holds if `c` uses the `mixins` mechanism (an obsolete React feature) .
 */
predicate usesMixins(ES5Component c) {
  c.flow().(DataFlow::SourceNode).hasPropertyWrite("mixins", _)
}

/**
 * Gets a write for a state property of `c` that has no corresponding read.
 */
DataFlow::PropWrite getAnUnusedStateProperty(ReactComponent c) {
  result = getAPotentialStateAccess(c) and
  exists (string name |
    name = result.getPropertyName() |
    not exists(DataFlow::PropRead prn |
      prn = getAPotentialStateAccess(c) and
      prn.getPropertyName() = name
    )
  )
}

/**
 * Gets a read for a state property of `c` that has no corresponding write.
 */
DataFlow::PropRead getAnUndefinedStateProperty(ReactComponent c) {
  result = getAPotentialStateAccess(c) and
  exists (string name |
    name = result.getPropertyName() |
    not exists(DataFlow::PropWrite pwn |
      pwn = getAPotentialStateAccess(c) and
      pwn.getPropertyName() = name
    )
  )
}

from ReactComponent c, DataFlow::PropRef n, string action, string nonAction
where (
      action = "written" and nonAction = "read" and
      n = getAnUnusedStateProperty(c) and
      not hasUnknownStatePropertyRead(c)
      or
      action = "read" and nonAction = "written" and
      n = getAnUndefinedStateProperty(c) and
      not hasUnknownStatePropertyWrite(c)
      ) and
      not hasAStateEscape(c) and
      not usesMixins(c)
select (FirstLineOf)c, "Component state property '" + n.getPropertyName() + "' is $@, but it is never " + nonAction + ".", n, action
