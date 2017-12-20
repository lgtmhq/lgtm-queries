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
 * @name Dead AngularJS event listener
 * @description An AngularJS event listener that listens for a non-existent event has no effect.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id js/angular/dead-event-listener
 * @tags correctness
 *       frameworks/angularjs
 */

import javascript

/**
 * Holds if the name is a known AngularJS event name.
 */
predicate isABuiltinEventName(string name) {
  // $rootScope.Scope
  name = "$destroy" or

  // $location
  name = "$locationChangeStart" or
  name = "$locationChangeSuccess" or

  // ngView
  name = "$viewContentLoaded" or

  // angular-ui/ui-router
  name = "$stateChangeStart" or
  name = "$stateNotFound" or
  name = "$stateChangeSuccess" or
  name = "$stateChangeError" or
  name = "$viewContentLoading " or
  name = "$viewContentLoaded " or

  // $route
  name = "$routeChangeStart" or
  name = "$routeChangeSuccess" or
  name = "$routeChangeError" or
  name = "$routeUpdate" or

  // ngInclude
  name = "$includeContentRequested" or
  name = "$includeContentLoaded" or
  name = "$includeContentError"
}

/**
 * Holds if user code emits or broadcasts an event named `name`.
 */
predicate isAUserDefinedEventName(string name) {
  exists (string methodName, MethodCallExpr mce |
    methodName = "$emit" or methodName = "$broadcast" |
    name = mce.getArgument(0).(DataFlowNode).getALocalSource().(ConstantString).getStringValue() and
    (
      // dataflow based scope resolution
      mce = any(AngularJS::ScopeServiceReference scope).getAMethodCall(methodName) or
      // heuristic scope resolution: assume parameters like `$scope` or `$rootScope` are AngularJS scope objects
      exists(SimpleParameter param |
        param.getName() = any(AngularJS::ScopeServiceReference scope).getName() and
        mce.getReceiver().(DataFlowNode).getALocalSource() = param.getAnInitialUse() and
        mce.getMethodName() = methodName
      ) or
      // a call in an AngularJS expression
      exists (AngularJS::NgCallExpr call |
        call.getCallee().(AngularJS::NgVarExpr).getName() = methodName and
        call.getArgument(0).(AngularJS::NgString).getStringValue() = name
      )
    )
  )
}

from AngularJS::ScopeServiceReference scope, MethodCallExpr mce, DataFlowNode event, string eventName
where mce = scope.getAMethodCall("$on") and
      event = mce.getArgument(0).(DataFlowNode).getALocalSource() and
      eventName = event.(ConstantString).getStringValue() and
      not (
        isAUserDefinedEventName(eventName) or
        isABuiltinEventName(eventName) or
        // external, namespaced
        eventName.regexpMatch(".*[.:].*") or
        // from other event system (DOM: onClick et al)
        eventName.regexpMatch("on[A-Z][a-zA-Z]+") // camelCased with 'on'-prefix
        )
select mce.getArgument(1), "This event listener is dead, the event '" + eventName + "' is not emitted anywhere."
