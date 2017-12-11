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
 * @name Insecure URL whitelist
 * @description URL whitelists that are too permissive can cause security vulnerabilities.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id js/angular/insecure-url-whitelist
 * @tags security
 *       frameworks/angularjs
 *       external/cwe/cwe-183
 *       external/cwe/cwe-625
 */

import javascript

/**
 * Holds if `entry` is insecure to use in an URL pattern whitelist and `explanation` explains why it is insecure.
 */
predicate isInsecureWhitelistEntry(Expr urlExpr, string explanation) {
  exists(string componentName, string component |
    exists(int componentNumber |
      (componentName = "scheme" and componentNumber = 1) or
      (componentName = "domain" and componentNumber = 2) or
      (componentName = "TLD" and componentNumber = 4) |
      component = urlExpr.(ConstantString).getStringValue().regexpCapture("(.*?)://(.*?(\\.(.*?))?)(:\\d+)?(/.*)?", componentNumber)
    ) and
    explanation = "the " + componentName + " '" + component + "' is insecurely specified" |
    (componentName = "scheme" and component.matches("%*%")) or
    (componentName = "domain" and component.matches("%**%")) or
    (componentName = "TLD" and component = "*")
  )
}

from MethodCallExpr setupCall, ArrayExpr list, Expr entry, string explanation, AngularJS::ServiceReference service
where service.getName() = "$sceDelegateProvider" and
      setupCall = service.getAMethodCall("resourceUrlWhitelist") and
      list = setupCall.getArgument(0).(DataFlowNode).getALocalSource() and
      entry = list.getElement(_).(DataFlowNode).getALocalSource() and
      isInsecureWhitelistEntry(entry, explanation)
select setupCall, "'$@' is not a secure whitelist entry, because " + explanation + ".", entry, entry.toString()
