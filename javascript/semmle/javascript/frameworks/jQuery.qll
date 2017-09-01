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
 * Provides classes for working with jQuery code.
 */

import javascript

/**
 * Holds if `nd` may refer to the jQuery `$` function.
 */
private predicate isJQueryRef(DataFlowNode nd) {
  exists (DataFlowNode src | src = nd.getALocalSource() |
   // either a reference to a global variable `$` or `jQuery`
   src.(GlobalVarAccess).getName() = any(string jq | jq = "$" or jq = "jQuery") or
   // or imported from a module named `jquery`
   src.(ModuleInstance).getPath() = "jquery"
  )
}

/**
 * A (possibly chained) call to a jQuery method.
 */
class JQueryMethodCall extends CallExpr {
  string name;

  JQueryMethodCall() {
    isJQueryRef(getCallee()) and name = "$"
    or
    exists (MethodCallExpr mce | mce = this and name = mce.getMethodName() |
      mce.getReceiver() instanceof JQueryMethodCall or
      isJQueryRef(mce.getReceiver())
    )
  }

  /**
   * Gets the name of the jQuery method this call invokes.
   */
  string getMethodName() {
    result = name
  }
}

/**
 * A call to `jQuery.parseXML`.
 */
private class JQueryParseXmlCall extends XML::ParserInvocation {
  JQueryParseXmlCall() {
    this.(JQueryMethodCall).getMethodName() = "parseXML"
  }

  override DataFlowNode getSourceArgument() {
    result = getArgument(0)
  }

  override predicate resolvesEntities(XML::EntityKind kind) {
    kind = XML::InternalEntity()
  }
}
