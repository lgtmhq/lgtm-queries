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
 * Provides classes for working with [Express](https://expressjs.com) applications.
 */

import javascript
import semmle.javascript.frameworks.HTTP

module Express {
  /**
   * Holds if `e` creates an Express router.
   */
  predicate isRouterCreation(InvokeExpr e) {
    exists (ModuleInstance express | express.getPath() = "express" |
      // `app = express()`
      e.getCallee().(DataFlowNode).getALocalSource() = express
      or
      // `app = express.createServer()`
      e = express.getAMethodCall("createServer")
      or
      // `app = express.Router()`
      e = express.getAMethodCall("Router")
    )
  }

  /**
   * Holds if `e` is a router object.
   */
  private predicate isRouter(DataFlowNode e) {
    isRouterCreation(e.getALocalSource())
    or
    isRouter(e.(RouteSetup).getReceiver())
  }

  /**
   * Holds if `e` is a route object.
   */
  private predicate isRoute(MethodCallExpr e) {
    isRouter(e.getReceiver()) and e.getMethodName() = "route"
    or
    isRoute(e.(RouteSetup).getReceiver())
  }

  /**
   * A call to an Express method that sets up a route.
   */
  class RouteSetup extends MethodCallExpr {
    RouteSetup() {
      exists (string methodName | methodName = getMethodName() |
        (isRouter(getReceiver()) or isRoute(getReceiver()))
        and
        (methodName = "all" or methodName = "use" or
         methodName = any(HTTP::RequestMethodName m).toLowerCase())
      )
    }
  }

  /**
   * A function used as an Express route handler.
   */
  class RouteHandler extends Function {
    RouteHandler() {
      this = any(RouteSetup s).getAnArgument().(DataFlowNode).getALocalSource()
    }
  }

  /**
   * Holds if `nd` is an HTTP request object.
   */
  predicate isRequest(DataFlowNode nd) {
    exists (Variable req |
      req.getADeclaration() = any(RouteHandler h).getParameter(0) and
      nd.getALocalSource() = req.getAnAccess()
    )
  }

  /**
   * Holds if `nd` is an HTTP response object.
   */
  predicate isResponse(DataFlowNode nd) {
    exists (Variable res |
      res.getADeclaration() = any(RouteHandler h).getParameter(1) and
      nd.getALocalSource() = res.getAnAccess()
    )
  }

  /**
   * An access to an HTTP request parameter.
   */
  private class RequestParameterAccess extends RemoteFlowSource {
    RequestParameterAccess() {
      // `req.param("name")`
      exists (MethodCallExpr mce | mce = this |
        isRequest(mce.getReceiver()) and mce.getMethodName() = "param"
      )
      or
      exists (PropAccess pacc |
        isRequest(pacc.getBase()) and pacc = this.(PropAccess).getBase() |
        // `req.params.name`
        pacc.getPropertyName() = "params"
        or
        // `req.query.name`
        pacc.getPropertyName() = "query"
      )
    }

    override string getSourceType() {
      result = "Express request parameter"
    }
  }

  /**
   * An invocation of the `redirect` method of an HTTP response object.
   */
  private class RedirectInvocation extends HTTP::RedirectInvocation, MethodCallExpr {
    RedirectInvocation() {
      isResponse(getReceiver()) and
      getMethodName() = "redirect"
    }

    override Expr getUrlArgument() {
      result = getLastArgument()
    }
  }

  /**
   * An invocation of the `set` or `header` method on an HTTP response object that
   * sets a single header.
   */
  private class SetOneHeader extends HTTP::HeaderDefinition, MethodCallExpr {
    SetOneHeader() {
      isResponse(getReceiver()) and
      getMethodName() = any(string n | n = "set" or n = "header") and
      getNumArgument() = 2
    }

    override predicate defines(string headerName, Expr headerValue) {
      headerName = getArgument(0).getStringValue() and
      headerValue = getArgument(1)
    }
  }

  /**
   * An invocation of the `set` or `header` method on an HTTP response object that
   * sets multiple headers.
   */
  private class SetMultipleHeaders extends HTTP::HeaderDefinition, MethodCallExpr {
    SetMultipleHeaders() {
      isResponse(getReceiver()) and
      getMethodName() = any(string n | n = "set" or n = "header") and
      getNumArgument() = 1
    }

    override predicate defines(string headerName, Expr headerValue) {
      exists (DataFlowNode headers, PropWriteNode pwn |
        headers = getArgument(0).(DataFlowNode).getALocalSource() and
        pwn.getBase() = headers and
        pwn.getPropertyName() = headerName and
        pwn.getRhs() = headerValue
      )
    }
  }

  /**
   * An invocation of the `append` method on an HTTP response object.
   */
  private class AppendHeader extends HTTP::HeaderDefinition, MethodCallExpr {
    AppendHeader() {
      isResponse(getReceiver()) and
      getMethodName() = "append"
    }

    override predicate defines(string headerName, Expr headerValue) {
      headerName = getArgument(0).getStringValue() and
      headerValue = getArgument(1)
    }
  }
}
