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
import semmle.javascript.frameworks.ExpressModules

module Express {
  /**
   * Holds if `e` creates an Express application.
   */
  predicate isAppCreation(InvokeExpr e) {
    exists (ModuleInstance express | express.getPath() = "express" |
      // `app = express()`
      e.getCallee().(DataFlowNode).getALocalSource() = express
      or
      // `app = express.createServer()`
      e = express.getAMethodCall("createServer")
    )
  }

  /**
   * Holds if `e` is an Express application object
   */
  predicate isApp(DataFlowNode e) {
    isAppCreation(e.getALocalSource())
  }

  /**
   * Holds if `e` creates an Express router (possibly an application).
   */
  predicate isRouterCreation(InvokeExpr e) {
    isAppCreation(e)
    or
    exists (ModuleInstance express | express.getPath() = "express" |
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

    /**
     * Gets the variable that contains the request object.
     */
    Variable getRequestVariable() {
      result = getParameter(0).(SimpleParameter).getVariable()
    }

    /**
     * Gets the variable that contains the response object.
     */
    Variable getResponseVariable() {
      result = getParameter(1).(SimpleParameter).getVariable()
    }
  }

  /**
   * An Express route handler, viewed as an HTTP route handler.
   */
  private class ServerRouteHandler extends HTTP::RouteHandler {

    RouteHandler handler;

    ServerRouteHandler() {
      handler = this
    }

    override HTTP::HeaderDefinition getAResponseHeader(string name) {
      exists(ExplicitHeader h |
        h.getResponse().(DataFlowNode).getALocalSource() = handler.getResponseVariable().getAnAccess() and
        h.getAHeaderName() = name and
        result = h
      )
    }
  }

  /**
   * HTTP headers created by Express calls
   */
  private abstract class ExplicitHeader extends HTTP::ExplicitHeaderDefinition {

    DataFlowNode response;

    /**
     * Gets the response object that this header is set on.
     */
    DataFlowNode getResponse() {
      result = response
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
      res = any(RouteHandler h).getResponseVariable() and
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
   * An access to the HTTP request body.
   */
  class RequestBodyAccess extends RemoteFlowSource {
    RequestBodyAccess() {
      exists (Expr req |
        isRequest(req) and
        this.(PropAccess).accesses(req, "body")
      )
    }

    override string getSourceType() {
      result = "Express request body"
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
  private class SetOneHeader extends ExplicitHeader, MethodCallExpr {
    SetOneHeader() {
      isResponse(getReceiver()) and response = getReceiver() and
      getMethodName() = any(string n | n = "set" or n = "header") and
      getNumArgument() = 2
    }

    override predicate definesExplicitly(string headerName, Expr headerValue) {
      headerName = getArgument(0).getStringValue() and
      headerValue = getArgument(1)
    }

  }

  /**
   * An invocation of the `set` or `header` method on an HTTP response object that
   * sets multiple headers.
   */
  private class SetMultipleHeaders extends ExplicitHeader, MethodCallExpr {
    SetMultipleHeaders() {
      isResponse(getReceiver()) and response = getReceiver() and
      getMethodName() = any(string n | n = "set" or n = "header") and
      getNumArgument() = 1
    }

    override predicate definesExplicitly(string headerName, Expr headerValue) {
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
  private class AppendHeader extends ExplicitHeader, MethodCallExpr {
    AppendHeader() {
      isResponse(getReceiver()) and response = getReceiver() and
      getMethodName() = "append"
    }

    override predicate definesExplicitly(string headerName, Expr headerValue) {
      headerName = getArgument(0).getStringValue() and
      headerValue = getArgument(1)
    }
  }

  /**
   * An argument passed to the `send` method of an HTTP response object.
   */
  private class ResponseBody extends HTTP::ResponseBody {
    ResponseBody() {
      exists (MethodCallExpr mce |
        isResponse(mce.getReceiver()) and
        mce.getMethodName() = "send" and
        this = mce.getArgument(0)
      )
    }
  }

  /**
   * An invocation of the `cookie` method on an HTTP response object.
   */
  private class SetCookie extends HTTP::CookieDefinition, MethodCallExpr {
    SetCookie() {
      isResponse(getReceiver()) and
      getMethodName() = "cookie"
    }

    override Expr getNameArgument() { result = getArgument(0) }
    override Expr getValueArgument() { result = getArgument(1) }
  }

  /*
   * An expression passed to the `render` method of an HTTP response object
   * as the value of a template variable.
   */
  private class TemplateInput extends HTTP::ResponseBody {
    TemplateInput() {
      exists (MethodCallExpr mce, DataFlowNode locals, PropWriteNode pw |
        isResponse(mce.getReceiver()) and
        mce.getMethodName() = "render" and
        mce.getArgument(1).(DataFlowNode).getALocalSource() = locals and
        pw.getBase().getALocalSource() = locals and
        pw.getRhs() = this
      )
    }
  }

  /**
   * An Express server application.
   */
  private class Application extends HTTP::Server {

    Application() {
      isAppCreation(this)
    }

    /**
     * Gets a route handler of the application, regardless of nesting.
     */
    HTTP::RouteHandler getARouteHandler() {
      result = this.(Router).getASubRouter*().getARouteHandler()
    }

  }

  /**
   * An Express router.
   */
  private class Router extends InvokeExpr {

    Router() {
      isRouterCreation(this)
    }

    /**
     * Gets a `RouteSetup` that was used for setting up a route on this router.
     */
    private RouteSetup getARouteSetup() {
      this = result.getReceiver().(DataFlowNode).getALocalSource()
    }

    /**
     * Gets a sub-router registered on this router.
     *
     * Example: `router2` for `router1.use(router2)` or `router1.use("/route2", router2)`
     */
    Router getASubRouter() {
      result = getARouteSetup().getAnArgument().(DataFlowNode).getALocalSource()
    }

    /**
     * Gets a route handler registered on this router.
     *
     * Example: `fun` for `router1.use(fun)` or `router.use("/route", fun)`
     */
    HTTP::RouteHandler getARouteHandler() {
      result = getARouteSetup().getAnArgument().(DataFlowNode).getALocalSource()
    }
  }

}
