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
  predicate isApp(Expr e) {
    exists (DataFlow::TrackedNode appCreation, DataFlow::Node app |
      isAppCreation(appCreation.asExpr()) and
      appCreation.flowsTo(app) and
      e = app.asExpr()
    )
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
   * Track Express router creations inter-procedurally.
   */
  private class TrackRouterCreations extends DataFlow::TrackedNode {
    TrackRouterCreations() {
      isRouterCreation(asExpr())
    }
  }

  /**
   * Holds if `e` may refer to the given `router` object.
   */
  private predicate isRouter(Expr e, RouterDefinition router) {
    exists (DataFlow::TrackedNode routerCreation |
      routerCreation.asExpr() = router and
      routerCreation.flowsTo(DataFlow::valueNode(e))
    )
    or
    isRouter(e.(RouteSetup).getReceiver(), router)
  }

  /**
   * A call to an Express method that returns a route.
   */
  private class Route extends MethodCallExpr {
    RouterDefinition router;

    Route() {
      isRouter(this.getReceiver(), router) and
      this.getMethodName() = "route"
      or
      this.(RouteSetup).getReceiver().(Route).getRouter() = router
    }

    /** Gets the router from which this route was created. */
    RouterDefinition getRouter() {
      result = router
    }
  }

  /**
   * A call to an Express method that sets up a route.
   */
  class RouteSetup extends HTTP::Servers::StandardRouteSetup, MethodCallExpr {

    RouterDefinition router;

    RouteSetup() {
      exists (string methodName | methodName = getMethodName() |
        (isRouter(getReceiver(), router) or getReceiver().(Route).getRouter() = router)
        and
        (methodName = "all" or methodName = "use" or
         methodName = any(HTTP::RequestMethodName m).toLowerCase())
      )
    }

    /** Gets the router on which handlers are being registered. */
    RouterDefinition getRouter() {
      result = router
    }

    /** Holds if this is a call `use`, such as `app.use(handler)`. */
    predicate isUseCall() {
      getMethodName() = "use"
    }

    /**
     * Gets the `n`th handler registered by this setup, with 0 being the first.
     *
     * This differs from `getARouteHandler` in that the argument expression is
     * returned, not its dataflow source.
     */
    Expr getRouteHandlerExpr(int index) {
      // The first argument is a URI pattern if it is a string. If it could possibly be
      // a function, we consider it to be a route handler, otherwise a URI pattern.
      if DataFlow::valueNode(getArgument(0)).(AnalyzedFlowNode).getAType().getTypeofTag() = "function" then
        result = getArgument(index)
      else
        (index >= 0 and result = getArgument(index + 1))
    }

    /** Gets an argument that represents a route handler being registered. */
    Expr getARouteHandlerExpr() {
      result = getRouteHandlerExpr(_)
    }

    /** Gets the last argument representing a route handler being registered. */
    Expr getLastRouteHandlerExpr() {
      result = max(int i || getRouteHandlerExpr(i) order by i)
    }

    override DataFlowNode getARouteHandler() {
      result = getAnArgument().(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getAServer() {
      result.(Application).getARouteHandler() = getARouteHandler()
    }

    /**
     * Gets the HTTP request type this is registered for, if any.
     *
     * Has no result for `use` and `all` calls.
     */
    HTTP::RequestMethodName getRequestMethod() {
      result.toLowerCase() = getMethodName()
    }
  }

  /**
   * An expression used as an Express route handler, such as `submitHandler` below:
   * ```
   * app.post('/submit', submitHandler)
   * ```
   *
   * Unlike `RouterHandler`, this is the argument passed to a setup, as opposed to
   * a function that flows into such an argument.
   */
  class RouteHandlerExpr extends DataFlowNode {
    RouteSetup setup;
    int index;

    RouteHandlerExpr() {
      this = setup.getRouteHandlerExpr(index)
    }

    /**
     * Gets the setup call that registers this route handler.
     */
    RouteSetup getSetup() {
      result = setup
    }

    /**
     * Gets the function body of this handler, if it is defined locally.
     */
    RouteHandler getBody() {
      result = getALocalSource()
    }

    /**
     * Holds if this is not followed by more handlers.
     */
    predicate isLastHandler() {
      not setup.isUseCall() and
      not exists(setup.getRouteHandlerExpr(index + 1))
    }

    /**
     * Gets a route handler that immediately precedes this in the route stack.
     *
     * For example:
     * ```
     * app.use(auth);
     * app.get('/foo', parseForm, foo);
     * app.get('/bar', bar);
     * ```
     * The previous from `foo` is `parseForm`, and the previous from `parseForm` is `auth`.
     * The previous from `bar` is `auth`.
     *
     * This does not take URI patterns into account. Route handlers should be seen as a no-ops when the
     * requested URI does not match its pattern, but it will be part of the route stack regardless.
     * For example:
     * ```
     * app.use('/admin', auth);
     * app.get('/foo, 'foo);
     * ```
     * In this case, the previous from `foo` is `auth` although they do not act on the
     * same requests.
     */
    Express::RouteHandlerExpr getPreviousMiddleware() {
      index = 0 and result = setup.getRouter().getMiddlewareStackAt(setup.getAPredecessor())
      or
      index > 0 and result = setup.getRouteHandlerExpr(index - 1)
      or
      // Outside the router's original container, use the flow-insensitive model of its middleware stack.
      // Its state is not tracked to CFG nodes outside its original container.
      index = 0 and
      exists (RouterDefinition router | router = setup.getRouter() |
        router.getContainer() != setup.getContainer() and
        result = router.getMiddlewareStack())
    }

    /**
     * Gets a route handler that may follow immediately after this one in its route stack.
     */
    Express::RouteHandlerExpr getNextMiddleware() {
      result.getPreviousMiddleware() = this
    }

    /**
     * Gets the router being registered as a sub-router here, if any.
     */
    RouterDefinition getAsSubRouter() {
      isRouter(this, result)
    }
  }

  /**
   * A function used as an Express route handler.
   */
  class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      any(RouteSetup s).getARouteHandler() = this
    }

    /**
     * Gets the parameter of the route handler that contains the request object.
     */
    SimpleParameter getRequestParameter() {
      result = function.getParameter(0)
    }

    /**
     * Gets the parameter of the route handler that contains the response object.
     */
    SimpleParameter getResponseParameter() {
      result = function.getParameter(1)
    }

    /**
     * Gets the data flow node corresponding to the request parameter.
     */
    private DataFlow::TrackedNode getRequestNode() {
      result = DataFlow::parameterNode(getRequestParameter())
    }

    /**
     * Gets the data flow node corresponding to the response parameter.
     */
    private DataFlow::TrackedNode getResponseNode() {
      result = DataFlow::parameterNode(getResponseParameter())
    }

    /**
     * Gets an expression that contains the "request" object of
     * a route handler invocation.
     */
    Expr getARequestExpr(){
      exists (DataFlow::Node sink |
        getRequestNode().flowsTo(sink) and
        result = sink.asExpr()
      )
    }

    /**
     * Gets an expression that contains the "response" object of
     * a route handler invocation.
     */
    Expr getAResponseExpr(){
      exists (DataFlow::Node sink |
        getResponseNode().flowsTo(sink) and
        result = sink.asExpr()
      )
    }

    /**
     * Gets a request body access of this handler.
     */
    DataFlowNode getARequestBodyAccess() {
      result.(PropAccess).accesses(getARequestExpr(), "body")
    }
  }

  /**
   * Track Express requests and responses inter-procedurally.
   */
  private class TrackRequestResponseParams extends DataFlow::TrackedNode {
    TrackRequestResponseParams() {
      exists (RouteHandler rh, SimpleParameter p |
        p = rh.getRequestParameter() or
        p = rh.getResponseParameter() |
        this = DataFlow::parameterNode(p)
      )
    }
  }


  /**
   * An access to a user-controlled Express request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {

    string kind;

    RequestInputAccess() {
      exists (RouteHandler rh, Expr request |
        request = rh.getARequestExpr() |
        kind = "parameter" and
        (
          this.asExpr().(MethodCallExpr).calls(request, "param") or
          exists (PropAccess base, string propName |
            // `req.params.name` or `req.query.name`
            base.accesses(request, propName) and
            this.asExpr().(PropAccess).accesses(base, _) |
            propName = "params" or
            propName = "query"
          )
        ) or
        kind = "body" and
        this.asExpr() = rh.getARequestBodyAccess()
        or
        exists (string propName |
          // `req.url` or `req.originalUrl`
          kind = "url" and
          this.asExpr().(PropAccess).accesses(request, propName) |
          propName = "url" or
          propName = "originalUrl"
        )
        or
        exists (string methodName |
          // `req.get(...)` or `req.header(...)`
          kind = "header" and
          this.asExpr().(MethodCallExpr).calls(request, methodName) |
          methodName = "get" or
          methodName = "header"
        )
        or
        // `req.cookies
        kind = "cookie" and
        this.asExpr().(PropAccess).accesses(request, "cookies")
      )
    }

    override string getKind() {
      result = kind
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
    any(RouteHandler rh).getARequestExpr() = nd
  }

  /**
   * Holds if `nd` is an HTTP response object.
   */
  predicate isResponse(DataFlowNode nd) {
    any(RouteHandler rh).getAResponseExpr() = nd
  }

  /**
   * An access to the HTTP request body.
   */
  class RequestBodyAccess extends Expr {

    RequestBodyAccess() {
      any(RouteHandler h).getARequestBodyAccess() = this
    }

  }

  private abstract class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {
    HeaderDefinition() {
      isResponse(getReceiver())
    }

    override RouteHandler getARouteHandler() {
      getReceiver() = result.getAResponseExpr()
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
  private class SetOneHeader extends HeaderDefinition {
    SetOneHeader() {
      getMethodName() = any(string n | n = "set" or n = "header") and
      getNumArgument() = 2
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
  private class AppendHeader extends HeaderDefinition {
    AppendHeader() {
      getMethodName() = "append"
    }
  }

  /**
   * An argument passed to the `send` method of an HTTP response object.
   */
  private class ResponseSendArgument extends HTTP::ResponseSendArgument {
    RouteHandler rh;

    ResponseSendArgument() {
      exists (MethodCallExpr mce |
        mce.calls(rh.getAResponseExpr(), "send") and
        this = mce.getArgument(0)
      )
    }

    override RouteHandler getHandler() { result = rh }
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

  /**
   * An expression passed to the `render` method of an HTTP response object
   * as the value of a template variable.
   */
  private class TemplateInput extends HTTP::ResponseBody {
    RouteHandler rh;

    TemplateInput() {
      exists (MethodCallExpr mce, DataFlowNode locals, PropWriteNode pw |
        mce.calls(rh.getAResponseExpr(), "render") and
        mce.getArgument(1).(DataFlowNode).getALocalSource() = locals and
        pw.getBase().getALocalSource() = locals and
        pw.getRhs() = this
      )
    }

    override RouteHandler getHandler() { result = rh }
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
      result = this.(RouterDefinition).getASubRouter*().getARouteHandler()
    }

  }

  /**
   * An Express router.
   */
  class RouterDefinition extends InvokeExpr {

    RouterDefinition() {
      isRouterCreation(this)
    }

    /**
     * Gets a `RouteSetup` that was used for setting up a route on this router.
     */
    private RouteSetup getARouteSetup() {
      exists (DataFlow::TrackedNode src |
        src.asExpr() = this and
        src.flowsTo(DataFlow::valueNode(result.getReceiver()))
      )
    }

    /**
     * Gets a sub-router registered on this router.
     *
     * Example: `router2` for `router1.use(router2)` or `router1.use("/route2", router2)`
     */
    RouterDefinition getASubRouter() {
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

    /**
     * Gets the last middleware in the given router at `node`.
     *
     * For example:
     * ```
     * app = express()
     * app.use(auth)
     * app.use(throttle)
     * ```
     * After line one, the router has no middleware.
     * After line two, the router has `auth` on top of its middleware stack,
     * and after line three, the router has `throttle` on top of its middleware stack.
     *
     * If `node` is not in the same container where `router` was defined, the predicate has no result.
     */
    Express::RouteHandlerExpr getMiddlewareStackAt(ControlFlowNode node) {
      if exists (Express::RouteSetup setup | node = setup and setup.getRouter() = this | setup.isUseCall()) then
        result = node.(Express::RouteSetup).getLastRouteHandlerExpr()
      else
        result = getMiddlewareStackAt(node.getAPredecessor())
    }

    /**
     * Gets the final middleware registered on this router.
     */
    Express::RouteHandlerExpr getMiddlewareStack() {
      result = getMiddlewareStackAt(getContainer().getExit())
    }
  }

  /** An expression that is passed as `expressBasicAuth({ users: { <user>: <password> }})`. */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (CallExpr call |
        exists (ModuleInstance mod |
          mod.getPath() = "express-basic-auth" |
          call.getCallee().(DataFlowNode).getALocalSource() = mod
        ) and
        exists (DataFlowNode users, PropWriteNode pwn |
          call.hasOptionArgument(0, "users", users) |
          pwn.getBase().getALocalSource() = users.getALocalSource() and
          (
            (this = pwn and kind = "user name") or
            (this = pwn.getRhs() and kind = "password")
          )
        )
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }

}
