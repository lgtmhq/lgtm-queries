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
      // `app = [new] express()`
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
    any(Application app).flowsTo(e)
  }

  /**
   * Holds if `e` creates an Express router (possibly an application).
   */
  predicate isRouterCreation(InvokeExpr e) {
    isAppCreation(e)
    or
    exists (ModuleInstance express | express.getPath() = "express" |
      // `app = [new] express.Router()`
      e = express.getAMemberInvocation("Router"))
  }

  /**
   * Holds if `e` may refer to the given `router` object.
   */
  private predicate isRouter(Expr e, RouterDefinition router) {
    router.flowsTo(e)
    or
    isRouter(e.(RouteSetup).getReceiver(), router)
  }

  /**
   * An expression that refers to a route.
   */
  class RouteExpr extends MethodCallExpr {
    RouterDefinition router;

    RouteExpr() {
      isRouter(this.getReceiver(), router) and
      this.getMethodName() = "route"
      or
      this.(RouteSetup).getReceiver().(RouteExpr).getRouter() = router
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
        (isRouter(getReceiver(), router) or getReceiver().(RouteExpr).getRouter() = router)
        and
        (methodName = "all" or methodName = "use" or
         methodName = any(HTTP::RequestMethodName m).toLowerCase())
      )
    }

    /** Gets the path associated with the route. */
    string getPath() {
      getArgument(0).mayHaveStringValue(result)
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
      if getArgument(0).analyze().getAType().getTypeofTag() = "function" then
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
      result = getARouteHandlerExpr().(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getServer() {
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

    /**
     * Holds if this registers a route for all request methods.
     */
    predicate handlesAllRequestMethods() {
      getMethodName() = "use" or getMethodName() = "all"
    }

    /**
     * Holds if this route setup sets up a route for the same
     * request method as `that`.
     */
    bindingset[that]
    predicate handlesSameRequestMethodAs(RouteSetup that) {
      this.handlesAllRequestMethods() or
      that.handlesAllRequestMethods() or
      this.getRequestMethod() = that.getRequestMethod()
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
     * Gets a route handler that precedes this one (not necessarily immediately), may handle
     * same request method, and matches on the same path or a prefix.
     *
     * If the preceding handler's path cannot be determined, it is assumed to match.
     *
     * Note that this predicate is not complete: path globs such as `'*'` are not currently
     * handled, and relative paths of subrouters are not modelled. In particular, if an outer
     * router installs a route handler `r1` on a path that matches the path of a route handler
     * `r2` installed on a subrouter, `r1` will not be recognized as an ancestor of `r2`.
     */
    Express::RouteHandlerExpr getAMatchingAncestor() {
      result = getPreviousMiddleware+() and
      exists (RouteSetup resSetup | resSetup = result.getSetup() |
        // check whether request methods are compatible
        resSetup.handlesSameRequestMethodAs(setup)
        and
        // check whether `resSetup` matches on (a prefix of) the same path as `setup`
        (
          // if `result` doesn't specify a path or we cannot determine it, assume
          // that it matches
          not exists (resSetup.getPath())
          or
          setup.getPath() = resSetup.getPath() + any(string s)
        )
      )
      or
      // if this is a sub-router, any previously installed middleware for the same
      // request method will necessarily match
      exists (RouteHandlerExpr outer |
        setup.getRouter() = outer.getAsSubRouter() and
        outer.getSetup().handlesSameRequestMethodAs(setup) and
        result = outer.getAMatchingAncestor()
      )
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
     * Gets the parameter of kind `kind` of this route handler.
     *
     * `kind` is one of: "error", "request", "response", "next".
     */
    private SimpleParameter getRouteHandlerParameter(string kind) {
      exists (int index, int offset |
        result = function.getParameter(index + offset) and
        (if function.getNumParameter() >= 4 then offset = 0 else offset = -1) |
        kind = "error" and index = 0
        or
        kind = "request" and index = 1
        or
        kind = "response" and index = 2
        or
        kind = "next" and index = 3
      )
    }

    /**
     * Gets the parameter of the route handler that contains the request object.
     */
    SimpleParameter getRequestParameter() {
      result = getRouteHandlerParameter("request")
    }

    /**
     * Gets the parameter of the route handler that contains the response object.
     */
    SimpleParameter getResponseParameter() {
      result = getRouteHandlerParameter("response")
    }

    /**
     * Gets a request body access of this handler.
     */
    DataFlowNode getARequestBodyAccess() {
      result.(PropAccess).accesses(getARequestExpr(), "body")
    }
  }

  /**
   * Holds if `call` is a chainable method call on the response object of `handler`.
   */
  private predicate isChainableResponseMethodCall(RouteHandler handler, MethodCallExpr call) {
    exists (string name |
      call.calls(handler.getAResponseExpr(), name) |
      name = "append" or
      name = "attachment" or
      name = "clearCookie" or
      name = "contentType" or
      name = "cookie" or
      name = "format" or
      name = "header" or
      name = "json" or
      name = "jsonp" or
      name = "links" or
      name = "location" or
      name = "send" or
      name = "sendStatus" or
      name = "set" or
      name = "status" or
      name = "type" or
      name = "vary"
    )
  }

  /**
   * An Express response source, that is, the response parameter of a
   * route handler, or a chained method call on a response.
   */
  private class ResponseSource extends HTTP::Servers::ResponseSource {
    RouteHandler rh;

    ResponseSource() {
      this = DataFlow::parameterNode(rh.getResponseParameter())
      or
      isChainableResponseMethodCall(rh, this.asExpr())
    }

    /**
     * Gets the route handler that provides this response.
     */
    RouteHandler getRouteHandler() {
      result = rh
    }
  }

  /**
   * An Express request source, that is, the request parameter of a
   * route handler.
   */
  private class RequestSource extends HTTP::Servers::RequestSource {
    RouteHandler rh;

    RequestSource() {
      this = DataFlow::parameterNode(rh.getRequestParameter())
    }

    /**
     * Gets the route handler that handles this request.
     */
    RouteHandler getRouteHandler() {
      result = rh
    }
  }

  /**
   * An Express response expression.
   */
  class ResponseExpr extends HTTP::Servers::StandardResponseExpr {
    override ResponseSource src;
  }

  /**
   * An Express request expression.
   */
  class RequestExpr extends HTTP::Servers::StandardRequestExpr {
    override RequestSource src;
  }

  /**
   * An access to a user-controlled Express request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {
    RouteHandler rh;
    string kind;

    RequestInputAccess() {
      exists (Expr request | request = rh.getARequestExpr() |
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
        // `req.cookies`
        kind = "cookie" and
        this.asExpr().(PropAccess).accesses(request, "cookies")
      )
    }

    override RouteHandler getRouteHandler() {
      result = rh
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

    override RouteHandler getRouteHandler() {
      getReceiver() = result.getAResponseExpr()
    }
  }

  /**
   * An invocation of the `redirect` method of an HTTP response object.
   */
  private class RedirectInvocation extends HTTP::RedirectInvocation, MethodCallExpr {
    RouteHandler rh;

    RedirectInvocation() {
      getReceiver() = rh.getAResponseExpr() and
      getMethodName() = "redirect"
    }

    override Expr getUrlArgument() {
      result = getLastArgument()
    }

    override RouteHandler getRouteHandler() {
      result = rh
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
    RouteHandler rh;

    SetMultipleHeaders() {
      getReceiver() = rh.getAResponseExpr() and response = getReceiver() and
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

    override RouteHandler getRouteHandler() {
      result = rh
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

    override RouteHandler getRouteHandler() { result = rh }
  }

  /**
   * An invocation of the `cookie` method on an HTTP response object.
   */
  private class SetCookie extends HTTP::CookieDefinition, MethodCallExpr {
    RouteHandler rh;

    SetCookie() {
      calls(rh.getAResponseExpr(), "cookie")
    }

    override Expr getNameArgument() { result = getArgument(0) }
    override Expr getValueArgument() { result = getArgument(1) }
    override RouteHandler getRouteHandler() { result = rh }
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

    override RouteHandler getRouteHandler() { result = rh }
  }

  /**
   * An Express server application.
   */
  private class Application extends HTTP::ServerDefinition, DataFlow::TrackedExpr {

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
  class RouterDefinition extends InvokeExpr, DataFlow::TrackedExpr {

    RouterDefinition() {
      isRouterCreation(this)
    }

    /**
     * Gets a `RouteSetup` that was used for setting up a route on this router.
     */
    private RouteSetup getARouteSetup() {
      this.flowsTo(result.getReceiver())
    }

    /**
     * Gets a sub-router registered on this router.
     *
     * Example: `router2` for `router1.use(router2)` or `router1.use("/route2", router2)`
     */
    RouterDefinition getASubRouter() {
      result.flowsTo(getARouteSetup().getAnArgument())
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
            (this = pwn.getPropertyNameExpr() and kind = "user name") or
            (this = pwn.getRhs() and kind = "password")
          )
        )
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }

  /** A call to `response.sendFile`, considered as a file system access. */
  private class ResponseSendFileAsFileSystemAccess extends FileSystemAccess, DataFlow::ValueNode {
    override MethodCallExpr astNode;

    ResponseSendFileAsFileSystemAccess() {
      asExpr().(MethodCallExpr).calls(any(ResponseExpr res), "sendFile")
    }

    override DataFlow::Node getAPathArgument() {
      result = DataFlow::valueNode(astNode.getArgument(0))
    }
  }
}
