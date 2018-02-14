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
 * Provides classes for working with [Koa](https://koajs.com) applications.
 */
import javascript
import semmle.javascript.frameworks.HTTP

module Koa {
  /**
   * A Koa server application.
   */
  private class KoaApp extends HTTP::Servers::StandardServer, NewExpr {
    KoaApp() {
      exists (ModuleInstance koa | koa.getPath() = "koa" |
        // `app = new Koa()`
        this.getCallee().(DataFlowNode).getALocalSource() = koa
      )
    }
  }

  /**
   * An HTTP header defined in a Koa application.
   */
  private class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {

    string name;

    HeaderDefinition() {
      name = getMethodName() and
      exists(RouteHandler rh |
        ( // ctx.set('Cache-Control', 'no-cache');
          getReceiver() = rh.getAContextExpr() and
          name = "set") or
        ( // ctx.response.header('Cache-Control', 'no-cache')
          getReceiver() = rh.getAResponseExpr() and
          name = "header")
      )
    }

    override RouteHandler getARouteHandler(){
      exists(Expr ctx |
        result.getAContextExpr() = ctx and
        (name = "set" and getReceiver() = ctx) or
        (name = "header" and getReceiver().(PropAccess).getBase() = ctx)
      )
    }

  }

  /**
   * A Koa route handler.
   */
  private class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      any(KoaRouteSetup setup).getARouteHandler() = this
    }

    /**
     * Gets an expression that contains the "context" object of
     * a route handler invocation.
     *
     * Explanation: the context-object in Koa is typically
     * `this` or `ctx`, given as the first and only argument to the
     * route handler.
     */
    Expr getAContextExpr() {
      // param-access
      result.mayReferToParameter(function.getParameter(0))
      or
      // this-access
      result.(ThisExpr).getEnclosingFunction().getThisBinder() = function
    }

    /**
     * Gets an expression that contains the "request" object of
     * a route handler invocation.
     */
    DataFlowNode getARequestExpr() {
      result.getALocalSource().(PropAccess).accesses(getAContextExpr(), "request")
    }

    /**
     * Gets an expression that contains the "response" object of
     * a route handler invocation.
     */
    DataFlowNode getAResponseExpr() {
      result.getALocalSource().(PropAccess).accesses(getAContextExpr(), "response")
    }

  }

  /**
   * An access to a user-controlled Koa request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {

    string kind;

    RequestInputAccess() {
      exists (DataFlowNode request |
        request = any(RouteHandler rh).getARequestExpr() |
        // `ctx.request.body`
        kind = "body" and
        this.asExpr().(PropAccess).accesses(request, "body")
        or
        exists (PropAccess query |
          kind = "parameter" and
          // `ctx.request.query.name`
          query.accesses(request, "query")  and
          this.asExpr().(PropAccess).accesses(query, _)
        )
        or
        exists (string propName |
          // `ctx.request.url`, `ctx.request.originalUrl`, or `ctx.request.href`
          kind = "url" and
          this.asExpr().(PropAccess).accesses(request, propName) |
          propName = "url" or
          propName = "originalUrl" or
          propName = "href"
        )
        or
        exists (string propName, PropAccess headers |
          // `ctx.request.header.<name>`, `ctx.request.headers.<name>`
          kind = "header" and
          headers.accesses(request, propName) and
          this.asExpr().(PropAccess).accesses(headers, _) |
          propName = "header" or
          propName = "headers"
        )
        or
        // `ctx.request.get(<name>)`
        kind = "header" and
        this.asExpr().(MethodCallExpr).calls(request, "get")
      ) or
      exists (PropAccess cookies |
        // `ctx.cookies.get(<name>)`
        kind = "cookie" and
        cookies.accesses(any(RouteHandler rh).getAContextExpr(), "cookies") and
        this.asExpr().(MethodCallExpr).calls(cookies, "get")
      )
    }

    override string getKind() {
      result = kind
    }

  }

  /**
   * A call to a Koa method that sets up a route.
   */
  private class KoaRouteSetup extends HTTP::Servers::StandardRouteSetup, MethodCallExpr {

    Expr server;

    KoaRouteSetup() {
      // app.use(fun)
      server = getReceiver() and
      server.(DataFlowNode).getALocalSource() instanceof KoaApp and
      getMethodName() = "use"
    }

    override DataFlowNode getARouteHandler() {
      result = getArgument(0).(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getAServer() {
      result = server.(DataFlowNode).getALocalSource()
    }
  }

  /**
   * A value assigned to the body of an HTTP response object.
   */
  private class ResponseSendArgument extends HTTP::ResponseSendArgument {
    RouteHandler rh;

    ResponseSendArgument() {
      exists (PropWriteNode pwn |
        pwn.(PropAccess).accesses(rh.getAResponseExpr(), "body") and
        this = pwn.getRhs()
      )
    }

    override RouteHandler getHandler() { result = rh }
  }

}
