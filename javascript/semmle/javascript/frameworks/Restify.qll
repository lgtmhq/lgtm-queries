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
 * Provides classes for working with [Restify](https://restify.com/) servers.
 */
import javascript
import semmle.javascript.frameworks.HTTP

module Restify {
  /**
   * A Restify server.
   */
  private class Server extends HTTP::Servers::StandardServer, CallExpr {
    Server() {
      exists (ModuleInstance restify | restify.getPath() = "restify" |
        // `server = restify.createServer()`
        this = restify.getAMethodCall("createServer")
      )
    }
  }

  /**
   * A NodeJS HTTP response provided by Restify.
   */
  private class ResponseExpr extends NodeJSLib::ResponseExpr {

    RouteHandler rh;

    ResponseExpr() {
      this = rh.getAResponseExpr()
    }

    override RouteHandler getARouteHandler() {
      result = rh
    }

  }

  /**
   * A NodeJS HTTP response provided by Restify.
   */
  private class RequestExpr extends NodeJSLib::RequestExpr {

    RouteHandler rh;

    RequestExpr() {
      this = rh.getARequestExpr()
    }

    override RouteHandler getARouteHandler() {
      result = rh
    }

  }


  /**
   * A Restify route handler.
   */
  private class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      any(RouteSetup setup).getARouteHandler() = this
    }

    /**
     * Gets an expression that contains the "response" object of
     * a route handler invocation.
     */
    Expr getAResponseExpr() {
      result.mayReferToParameter(function.getParameter(1))
    }

    /**
     * Gets an expression that contains the "request" object of
     * a route handler invocation.
     */
    Expr getARequestExpr() {
      result.mayReferToParameter(function.getParameter(0))
    }

  }

  /**
   * An access to a user-controlled Restify request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {

    string kind;

    RequestInputAccess() {
      exists (RequestExpr request |
        exists (MethodCallExpr query |
          // `request.getQuery().<name>`
          kind = "parameter" and
          query.calls(request, "getQuery") and
          this.asExpr().(PropAccess).accesses(query, _)
        )
        or
        exists (string methodName |
          // `request.href()` or `request.getPath()`
          kind = "url" and
          this.asExpr().(MethodCallExpr).calls(request, methodName) |
          methodName = "href" or
          methodName = "getPath"
        )
        or
        exists (string methodName |
          // `request.getContentType()`, `request.userAgent()`, `request.trailer(...)`, `request.header(...)`
          kind = "header" and
          this.asExpr().(MethodCallExpr).calls(request, methodName) |
          methodName = "getContentType" or
          methodName = "userAgent" or
          methodName = "trailer" or
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
   * An HTTP header defined in a Restify server.
   */
  private class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {

    HeaderDefinition() {
      // response.header('Cache-Control', 'no-cache')
      getReceiver() instanceof ResponseExpr and
      getMethodName() = "header"
    }

    override RouteHandler getARouteHandler(){
      getReceiver() = result.getAResponseExpr()
    }

  }

  /**
   * A call to a Restify method that sets up a route.
   */
  private class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {

    Expr server;

    RouteSetup() {
      // server.get('/', fun)
      // server.head('/', fun)
      server = getReceiver() and
      server.(DataFlowNode).getALocalSource() instanceof Server and
      getMethodName() = any(HTTP::RequestMethodName m).toLowerCase()
    }

    override DataFlowNode getARouteHandler() {
      result = getArgument(1).(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getAServer() {
      result = server.(DataFlowNode).getALocalSource()
    }
  }
}
