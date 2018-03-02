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
   * An expression that creates a new Restify server.
   */
  class ServerDefinition extends HTTP::Servers::StandardServerDefinition, CallExpr, DataFlow::TrackedExpr {
    ServerDefinition() {
      exists (ModuleInstance restify | restify.getPath() = "restify" |
        // `server = restify.createServer()`
        this = restify.getAMethodCall("createServer")
      )
    }
  }

  /**
   * A Restify route handler.
   */
  class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      any(RouteSetup setup).getARouteHandler() = this
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
  }

  /**
   * A Restify response source, that is, the response parameter of a
   * route handler.
   */
  private class ResponseSource extends HTTP::Servers::ResponseSource {
    RouteHandler rh;

    ResponseSource() {
      this = DataFlow::parameterNode(rh.getResponseParameter())
    }

    /**
     * Gets the route handler that provides this response.
     */
    RouteHandler getRouteHandler() {
      result = rh
    }
  }

  /**
   * A Restify request source, that is, the request parameter of a
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
   * A Node.js HTTP response provided by Restify.
   */
  class ResponseExpr extends NodeJSLib::ResponseExpr {
    ResponseExpr() { src instanceof ResponseSource }
  }

  /**
   * A Node.js HTTP request provided by Restify.
   */
  class RequestExpr extends NodeJSLib::RequestExpr {
    RequestExpr() { src instanceof RequestSource }
  }

  /**
   * An access to a user-controlled Restify request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {
    RequestExpr request;
    string kind;

    RequestInputAccess() {
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
    }

    override RouteHandler getRouteHandler() {
      result = request.getRouteHandler()
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

    override RouteHandler getRouteHandler(){
      getReceiver() = result.getAResponseExpr()
    }

  }

  /**
   * A call to a Restify method that sets up a route.
   */
  class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {
    ServerDefinition server;

    RouteSetup() {
      // server.get('/', fun)
      // server.head('/', fun)
      server.flowsTo(getReceiver()) and
      getMethodName() = any(HTTP::RequestMethodName m).toLowerCase()
    }

    override DataFlowNode getARouteHandler() {
      result = getArgument(1).(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getServer() {
      result = server
    }
  }
}
