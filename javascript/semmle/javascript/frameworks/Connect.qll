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
 * Provides classes for working with [Connect](https://github.com/senchalabs/connect) applications.
 */
import javascript
import semmle.javascript.frameworks.HTTP

module Connect {
  /**
   * An expression that creates a new Connect server.
   */
  class ServerDefinition extends HTTP::Servers::StandardServerDefinition, CallExpr {
    ServerDefinition() {
      // `app = connect()`
      this = DataFlow::moduleImport("connect").getAnInvocation().asExpr()
    }
  }

  /**
   * A Connect route handler.
   */
  class RouteHandler extends HTTP::Servers::StandardRouteHandler, DataFlow::ValueNode {

    Function function;

    RouteHandler() {
      function = astNode and
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
   * A Connect response source, that is, the response parameter of a
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
   * A Connect request source, that is, the request parameter of a
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
   * A Node.js HTTP response provided by Connect.
   */
  class ResponseExpr extends NodeJSLib::ResponseExpr {
    ResponseExpr() { src instanceof ResponseSource }
  }

  /**
   * A Node.js HTTP request provided by Connect.
   */
  class RequestExpr extends NodeJSLib::RequestExpr {
    RequestExpr() { src instanceof RequestSource }
  }

  /**
   * A call to a Connect method that sets up a route.
   */
  class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {
    ServerDefinition server;

    RouteSetup() {
      // app.use('/', fun)
      // app.use(fun)
      server.flowsTo(getReceiver()) and
      getMethodName() = "use"
    }

    override DataFlow::SourceNode getARouteHandler() {
      result.flowsToExpr(getAnArgument())
    }

    override Expr getServer() {
      result = server
    }
  }

  /** An expression that is passed as `basicAuthConnect(<user>, <password>)`. */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (CallExpr call |
        call = DataFlow::moduleImport("basic-auth-connect").getAnInvocation().asExpr() and
        call.getNumArgument() = 2 |
        this = call.getArgument(0) and kind = "user name" or
        this = call.getArgument(1) and kind = "password"
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }

  /**
   * An access to a user-controlled Connect request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {
    RequestExpr request;
    string kind;

    RequestInputAccess() {
      exists (PropAccess cookies |
        // `req.cookies.get(<name>)`
        kind = "cookie" and
        cookies.accesses(request, "cookies") and
        this.asExpr().(MethodCallExpr).calls(cookies, "get")
      )
    }

    override RouteHandler getRouteHandler() {
      result = request.getRouteHandler()
    }

    override string getKind() {
      result = kind
    }
  }

}
