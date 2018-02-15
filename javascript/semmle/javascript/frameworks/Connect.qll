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
   * A Connect server.
   */
  private class Server extends HTTP::Servers::StandardServer, CallExpr {
    Server() {
      exists (ModuleInstance connect | connect.getPath() = "connect" |
        // `app = connect()`
        getCallee().(DataFlowNode).getALocalSource() = connect
      )
    }
  }

  /**
   * A Connect route handler.
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
   * A NodeJS HTTP response provided by Connect.
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
   * A NodeJS HTTP response provided by Connect.
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
   * A call to a Connect method that sets up a route.
   */
  private class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {

    DataFlowNode server;

    RouteSetup() {
      // app.use('/', fun)
      // app.use(fun)
      server = getReceiver() and
      server.getALocalSource() instanceof Server and
      getMethodName() = "use"
    }

    override DataFlowNode getARouteHandler() {
      result = getAnArgument().(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getAServer() {
      result = server.getALocalSource()
    }
  }

  /** An expression that is passed as `basicAuthConnect(<user>, <password>)`. */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (CallExpr call |
        exists (ModuleInstance mod |
          mod.getPath() = "basic-auth-connect" |
          call.getCallee().(DataFlowNode).getALocalSource() = mod
        ) and
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
    string kind;

    RequestInputAccess() {
      exists (RequestExpr request |
        exists (PropAccess cookies |
          // `req.cookies.get(<name>)`
          kind = "cookie" and
          cookies.accesses(request, "cookies") and
          this.asExpr().(MethodCallExpr).calls(cookies, "get")
        )
      )
    }

    override string getKind() {
      result = kind
    }

  }

}
