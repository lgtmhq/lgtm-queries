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
 * Provides classes for working with [Hapi](https://hapijs.com/) servers.
 */
import javascript
import semmle.javascript.frameworks.HTTP

module Hapi {
  /**
   * A Hapi server.
   */
  private class Server extends HTTP::Servers::StandardServer, NewExpr {
    Server() {
      exists (ModuleInstance hapi | hapi.getPath() = "hapi" |
        // `server = new Hapi.Server()`
        this.getCallee() = hapi.getAPropertyRead("Server")
      )
    }
  }

  /**
   * A Hapi route handler.
   */
  private class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      exists(RouteSetup setup | this = setup.getARouteHandler())
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
   * An HTTP header defined in a Hapi server.
   */
  private class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {

    HeaderDefinition() {
      exists(Expr req |
        any(RouteHandler rh).getARequestExpr() = req and
        // request.response.header('Cache-Control', 'no-cache')
        getReceiver().(PropAccess).accesses(req, "response") and
        getMethodName() = "header"
      )
    }

    override RouteHandler getARouteHandler(){
      exists(Expr base |
        this.getReceiver().(PropAccess).getBase() = base and
        result.getARequestExpr() = base
      )
    }

  }

  /**
   * A call to a Hapi method that sets up a route.
   */
  private class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {

    Expr server;

    string methodName;

    RouteSetup() {
      server = getReceiver() and
      server.(DataFlowNode).getALocalSource() instanceof Server and
      (methodName = "route" or methodName = "ext")
    }

    override DataFlowNode getARouteHandler() {
      // server.route({ handler: fun })
      (methodName = "route" and result = any(DataFlowNode n | hasOptionArgument(0, "handler", n)).getALocalSource()) or
        // server.ext('/', fun)
        (methodName = "ext" and result = getArgument(1).(DataFlowNode).getALocalSource())
      }

      override DataFlowNode getAServer(){
      result = server.(DataFlowNode).getALocalSource()
    }
  }
}
