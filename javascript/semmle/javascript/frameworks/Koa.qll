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
      exists(RouteHandler rh, Expr ctx | rh.getAContextExpr() = ctx |
        ( // ctx.set('Cache-Control', 'no-cache');
          ctx = getReceiver() and
          name = "set") or
        ( // ctx.response.header('Cache-Control', 'no-cache')
          getReceiver().(PropAccess).accesses(ctx, "response") and
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
      function.getParameter(0).(SimpleParameter).getAnInitialUse() =
      result.(DataFlowNode).getALocalSource()
      or
      // this-access
      result.(ThisExpr).getEnclosingFunction().getThisBinder() = function
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
}
