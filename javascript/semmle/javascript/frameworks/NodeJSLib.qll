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
 * Provides classes for modelling the Node.js standard library.
 */

import javascript
import semmle.javascript.frameworks.HTTP
import semmle.javascript.security.SensitiveActions

module NodeJSLib {
  /**
   * Holds if `call` is an invocation of `http.createServer` or `https.createServer`.
   */
  predicate isCreateServer(CallExpr call) {
    exists (ModuleInstance http |
      http.getPath() = "http" or http.getPath() = "https" |
      call = http.getAMethodCall("createServer")
    )
  }

  /**
   * A NodeJS HTTP response.
   *
   * A server library that provides an (enhanced) NodesJS HTTP response
   * object should implement a library specific subclass of this class.
   */
  abstract class ResponseExpr extends Expr {

    /**
     * Gets a route handler that provides this response.
     */
    abstract HTTP::RouteHandler getARouteHandler();

  }

  /**
   * A NodeJS HTTP request.
   *
   * A server library that provides an (enhanced) NodesJS HTTP request
   * object should implement a library specific subclass of this class.
   */
  abstract class RequestExpr extends Expr {

    /**
     * Gets a route handler that provides this request.
     */
    abstract HTTP::RouteHandler getARouteHandler();

  }

  /**
   * A builtin NodeJS HTTP response.
   */
  private class BuiltinRouteHandlerResponseExpr extends ResponseExpr {

    RouteHandler rh;

    BuiltinRouteHandlerResponseExpr() {
      this = rh.getAResponseExpr()
    }

    override RouteHandler getARouteHandler() {
      result = rh
    }

  }

  /**
   * A builtin NodeJS HTTP request.
   */
  private class BuiltinRouteHandlerRequestExpr extends RequestExpr {

    RouteHandler rh;

    BuiltinRouteHandlerRequestExpr() {
      this = rh.getARequestExpr()
    }


    override RouteHandler getARouteHandler() {
      result = rh
    }

  }

  class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      any(RouteSetup setup).getARouteHandler() = this
    }

    private Expr getALocalParameterUse(int paramIndex){
      exists(SimpleParameter param |
        param = function.getParameter(paramIndex) and
        result.mayReferToParameter(param)
      )
    }

    /**
     * Gets an expression that contains the "request" object of
     * a route handler invocation.
     */
    Expr getARequestExpr(){
      result = getALocalParameterUse(0)
    }

    /**
     * Gets an expression that contains the "response" object of
     * a route handler invocation.
     */
    Expr getAResponseExpr(){
      result = getALocalParameterUse(1)
    }
  }


  /**
   * An access to a user-controlled NodeJS request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {

    string kind;

    RequestInputAccess() {
      exists (RequestExpr request |
        // `req.url`
        kind = "url" and
        this.asExpr().(PropAccess).accesses(request, "url")
        or
        exists (PropAccess headers, string name |
          // `req.headers.<name>`
          if name = "cookie" then kind = "cookie" else kind= "header" |
          headers.accesses(request, "headers") and
          this.asExpr().(PropAccess).accesses(headers, name)
        )
      )
    }

    override string getKind() {
      result = kind
    }

  }

  /**
   * Holds if `nd` is an HTTP request object.
   *
   * DEPRECATED: use `instanceof RequestExpr` instead.
   */
  deprecated predicate isRequest(DataFlowNode nd) {
    nd instanceof RequestExpr
  }

  /**
   * Holds if `nd` is an HTTP response object.
   *
   * DEPRECATED: use `instanceof ResponseExpr` instead.
   */
  deprecated predicate isResponse(DataFlowNode nd) {
    nd instanceof ResponseExpr
  }

  class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {

    Expr server;

    Expr handler;

    RouteSetup() {
      (server = this and
        isCreateServer(server) and
        handler = getArgument(0)) or
        (server = getReceiver() and
          server.(DataFlowNode).getALocalSource() instanceof Server and
          getMethodName().regexpMatch("on(ce)?") and
          getArgument(0).getStringValue() = "request" and
          handler = getArgument(1)
        )
    }

    override DataFlowNode getARouteHandler() {
      result = handler.(DataFlowNode).getALocalSource()
    }

    override DataFlowNode getAServer() {
      result = server.(DataFlowNode).getALocalSource()
    }

  }

  private abstract class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {

    ResponseExpr r;

    HeaderDefinition(){
      getReceiver() = r
    }

    override HTTP::RouteHandler getARouteHandler(){
      result = r.getARouteHandler()
    }

  }

  /**
   * A call to the `setHeader` method of an HTTP response.
   */
  private class SetHeader extends HeaderDefinition {
    SetHeader() {
      getMethodName() = "setHeader"
    }
  }

  /**
   * A call to the `writeHead` method of an HTTP response.
   */
  private class WriteHead extends HeaderDefinition {
    WriteHead() {
      getMethodName() = "writeHead" and
      getNumArgument() > 1
    }

    override predicate definesExplicitly(string headerName, Expr headerValue) {
      exists (DataFlowNode headers, PropWriteNode pwn |
        headers = getLastArgument().(DataFlowNode).getALocalSource() and
        pwn.getBase() = headers and
        pwn.getPropertyName() = headerName and
        pwn.getRhs() = headerValue
      )
    }
  }

  /**
   * A call to `url.parse` or `querystring.parse`.
   */
  private class UrlParsingFlowTarget extends TaintTracking::FlowTarget, DataFlow::ValueNode {
    UrlParsingFlowTarget() {
      astNode.(MethodCallExpr).calls(_, "parse")
    }

    override DataFlow::Node getATaintSource() {
      exists (ModuleInstance m |
        m.getPath() = "url" or m.getPath() = "querystring" |
        astNode = m.getAMethodCall("parse") and
        result.asExpr() = astNode.(CallExpr).getArgument(0)
      )
    }
  }

  /**
   * A call to a path-module method that preserves taint.
   */
  private class PathFlowTarget extends TaintTracking::FlowTarget, DataFlow::ValueNode {

    Expr tainted;

    PathFlowTarget() {
      exists (ModuleInstance pathModule, CallExpr call, string methodName |
        astNode = call and
        pathModule.getPath() = "path" and
        astNode = pathModule.getAMethodCall(methodName) |
        // getters
        (methodName = "basename" and tainted = call.getArgument(0)) or
        (methodName = "dirname" and tainted = call.getArgument(0)) or
        (methodName = "extname" and tainted = call.getArgument(0)) or

        // transformers
        (methodName = "join" and tainted = call.getAnArgument()) or
        (methodName = "normalize" and tainted = call.getArgument(0)) or
        (methodName = "relative" and tainted = call.getArgument([0..1])) or
        (methodName = "resolve" and tainted = call.getAnArgument()) or
        (methodName = "toNamespacedPath" and tainted = call.getArgument(0))
      )
    }

    override DataFlow::Node getATaintSource() {
        result.asExpr() = tainted
    }

  }

  /**
   * An expression passed as the first argument to the `write` or `end` method
   * of an HTTP response.
   */
  private class ResponseSendArgument extends HTTP::ResponseSendArgument {
    HTTP::RouteHandler rh;

    ResponseSendArgument() {
      exists (MethodCallExpr mce, string m | m = "write" or m = "end" |
        mce.calls(any(ResponseExpr e | e.getARouteHandler() = rh), m) and
        this = mce.getArgument(0) and
        // don't mistake callback functions as data
        not this.(DataFlowNode).getALocalSource() instanceof Function
      )
    }

    override HTTP::RouteHandler getHandler() { result = rh }
  }

  /**
   * A Node.js server application.
   */
  class Server extends HTTP::Servers::StandardServer {
    Server() {
      isCreateServer(this)
    }
  }

  /** An expression that is passed as `http.request({ auth: <expr> }, ...)`. */
  class Credentials extends CredentialsExpr {

    Credentials() {
      exists (CallExpr call |
        exists (ModuleInstance http |
          http.getPath() = "http" or http.getPath() = "https" |
          call = http.getAMethodCall("request")
        ) and
        call.hasOptionArgument(0, "auth", this)
      )
    }

    override string getCredentialsKind() {
      result = "credentials"
    }

  }

  /**
   * A call a process-terminating function, such as `process.exit`.
   */
  class ProcessTermination extends SensitiveAction {

    ProcessTermination() {
      exists (Expr callee |
        this.asExpr().(CallExpr).getCallee().(DataFlowNode).getALocalSource() = callee |
        exists(ModuleInstance mod |
          mod.getPath() = "exit" and
          callee = mod
        ) or
        exists(PropAccess exit |
          exit.accesses(any(Expr e | e.accessesGlobal("process")), "exit") and
          callee = exit
        )
      )
    }

  }

}
