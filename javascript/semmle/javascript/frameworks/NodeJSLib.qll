// Copyright 2017 Semmle Ltd.
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

  class RouteHandler extends HTTP::Servers::StandardRouteHandler {

    Function function;

    RouteHandler() {
      function = this and
      any(RouteSetup setup).getARouteHandler() = this
    }

    private DataFlowNode getALocalParameterUse(int paramIndex){
      exists(SimpleParameter param |
        param = function.getParameter(paramIndex) and
        param.getAnInitialUse() = result.getALocalSource()
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

  /**
   * A read access to the `url` property of an HTTP request.
   */
  private class RequestUrlAccess extends RemoteFlowSource {
    RequestUrlAccess() {
      exists (PropReadNode prn | this = prn |
        isRequest(prn.getBase()) and prn.getPropertyName() = "url"
      )
    }

    override string getSourceType() {
      result = "Node.js request URL"
    }
  }

  private abstract class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {

    HeaderDefinition(){
      isResponse(getReceiver())
    }

    override RouteHandler getARouteHandler(){
      getReceiver() = result.getAResponseExpr()
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
  private class UrlParsingFlowTarget extends TaintTracking::FlowTarget, @callexpr {
    override DataFlowNode getATaintSource() {
      exists (ModuleInstance m |
        m.getPath() = "url" or m.getPath() = "querystring" |
        this = m.getAMethodCall("parse") and result = this.(CallExpr).getArgument(0)
      )
    }
  }

  /**
   * An expression passed as the first argument to the `write` or `end` method
   * of an HTTP response.
   */
  private class ResponseBody extends HTTP::ResponseBody {
    ResponseBody() {
      exists (MethodCallExpr mce |
        isResponse(mce.getReceiver()) and
        (mce.getMethodName() = "write" or mce.getMethodName() = "end") and
        this = mce.getArgument(0) and
        // don't mistake callback functions as data
        not this.(DataFlowNode).getALocalSource() instanceof Function
      )
    }
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
}
