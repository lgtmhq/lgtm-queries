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

  private class RouteHandler extends HTTP::RouteHandler {

    RequestListener function;

    RouteHandler() {
      function = this
    }

    override HTTP::HeaderDefinition getAResponseHeader(string name){
      exists(SetHeader h |
        h.getResponse().(DataFlowNode).getALocalSource() = this.getResponseVariable().getAnAccess() and
        name = h.getAHeaderName() and
        result = h)
    }

    /**
    * Gets the variable that contains the request object.
    */
    Variable getRequestVariable(){
      result = function.getParameter(0).(SimpleParameter).getVariable()
    }

    /**
    * Gets the variable that contains the request object.
    */
    Variable getResponseVariable(){
      result = function.
      getParameter(1).(SimpleParameter).getVariable()
    }

    /**
     * Gets a server this handler is registered on.
     */
    Server getAServer() {
      result = function.getAServer()
    }
  }

  /**
   * An HTTP request listener.
   */
  class RequestListener extends Function {

    Server server;

    RequestListener() {
      exists (MethodCallExpr mce |
        this = mce.getLastArgument().(DataFlowNode).getALocalSource() |
        server = mce // registration during server creation
        or
        server = mce.getReceiver().(DataFlowNode).getALocalSource() and
        mce.getMethodName().regexpMatch("on(ce)?") and
        mce.getArgument(0).getStringValue() = "request"
      )
    }

    /**
     * Gets a server this listener is registered on.
    */
    Server getAServer() {
      result = server
    }
  }

  /**
   * Holds if `nd` is an HTTP request object.
   */
  predicate isRequest(DataFlowNode nd) {
    exists (Variable req |
      req.getADeclaration() = any(RequestListener lr).getParameter(0) and
      nd.getALocalSource() = req.getAnAccess()
    )
  }

  /**
   * Holds if `nd` is an HTTP response object.
   */
  predicate isResponse(DataFlowNode nd) {
    exists (Variable res |
      res.getADeclaration() = any(RequestListener h).getParameter(1) and
      nd.getALocalSource() = res.getAnAccess()
    )
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

  private abstract class HeaderDefinition extends HTTP::ExplicitHeaderDefinition {
    Expr response;

    /**
     * Gets the response object this set is set on.
     */
    Expr getResponse() {
      result = response
    }
  }

  /**
   * A call to the `setHeader` method of an HTTP response.
   */
  private class SetHeader extends HeaderDefinition, MethodCallExpr {
    SetHeader() {
      isResponse(getReceiver()) and response = getReceiver() and
      getMethodName() = "setHeader"
    }

    override predicate definesExplicitly(string headerName, Expr headerValue) {
      headerName = getArgument(0).getStringValue() and
      headerValue = getArgument(1)
    }
  }

  /**
   * A call to the `writeHead` method of an HTTP response.
   */
  private class WriteHead extends HeaderDefinition, MethodCallExpr {
    WriteHead() {
      isResponse(getReceiver()) and response = getReceiver() and
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
  class Server extends HTTP::Server {
    Server() {
      isCreateServer(this)
    }

    override RouteHandler getARouteHandler() {
      result.getAServer() = this
    }
  }

 }
