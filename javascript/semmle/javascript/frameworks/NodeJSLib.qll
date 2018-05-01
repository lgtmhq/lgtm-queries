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
   * Gets a reference to the 'process' object.
   */
  DataFlow::SourceNode process() {
    result = DataFlow::globalVarRef("process") or
    result = DataFlow::moduleImport("process")
  }

  /**
   * Holds if `call` is an invocation of `http.createServer` or `https.createServer`.
   */
  predicate isCreateServer(CallExpr call) {
    exists (DataFlow::ModuleImportNode http |
      http.getPath() = "http" or http.getPath() = "https" |
      call = http.getAMemberCall("createServer").asExpr()
    )
  }

  /**
   * A Node.js HTTP response.
   *
   * A server library that provides an (enhanced) NodesJS HTTP response
   * object should implement a library specific subclass of this class.
   */
  abstract class ResponseExpr extends HTTP::Servers::StandardResponseExpr {
  }

  /**
   * A Node.js HTTP request.
   *
   * A server library that provides an (enhanced) NodesJS HTTP request
   * object should implement a library specific subclass of this class.
   */
  abstract class RequestExpr extends HTTP::Servers::StandardRequestExpr {
  }

  /**
   * A Node.js route handler.
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
   * A Node.js response source, that is, the response parameter of a
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
   * A Node.js request source, that is, the request parameter of a
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
   * A builtin Node.js HTTP response.
   */
  private class BuiltinRouteHandlerResponseExpr extends ResponseExpr {
    BuiltinRouteHandlerResponseExpr() { src instanceof ResponseSource }
  }

  /**
   * A builtin Node.js HTTP request.
   */
  private class BuiltinRouteHandlerRequestExpr extends RequestExpr {
    BuiltinRouteHandlerRequestExpr() { src instanceof RequestSource }
  }

  /**
   * An access to a user-controlled Node.js request input.
   */
  private class RequestInputAccess extends HTTP::RequestInputAccess {
    RequestExpr request;
    string kind;

    RequestInputAccess() {
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
    }

    override RouteHandler getRouteHandler() {
      result = request.getRouteHandler()
    }

    override string getKind() {
      result = kind
    }
  }

  class RouteSetup extends MethodCallExpr, HTTP::Servers::StandardRouteSetup {
    ServerDefinition server;
    Expr handler;

    RouteSetup() {
      server.flowsTo(this) and
      handler = getArgument(0)
      or
      server.flowsTo(getReceiver()) and
      getMethodName().regexpMatch("on(ce)?") and
      getArgument(0).getStringValue() = "request" and
      handler = getArgument(1)
    }

    override DataFlow::SourceNode getARouteHandler() {
      result.flowsToExpr(handler)
    }

    override Expr getServer() {
      result = server
    }

  }

  private abstract class HeaderDefinition extends HTTP::Servers::StandardHeaderDefinition {

    ResponseExpr r;

    HeaderDefinition(){
      astNode.getReceiver() = r
    }

    override HTTP::RouteHandler getRouteHandler(){
      result = r.getRouteHandler()
    }

  }

  /**
   * A call to the `setHeader` method of an HTTP response.
   */
  private class SetHeader extends HeaderDefinition {
    SetHeader() {
      astNode.getMethodName() = "setHeader"
    }
  }

  /**
   * A call to the `writeHead` method of an HTTP response.
   */
  private class WriteHead extends HeaderDefinition {
    WriteHead() {
      astNode.getMethodName() = "writeHead" and
      astNode.getNumArgument() > 1
    }

    override predicate definesExplicitly(string headerName, Expr headerValue) {
      exists (DataFlow::SourceNode headers |
        headers.flowsToExpr(astNode.getLastArgument()) and
        headers.hasPropertyWrite(headerName, DataFlow::valueNode(headerValue))
      )
    }
  }

  /**
   * A call to a path-module method that preserves taint.
   */
  private class PathFlowTarget extends TaintTracking::DefaultTaintStep, DataFlow::ValueNode {
    override CallExpr astNode;
    Expr tainted;

    PathFlowTarget() {
      exists (DataFlow::ModuleImportNode pathModule, string methodName |
        pathModule.getPath() = "path" and
        this = pathModule.getAMemberCall(methodName) |
        // getters
        (methodName = "basename" and tainted = astNode.getArgument(0)) or
        (methodName = "dirname" and tainted = astNode.getArgument(0)) or
        (methodName = "extname" and tainted = astNode.getArgument(0)) or

        // transformers
        (methodName = "join" and tainted = astNode.getAnArgument()) or
        (methodName = "normalize" and tainted = astNode.getArgument(0)) or
        (methodName = "relative" and tainted = astNode.getArgument([0..1])) or
        (methodName = "resolve" and tainted = astNode.getAnArgument()) or
        (methodName = "toNamespacedPath" and tainted = astNode.getArgument(0))
      )
    }

    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      pred.asExpr() = tainted and succ = this
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
        mce.calls(any(ResponseExpr e | e.getRouteHandler() = rh), m) and
        this = mce.getArgument(0) and
        // don't mistake callback functions as data
        not this.analyze().getAValue() instanceof AbstractFunction
      )
    }

    override HTTP::RouteHandler getRouteHandler() { result = rh }
  }

  /**
   * An expression that creates a new Node.js server.
   */
  class ServerDefinition extends HTTP::Servers::StandardServerDefinition {
    ServerDefinition() {
      isCreateServer(this)
    }
  }

  /** An expression that is passed as `http.request({ auth: <expr> }, ...)`. */
  class Credentials extends CredentialsExpr {

    Credentials() {
      exists (CallExpr call |
        exists (DataFlow::ModuleImportNode http |
          http.getPath() = "http" or http.getPath() = "https" |
          call = http.getAMemberCall("request").asExpr()
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
  class ProcessTermination extends SensitiveAction, DataFlow::ValueNode {
    override CallExpr astNode;

    ProcessTermination() {
      this = DataFlow::moduleImport("exit").getAnInvocation()
      or
      this = process().getAMemberCall("exit")
    }

  }

  /**
   * Holds if the `i`th parameter of method `methodName` of the Node.js
   * `fs` module might represent a file path.
   *
   * We determine this by looking for an externs declaration for
   * `fs.methodName` where the `i`th parameter's name is `filename` or
   * `path` or a variation thereof.
   */
  private predicate fsFileParam(string methodName, int i) {
    exists (ExternalMemberDecl decl, Function f, JSDocParamTag p, string n |
      decl.hasQualifiedName("fs", methodName) and f = decl.getInit() and
      p.getDocumentedParameter() = f.getParameter(i).getAVariable() and
      n = p.getName().toLowerCase() |
      n = "filename" or n.regexpMatch("(old|new|src|dst|)path")
    )
  }


  /**
   * A call to a method from module `fs` or `graceful-fs`.
   */
  private class NodeJSFileSystemAccess extends FileSystemAccess, DataFlow::ValueNode {
    override MethodCallExpr astNode;

    NodeJSFileSystemAccess() {
      exists (DataFlow::ModuleImportNode fs |
        fs.getPath() = "fs" or fs.getPath() = "graceful-fs" |
        this = fs.getAMemberCall(_)
      )
    }

    override DataFlow::Node getAPathArgument() {
      exists (int i | fsFileParam(astNode.getMethodName(), i) |
        result = DataFlow::valueNode(astNode.getArgument(i))
      )
    }
  }

  /**
   * A call to a method from module `child_process`.
   */
  private class ChildProcessMethodCall extends SystemCommandExecution, DataFlow::ValueNode {
    override MethodCallExpr astNode;

    ChildProcessMethodCall() {
      this = DataFlow::moduleImport("child_process").getAMemberCall(_)
    }

    override DataFlow::Node getACommandArgument() {
      // check whether this is an invocation of an exec/spawn/fork method
      exists (string methodName | methodName = astNode.getMethodName() |
        methodName = "exec" or
        methodName = "execSync" or
        methodName = "execFile" or
        methodName = "execFileSync" or
        methodName = "spawn" or
        methodName = "spawnSync" or
        methodName = "fork"
      )
      and
      // all of the above methods take the command as their first argument
      result = DataFlow::valueNode(astNode.getArgument(0))
    }
  }
}
