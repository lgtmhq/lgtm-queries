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
 * Provides a taint-tracking configuration for reasoning about code injection.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources

module CodeInjection {
  /**
   * A data flow source for code injection vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for code injection vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for code injection vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint-tracking configuration for reasoning about code injection vulnerabilities.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "CodeInjection" }

    override predicate isSource(DataFlow::Node source) {
      source instanceof Source
    }

    override predicate isSink(DataFlow::Node sink) {
      sink instanceof Sink
    }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      isSafeLocationProperty(node.asExpr()) or
      node instanceof Sanitizer
    }

    override predicate isAdditionalTaintStep(DataFlow::Node src, DataFlow::Node trg) {
      // HTML sanitizers are insufficient protection against code injection
      exists(CallExpr htmlSanitizer, string calleeName |
        calleeName = htmlSanitizer.getCalleeName() and
        calleeName.regexpMatch("(?i).*html.*") and
        calleeName.regexpMatch("(?i).*(saniti[sz]|escape|strip).*") and
        trg.asExpr() = htmlSanitizer and src.asExpr() = htmlSanitizer.getArgument(0)
      )
    }
  }

  /** A source of remote user input, considered as a flow source for code injection. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * An access to a property that may hold (parts of) the document URL.
   */
  class LocationSource extends Source, DataFlow::ValueNode {
    LocationSource() {
      isDocumentURL(astNode)
    }
  }

  /**
   * An expression which may be interpreted as an AngularJS expression.
   */
  class AngularJSExpressionSink extends Sink, DataFlow::ValueNode {
    AngularJSExpressionSink() {
      any(AngularJS::AngularJSCall call).interpretsArgumentAsCode(this.asExpr())
    }
  }

  /**
   * An expression which may be evaluated as JavaScript in NodeJS using the 
   * `vm` module.
   */
  class NodeJSVmSink extends Sink, DataFlow::ValueNode {
    NodeJSVmSink() {
      exists(NodeJSLib::VmModuleMethodCall call | 
        this = call.getACodeArgument()
      )
    }
  }
  
  /**
   * An expression which may be evaluated as JavaScript.
   */
  class EvalJavaScriptSink extends Sink, DataFlow::ValueNode {
    EvalJavaScriptSink() {
      exists (DataFlow::InvokeNode c, int index |
        exists (string callName |
          c = DataFlow::globalVarRef(callName).getAnInvocation() |
          callName = "eval" and index = 0 or
          callName = "Function" or
          callName = "execScript" and index = 0 or
          callName = "executeJavaScript" and index = 0 or
          callName = "execCommand" and index = 0 or
          callName = "setTimeout" and index = 0 or
          callName = "setInterval" and index = 0 or
          callName = "setImmediate" and index = 0
        )
        or
        exists (DataFlow::GlobalVarRefNode wasm, string methodName |
          wasm.getName() = "WebAssembly" and c = wasm.getAMemberCall(methodName) |
          methodName = "compile" or
          methodName = "compileStreaming"
        )
      |
      this = c.getArgument(index)
      )
    }
  }
}

/** DEPRECATED: Use `CodeInjection::Source` instead. */
deprecated class CodeInjectionSource = CodeInjection::Source;

/** DEPRECATED: Use `CodeInjection::Sink` instead. */
deprecated class CodeInjectionSink = CodeInjection::Sink;

/** DEPRECATED: Use `CodeInjection::Sanitizer` instead. */
deprecated class CodeInjectionSanitizer = CodeInjection::Sanitizer;

/** DEPRECATED: Use `CodeInjection::Configuration` instead. */
deprecated class CodeInjectionDataFlowConfiguration = CodeInjection::Configuration;
