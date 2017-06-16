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
 * Provides a taint tracking configuration for reasoning about tainted-path
 * vulnerabilities.
 */

import javascript

/**
 * A data flow source for tainted-path vulnerabilities.
 */
abstract class TaintedPathSource extends DataFlowNode { }

/**
 * A data flow sink for tainted-path vulnerabilities.
 */
abstract class TaintedPathSink extends DataFlowNode { }

/**
 * A sanitizer for tainted-path vulnerabilities.
 */
abstract class TaintedPathSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about tainted-path vulnerabilities.
 */
class TaintedPathTrackingConfig extends TaintTracking::Configuration {
  TaintedPathTrackingConfig() {
    this = "TaintedPath"
  }

  override predicate isSource(DataFlowNode source) {
    source instanceof TaintedPathSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof TaintedPathSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    node instanceof TaintedPathSanitizer
  }
}

/**
 * An expression whose value is interpreted as a path to a module, making it
 * a data flow sink for tainted-path vulnerabilities.
 */
class ModulePathSink extends TaintedPathSink {
  ModulePathSink() {
    this = any(Require rq).getArgument(0) or
    this = any(AMDModuleDefinition amd).getDependencies()
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
 * A path argument to a file system function from Node's `fs` or `graceful-fs`
 * modules.
 */
class FsPathSink extends TaintedPathSink {
  FsPathSink() {
    exists (MethodCallExpr mce, ModuleInstance fs, int i |
      mce.getReceiver().(DataFlowNode).getALocalSource() = fs and
      (fs.getPath() = "fs" or fs.getPath() = "graceful-fs") and
      this = mce.getArgument(i) and
      fsFileParam(mce.getMethodName(), i)
    )
  }
}

/**
 * A path argument to the Express `res.render` method.
 */
class ExpressRenderSink extends TaintedPathSink {
  ExpressRenderSink() {
    exists (MethodCallExpr mce |
      Express::isResponse(mce.getReceiver()) and
      mce.getMethodName() = "render" and
      this = mce.getArgument(0)
    )
  }
}

/**
 * Holds if this expression is part of a check that is insufficient to prevent
 * path tampering.
 */
private predicate inWeakCheck(Expr e) {
  exists (MethodCallExpr m | e = m.getReceiver() |
    m.getMethodName() = "startsWith" or
    m.getMethodName() = "endsWith" or
    m.getMethodName().regexpMatch("exists(Sync)?")
  ) or
  exists (Expr op | op = e.(EqualityTest).getAnOperand() |
    op instanceof NullLiteral or
    op.(GlobalVarAccess).getName() = "undefined" or
    op.getStringValue() = ""
  )
}

/**
 * A conditional involving the path, that is not considered to be a weak check.
 */
class StrongPathCheck extends TaintTracking::SanitizingGuard, VarUse {
  StrongPathCheck() {
    not inWeakCheck(this)
  }

  override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
    cfg instanceof TaintedPathTrackingConfig and
    (outcome = true or outcome = false) and
    this = v.getAUse()
  }
}
