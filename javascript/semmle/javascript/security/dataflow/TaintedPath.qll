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
 * Provides a taint tracking configuration for reasoning about tainted-path
 * vulnerabilities.
 */

import javascript

/**
 * A data flow source for tainted-path vulnerabilities.
 */
abstract class TaintedPathSource extends DataFlow::Node { }

/**
 * A data flow sink for tainted-path vulnerabilities.
 */
abstract class TaintedPathSink extends DataFlow::Node { }

/**
 * A sanitizer for tainted-path vulnerabilities.
 */
abstract class TaintedPathSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about tainted-path vulnerabilities.
 */
class TaintedPathTrackingConfig extends TaintTracking::Configuration {
  TaintedPathTrackingConfig() {
    this = "TaintedPath"
  }

  override predicate isSource(DataFlow::Node source) {
    source instanceof TaintedPathSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof TaintedPathSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof TaintedPathSanitizer
  }
}

/**
 * An expression whose value is interpreted as a path to a module, making it
 * a data flow sink for tainted-path vulnerabilities.
 */
class ModulePathSink extends TaintedPathSink, DataFlow::ValueNode {
  ModulePathSink() {
    astNode = any(Require rq).getArgument(0) or
    astNode = any(AMDModuleDefinition amd).getDependencies()
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
class FsPathSink extends TaintedPathSink, DataFlow::ValueNode {
  FsPathSink() {
    exists (MethodCallExpr mce, ModuleInstance fs, int i |
      mce.getReceiver().(DataFlowNode).getALocalSource() = fs and
      (fs.getPath() = "fs" or fs.getPath() = "graceful-fs") and
      astNode = mce.getArgument(i) and
      fsFileParam(mce.getMethodName(), i)
    )
  }
}

/**
 * A path argument to the Express `res.render` method.
 */
class ExpressRenderSink extends TaintedPathSink, DataFlow::ValueNode {
  ExpressRenderSink() {
    exists (MethodCallExpr mce |
      Express::isResponse(mce.getReceiver()) and
      mce.getMethodName() = "render" and
      astNode = mce.getArgument(0)
    )
  }
}

/**
 * A `templateUrl` member of an AngularJS directive.
 */
class AngularJSTemplateUrlSink extends TaintedPathSink, DataFlow::ValueNode {
  AngularJSTemplateUrlSink() {
    astNode = any(AngularJS::CustomDirective d).getMember("templateUrl")
  }
}

/**
 * Holds if `check` evaluating to `outcome` is not sufficient to sanitize `path`.
 */
predicate weakCheck(Expr check, boolean outcome, VarAccess path) {
  // `path.startsWith`, `path.endsWith`, `fs.existsSync(path)`
  exists (Expr base, string m | check.(MethodCallExpr).calls(base, m) |
    path = base and
    (m = "startsWith" or m = "endsWith")
    or
    path = check.(MethodCallExpr).getArgument(0) and
    m.regexpMatch("exists(Sync)?")
  ) and
  (outcome = true or outcome = false)
  or
  // `path.indexOf` comparisons
  check.(Comparison).getAnOperand().(MethodCallExpr).calls(path, "indexOf") and
  (outcome = true or outcome = false)
  or
  // `path != null`, `path != undefined`, `path != "somestring"`
  exists (EqualityTest eq, Expr op |
    eq = check and eq.hasOperands(path, op) and outcome = eq.getPolarity().booleanNot() |
    op instanceof NullLiteral or
    op instanceof SyntacticConstants::UndefinedConstant or
    exists(op.getStringValue())
  )
  or
  // `path`
  check = path and
  (outcome = true or outcome = false)
}

/**
 * A conditional involving the path, that is not considered to be a weak check.
 */
class StrongPathCheck extends TaintTracking::SanitizingGuard {
  VarAccess path;
  boolean sanitizedOutcome;

  StrongPathCheck() {
    exists (ConditionGuardNode cgg | this = cgg.getTest() |
      this = path.getParentExpr*() and
      path = any(SsaVariable v).getAUse() and
      (sanitizedOutcome = true or sanitizedOutcome = false) and
      not weakCheck(this, sanitizedOutcome, path)
    )
  }

  override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, Expr e) {
    cfg instanceof TaintedPathTrackingConfig and
    path = e and
    outcome = sanitizedOutcome
  }
}
