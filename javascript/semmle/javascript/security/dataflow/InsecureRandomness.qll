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
 * Provides a taint tracking configuration for reasoning about random values that are not cryptographically secure.
 */
import javascript
private import semmle.javascript.security.SensitiveActions

/**
 * A data flow source for random values that are not cryptographically secure.
 */
abstract class InsecureRandomnessSource extends DataFlow::Node { }

/**
 * A data flow sink for random values that are not cryptographically secure.
 */
abstract class InsecureRandomnessSink extends DataFlow::Node { }

/**
 * A sanitizer for random values that are not cryptographically secure.
 */
abstract class InsecureRandomnessSanitizer extends DataFlow::Node { }

/**
 * A taint tracking configuration for random values that are not cryptographically secure.
 */
class InsecureRandomnessDataFlowConfiguration extends TaintTracking::Configuration {
  InsecureRandomnessDataFlowConfiguration() {
    this = "InsecureRandomnessDataFlowConfiguration"
  }

  override
  predicate isSource(DataFlow::Node source) {
    source instanceof InsecureRandomnessSource
  }

  override
  predicate isSink(DataFlow::Node sink) {
    sink instanceof InsecureRandomnessSink or
    sink.asExpr() instanceof SensitiveExpr
  }

  override
  predicate isSanitizer(DataFlow::Node node) {
    // not making use of `super.isSanitizer`: those sanitizers are not for this kind of data
    node instanceof InsecureRandomnessSanitizer
  }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    // Assume that all operations on tainted values preserve taint: crypto is hard
    succ.asExpr().(BinaryExpr).getAnOperand() = pred.asExpr() or
    succ.asExpr().(UnaryExpr).getOperand() = pred.asExpr()
  }

}

/**
 * A simple random number generator that is not cryptographically secure.
 */
class DefaultInsecureRandomnessSource extends InsecureRandomnessSource {

  DefaultInsecureRandomnessSource() {
    exists (Expr callee |
      this.asExpr().(CallExpr).getCallee().(DataFlowNode).getALocalSource() = callee |
      exists(ModuleInstance mod, string name |
        mod.getPath() = name |
        // require("random-number")();
        name = "random-number" and
        callee = mod
        or
        // require("random-int")();
        name = "random-int" and
        callee = mod
        or
        // require("random-float")();
        name = "random-float" and
        callee = mod
        or
        // require('random-seed').create()();
        name = "random-seed" and
        callee = mod.getAMethodCall("create")
        or
        // require('unique-random')()();
        name = "unique-random" and
        callee = any(CallExpr call | call.getCallee().(DataFlowNode).getALocalSource() = mod)
      ) or
      exists(PropAccess mathRandom |
        // Math.random()
        mathRandom.accesses(any(Expr e | e.accessesGlobal("Math")), "random") and
        callee = mathRandom
      )
    ) or
    exists(ModuleInstance mod, NewExpr instance | mod.getPath() = "chance" |
      // (new require('chance')).<name>(),
      instance.getCallee().(DataFlowNode).getALocalSource() = mod and
      this.asExpr().(MethodCallExpr).getReceiver().(DataFlowNode).getALocalSource() = instance
    )
  }

}
