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

module InsecureRandomness {
  /**
   * A data flow source for random values that are not cryptographically secure.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for random values that are not cryptographically secure.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for random values that are not cryptographically secure.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint tracking configuration for random values that are not cryptographically secure.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "InsecureRandomness" }

    override
    predicate isSource(DataFlow::Node source) {
      source instanceof Source
    }

    override
    predicate isSink(DataFlow::Node sink) {
      sink instanceof Sink
    }

    override
    predicate isSanitizer(DataFlow::Node node) {
      // not making use of `super.isSanitizer`: those sanitizers are not for this kind of data
      node instanceof Sanitizer
    }

    override
    predicate isSanitizer(DataFlow::Node pred, DataFlow::Node succ) {
      // stop propagation at the sinks to avoid double reporting
      pred instanceof Sink and
      // constrain succ
      pred = succ.getAPredecessor()

    }

    override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
      // Assume that all operations on tainted values preserve taint: crypto is hard
      succ.asExpr().(BinaryExpr).getAnOperand() = pred.asExpr() or
      succ.asExpr().(UnaryExpr).getOperand() = pred.asExpr() or
      exists (DataFlow::MethodCallNode mc |
        mc = DataFlow::globalVarRef("Math").getAMemberCall(_) and
        pred = mc.getAnArgument() and succ = mc
      )

    }

  }

  /**
   * A simple random number generator that is not cryptographically secure.
   */
  class DefaultSource extends Source, DataFlow::ValueNode {
    override CallExpr astNode;

    DefaultSource() {
      exists(DataFlow::ModuleImportNode mod, string name | mod.getPath() = name |
        // require("random-number")();
        name = "random-number" and
        this = mod.getACall()
        or
        // require("random-int")();
        name = "random-int" and
        this = mod.getACall()
        or
        // require("random-float")();
        name = "random-float" and
        this = mod.getACall()
        or
        // require('random-seed').create()();
        name = "random-seed" and
        this = mod.getAMemberCall("create").getACall()
        or
        // require('unique-random')()();
        name = "unique-random" and
        this = mod.getACall().getACall()
      )
      or
      // Math.random()
      this = DataFlow::globalVarRef("Math").getAMemberCall("random")
      or
      // (new require('chance')).<name>()
      this = DataFlow::moduleImport("chance").getAnInstantiation().getAMemberInvocation(_)
    }
  }

  /**
   * A sensitive write, considered as a sink for random values that are not cryptographically
   * secure.
   */
  class SensitiveWriteSink extends Sink {
    SensitiveWriteSink() { this instanceof SensitiveWrite }
  }

  /**
   * A cryptographic key, considered as a sink for random values that are not cryptographically
   * secure.
   */
  class CryptoKeySink extends Sink {
    CryptoKeySink() { this instanceof CryptographicKey }
  }

}

/** DEPRECATED: Use `InsecureRandomness::Source` instead. */
deprecated class InsecureRandomnessSource = InsecureRandomness::Source;

/** DEPRECATED: Use `InsecureRandomness::Sink` instead. */
deprecated class InsecureRandomnessSink = InsecureRandomness::Sink;

/** DEPRECATED: Use `InsecureRandomness::Sanitizer` instead. */
deprecated class InsecureRandomnessSanitizer = InsecureRandomness::Sanitizer;

/** DEPRECATED: Use `InsecureRandomness::Configuration` instead. */
deprecated class InsecureRandomnessDataFlowConfiguration = InsecureRandomness::Configuration;
