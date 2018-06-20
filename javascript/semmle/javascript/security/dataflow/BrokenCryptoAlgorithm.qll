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
 * Provides a taint tracking configuration for reasoning about sensitive information in broken or weak cryptographic algorithms.
 */
import javascript
private import semmle.javascript.security.SensitiveActions
private import semmle.javascript.frameworks.CryptoLibraries

module BrokenCryptoAlgorithm {
  /**
   * A data flow source for sensitive information in broken or weak cryptographic algorithms.
   */
  abstract class Source extends DataFlow::Node {
    /** Gets a string that describes the type of this data flow source. */
    abstract string describe();
  }

  /**
   * A data flow sink for sensitive information in broken or weak cryptographic algorithms.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for sensitive information in broken or weak cryptographic algorithms.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint tracking configuration for sensitive information in broken or weak cryptographic algorithms.
   *
   * This configuration identifies flows from `Source`s, which are sources of
   * sensitive data, to `Sink`s, which is an abstract class representing all
   * the places sensitive data may used in broken or weak cryptographic algorithms. Additional sources or sinks can be
   * added either by extending the relevant class, or by subclassing this configuration itself,
   * and amending the sources and sinks.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "BrokenCryptoAlgorithm" }

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
      super.isSanitizer(node) or
      node instanceof Sanitizer
    }
  }

  /**
   * A sensitive expression, viewed as a data flow source for sensitive information
   * in broken or weak cryptographic algorithms.
   */
  class SensitiveExprSource extends Source, DataFlow::ValueNode {
    override SensitiveExpr astNode;

    override string describe() {
      result = astNode.describe()
    }
  }

  /**
   * An expression used by a broken or weak cryptographic algorithm.
   */
  class WeakCryptographicOperationSink extends Sink {
    WeakCryptographicOperationSink() {
      exists(CryptographicOperation application |
        application.getAlgorithm().isWeak() and
        this.asExpr() = application.getInput()
      )
    }
  }
}

/** DEPRECATED: Use `BrokenCryptoAlgorithm::Source` instead. */
deprecated class BrokenCryptoAlgorithmSource = BrokenCryptoAlgorithm::Source;

/** DEPRECATED: Use `BrokenCryptoAlgorithm::Sink` instead. */
deprecated class BrokenCryptoAlgorithmSink = BrokenCryptoAlgorithm::Sink;

/** DEPRECATED: Use `BrokenCryptoAlgorithm::Sanitizer` instead. */
deprecated class BrokenCryptoAlgorithmSanitizer = BrokenCryptoAlgorithm::Sanitizer;

/** DEPRECATED: Use `BrokenCryptoAlgorithm::Configuration` instead. */
deprecated class BrokenCryptoAlgorithmDataFlowConfiguration = BrokenCryptoAlgorithm::Configuration;
