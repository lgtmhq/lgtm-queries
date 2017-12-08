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
 * Provides a dataflow configuration for reasoning about sensitive information in broken or weak cryptographic algorithms.
 */
import javascript
private import semmle.javascript.flow.Tracking
private import semmle.javascript.security.SensitiveActions
private import semmle.javascript.frameworks.CryptoLibraries

/**
 * A dataflow source for sensitive information in broken or weak cryptographic algorithms.
 */
abstract class BrokenCryptoAlgorithmSource extends DataFlowNode { }

/**
 * A dataflow sink for sensitive information in broken or weak cryptographic algorithms.
 */
abstract class BrokenCryptoAlgorithmSink extends DataFlowNode { }

/**
 * A sanitizer for sensitive information in broken or weak cryptographic algorithms.
 */
abstract class BrokenCryptoAlgorithmSanitizer extends DataFlowNode { }

/**
 * A dataflow configuration for sensitive information in broken or weak cryptographic algorithms.
 *
 * This configuration identifies flows from `BrokenCryptoAlgorithmSource`s, which are sources of
 * sensitive data, to `BrokenCryptoAlgorithmSink`s, which is an abstract class representing all
 * the places sensitive data may used in broken or weak cryptographic algorithms. Additional sources or sinks can be
 * added either by extending the relevant class, or by subclassing this configuration itself,
 * and amending the sources and sinks.
 */
class BrokenCryptoAlgorithmDataFlowConfiguration extends TaintTracking::Configuration {
  BrokenCryptoAlgorithmDataFlowConfiguration() {
    this = "BrokenCryptoAlgorithm"
  }

  override
  predicate isSource(DataFlowNode source) {
    source instanceof BrokenCryptoAlgorithmSource or
    source instanceof SensitiveExpr
  }

  override
  predicate isSink(DataFlowNode sink) {
    sink instanceof BrokenCryptoAlgorithmSink
  }

  override
  predicate isSanitizer(DataFlowNode node) {
    super.isSanitizer(node) or
    node instanceof BrokenCryptoAlgorithmSanitizer
  }
}

/**
 * An expression used by a broken or weak cryptographic algorithm.
 */
class WeakCryptographicOperationSink extends BrokenCryptoAlgorithmSink {
  WeakCryptographicOperationSink() {
    exists(CryptographicOperation application |
      application.getAlgorithm().isWeak() and
      this = application.getInput()
    )
  }
}

