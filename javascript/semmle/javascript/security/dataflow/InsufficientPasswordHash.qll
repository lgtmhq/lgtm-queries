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
 * Provides a taint tracking configuration for reasoning about password hashing with insufficient computational effort.
 */
import javascript
private import semmle.javascript.flow.Tracking
private import semmle.javascript.security.SensitiveActions
private import semmle.javascript.frameworks.CryptoLibraries

/**
 * A data flow source for password hashing with insufficient computational effort.
 */
abstract class InsufficientPasswordHashSource extends DataFlow::Node { }

/**
 * A data flow sink for password hashing with insufficient computational effort.
 */
abstract class InsufficientPasswordHashSink extends DataFlow::Node { }

/**
 * A sanitizer for password hashing with insufficient computational effort.
 */
abstract class InsufficientPasswordHashSanitizer extends DataFlow::Node { }

/**
 * A taint tracking configuration for password hashing with insufficient computational effort.
 *
 * This configuration identifies flows from `InsufficientPasswordHashSource`s, which are sources of
 * password data, to `InsufficientPasswordHashSink`s, which is an abstract class representing all
 * the places password data may be hashed with insufficient computational effort. Additional sources or sinks can be
 * added either by extending the relevant class, or by subclassing this configuration itself,
 * and amending the sources and sinks.
 */
class InsufficientPasswordHashDataFlowConfiguration extends TaintTracking::Configuration {
  InsufficientPasswordHashDataFlowConfiguration() {
    this = "InsufficientPasswordHash"
  }

  override
  predicate isSource(DataFlow::Node source) {
    source instanceof InsufficientPasswordHashSource or
    source.asExpr() instanceof CleartextPasswordExpr
  }

  override
  predicate isSink(DataFlow::Node sink) {
    sink instanceof InsufficientPasswordHashSink
  }

  override
  predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof InsufficientPasswordHashSanitizer
  }
}

/**
 * An expression used by a cryptographic algorithm that is not suitable for password hashing.
 */
class InsufficientPasswordHashAlgorithm extends InsufficientPasswordHashSink {
  InsufficientPasswordHashAlgorithm() {
    exists(CryptographicOperation application |
      application.getAlgorithm().isWeak() or
      not application.getAlgorithm() instanceof PasswordHashingAlgorithm |
      this.asExpr() = application.getInput()
    )
  }
}
