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
 * Provides a taint tracking configuration for reasoning about cleartext storage of sensitive information.
 */
import javascript
private import semmle.javascript.security.SensitiveActions

module CleartextStorage {
  /**
   * A data flow source for cleartext storage of sensitive information.
   */
  abstract class Source extends DataFlow::Node {
    /** Gets a string that describes the type of this data flow source. */
    abstract string describe();
  }

  /**
   * A data flow sink for cleartext storage of sensitive information.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for cleartext storage of sensitive information.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint tracking configuration for cleartext storage of sensitive information.
   *
   * This configuration identifies flows from `Source`s, which are sources of
   * sensitive data, to `Sink`s, which is an abstract class representing all
   * the places sensitive data may be stored in cleartext. Additional sources or sinks can be
   * added either by extending the relevant class, or by subclassing this configuration itself,
   * and amending the sources and sinks.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() {
      this = "ClearTextStorage" and
      exists(Source s) and exists(Sink s)
    }

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
      node instanceof Sanitizer
    }
  }

  /**
   * A sensitive expression, viewed as a data flow source for cleartext storage
   * of sensitive information.
   */
  class SensitiveExprSource extends Source, DataFlow::ValueNode {
    override SensitiveExpr astNode;

    override string describe() {
      result = astNode.describe()
    }
  }

  /** A call to any method whose name suggests that it encodes or encrypts the parameter. */
  class ProtectSanitizer extends Sanitizer, DataFlow::ValueNode {
    ProtectSanitizer() {
      exists(string s |
        astNode.(CallExpr).getCalleeName().regexpMatch("(?i).*" + s + ".*") |
        s = "protect" or s = "encode" or s = "encrypt"
      )
    }
  }

  /**
   * An expression set as a value on a cookie instance.
   */
  class CookieStorageSink extends Sink {
    CookieStorageSink() {
      exists (HTTP::CookieDefinition cookieDef |
        this.asExpr() = cookieDef.getValueArgument() or
        this.asExpr() = cookieDef.getHeaderArgument()
      )
    }
  }

  /**
   * An expression set as a value of localStorage or sessionStorage.
   */
  class WebStorageSink extends Sink {
    WebStorageSink() {
      this.asExpr() instanceof WebStorageWrite
    }
  }

  /**
   * An expression stored by AngularJS.
   */
  class AngularJSStorageSink extends Sink {
    AngularJSStorageSink() {
      any(AngularJS::AngularJSCall call).storesArgumentGlobally(this.asExpr())
    }
  }
}

/** DEPRECATED: Use `CleartextStorage::Source` instead. */
deprecated class CleartextStorageSource = CleartextStorage::Source;

/** DEPRECATED: Use `CleartextStorage::Sink` instead. */
deprecated class CleartextStorageSink = CleartextStorage::Sink;

/** DEPRECATED: Use `CleartextStorage::Sanitizer` instead. */
deprecated class CleartextStorageSanitizer = CleartextStorage::Sanitizer;

/** DEPRECATED: Use `CleartextStorage::Configuration` instead. */
deprecated class CleartextStorageDataFlowConfiguration = CleartextStorage::Configuration;
