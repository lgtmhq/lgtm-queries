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
 * Provides a taint-tracking configuration for reasoning about unsafe deserialization.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources

/**
 * A data flow source for unsafe deserialization vulnerabilities.
 */
abstract class UnsafeDeserializationSource extends DataFlow::Node { }

/**
 * A data flow sink for unsafe deserialization vulnerabilities.
 */
abstract class UnsafeDeserializationSink extends DataFlow::Node { }

/**
 * A sanitizer for unsafe deserialization vulnerabilities.
 */
abstract class UnsafeDeserializationSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about unsafe deserialization.
 */
class UnsafeDeserializationTrackingConfig extends TaintTracking::Configuration {
  UnsafeDeserializationTrackingConfig() { this = "UnsafeDeserializationTrackingConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof UnsafeDeserializationSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof UnsafeDeserializationSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof UnsafeDeserializationSanitizer
  }
}

/**
 * An expression passed to one of the unsafe load functions of the `js-yaml` package.
 */
class JsYamlUnsafeLoad extends UnsafeDeserializationSink {
  JsYamlUnsafeLoad() {
    exists (ModuleInstance mi | mi.getPath() = "js-yaml" |
      // the first argument to a call to `load` or `loadAll`
      exists (string n | n = "load" or n = "loadAll" |
        this.asExpr() = mi.getAMethodCall(n).getArgument(0)
      )
      or
      // the first argument to a call to `safeLoad` or `safeLoadAll` where
      // the schema is specified to be `DEFAULT_FULL_SCHEMA`
      exists (string n, CallExpr c, DataFlowNode fullSchema | n = "safeLoad" or n = "safeLoadAll" |
        c = mi.getAMethodCall(n) and
        this.asExpr() = c.getArgument(0) and
        c.hasOptionArgument(c.getNumArgument()-1, "schema", fullSchema) and
        fullSchema.getALocalSource() = mi.getAPropertyRead("DEFAULT_FULL_SCHEMA")
      )
    )
  }
}
