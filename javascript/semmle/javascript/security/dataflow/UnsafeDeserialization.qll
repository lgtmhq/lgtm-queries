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

module UnsafeDeserialization {
  /**
   * A data flow source for unsafe deserialization vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for unsafe deserialization vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for unsafe deserialization vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint-tracking configuration for reasoning about unsafe deserialization.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() {
      this = "UnsafeDeserialization" and
      exists(Source s) and exists(Sink s)
    }

    override predicate isSource(DataFlow::Node source) {
      source instanceof Source
    }

    override predicate isSink(DataFlow::Node sink) {
      sink instanceof Sink
    }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      node instanceof Sanitizer
    }
  }

  /** A source of remote user input, considered as a flow source for unsafe deserialization. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * An expression passed to one of the unsafe load functions of the `js-yaml` package.
   */
  class JsYamlUnsafeLoad extends Sink {
    JsYamlUnsafeLoad() {
      exists (DataFlow::ModuleImportNode mi | mi.getPath() = "js-yaml" |
        // the first argument to a call to `load` or `loadAll`
        exists (string n | n = "load" or n = "loadAll" |
          this = mi.getAMemberCall(n).getArgument(0)
        )
        or
        // the first argument to a call to `safeLoad` or `safeLoadAll` where
        // the schema is specified to be `DEFAULT_FULL_SCHEMA`
        exists (string n, DataFlow::CallNode c, DataFlow::Node fullSchema |
          n = "safeLoad" or n = "safeLoadAll" |
          c = mi.getAMemberCall(n) and
          this = c.getArgument(0) and
          fullSchema = c.getOptionArgument(c.getNumArgument()-1, "schema") and
          mi.getAPropertyRead("DEFAULT_FULL_SCHEMA").flowsTo(fullSchema)
        )
      )
    }
  }
}

/** DEPRECATED: Use `UnsafeDeserialization::Source` instead. */
deprecated class UnsafeDeserializationSource = UnsafeDeserialization::Source;

/** DEPRECATED: Use `UnsafeDeserialization::Sink` instead. */
deprecated class UnsafeDeserializationSink = UnsafeDeserialization::Sink;

/** DEPRECATED: Use `UnsafeDeserialization::Sanitizer` instead. */
deprecated class UnsafeDeserializationSanitizer = UnsafeDeserialization::Sanitizer;

/** DEPRECATED: Use `UnsafeDeserialization::Configuration` instead. */
deprecated class UnsafeDeserializationTrackingConfig = UnsafeDeserialization::Configuration;
