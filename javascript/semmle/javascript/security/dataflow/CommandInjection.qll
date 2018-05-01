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
 * Provides a taint tracking configuration for reasoning about command-injection
 * vulnerabilities (CWE-078).
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources

module CommandInjection {
  /**
   * A data flow source for command-injection vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for command-injection vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for command-injection vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint-tracking configuration for reasoning about command-injection vulnerabilities.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() {
      this = "CommandInjection" and
      exists(Source s) and exists(Sink s)
    }

    override predicate isSource(DataFlow::Node source) {
      source instanceof Source
    }

    override predicate isSink(DataFlow::Node sink) {
      sink instanceof Sink
    }

    override predicate isSanitizer(DataFlow::Node node) {
      node instanceof Sanitizer
    }
  }

  /** A source of remote user input, considered as a flow source for command injection. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * A command argument to a function that initiates an operating system command.
  */
  class SystemCommandExecutionSink extends Sink, DataFlow::ValueNode {
    SystemCommandExecutionSink() {
      this = any(SystemCommandExecution sys).getACommandArgument()
    }
  }
}

/** DEPRECATED: Use `CommandInjection::Source` instead. */
deprecated class CommandInjectionSource = CommandInjection::Source;

/** DEPRECATED: Use `CommandInjection::Sink` instead. */
deprecated class CommandInjectionSink = CommandInjection::Sink;

/** DEPRECATED: Use `CommandInjection::Sanitizer` instead. */
deprecated class CommandInjectionSanitizer = CommandInjection::Sanitizer;

/** DEPRECATED: Use `CommandInjection::Configuration` instead. */
deprecated class CommandInjectionTrackingConfig = CommandInjection::Configuration;
