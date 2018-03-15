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

/**
 * A data flow source for command-injection vulnerabilities.
 */
abstract class CommandInjectionSource extends DataFlow::Node { }

/**
 * A data flow sink for command-injection vulnerabilities.
 */
abstract class CommandInjectionSink extends DataFlow::Node { }

/**
 * A sanitizer for command-injection vulnerabilities.
 */
abstract class CommandInjectionSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about command-injection vulnerabilities.
 */
class CommandInjectionTrackingConfig extends TaintTracking::Configuration {
  CommandInjectionTrackingConfig() {
    this = "CommandInjection"
  }

  override predicate isSource(DataFlow::Node source) {
    source instanceof CommandInjectionSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof CommandInjectionSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    node instanceof CommandInjectionSanitizer
  }
}


/**
 * A command argument to a function that initiates an operating system command.
*/
class SystemCommandExecutionSink extends CommandInjectionSink, DataFlow::ValueNode {
  SystemCommandExecutionSink() {
    this = any(SystemCommandExecution sys).getACommandArgument()
  }
}
