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
 * Provides a taint-tracking configuration for reasoning about untrusted user input used to construct
 * regular expressions.
 */

import javascript

/**
 * A data flow source for untrusted user input used to construct regular expressions.
 */
abstract class RegExpInjectionSource extends DataFlowNode { }

/**
 * A data flow sink for untrusted user input used to construct regular expressions.
 */
abstract class RegExpInjectionSink extends DataFlowNode { }

/**
 * A sanitizer for untrusted user input used to construct regular expressions.
 */
abstract class RegExpInjectionSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for untrusted user input used to construct regular expressions.
 */
class RegExpInjectionTaintTrackingConfiguration extends TaintTracking::Configuration {
  RegExpInjectionTaintTrackingConfiguration() {
    this = "RegExpInjection"
  }

  override predicate isSource(DataFlowNode source) {
    source instanceof RemoteFlowSource or
    source instanceof RegExpInjectionSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof RegExpInjectionSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    super.isSanitizer(node) or
    node instanceof RegExpInjectionSanitizer
  }
}

/**
 * The first argument to an invocation of `RegExp` (with or without `new`).
 */
class RegExpObjectCreationSink extends RegExpInjectionSink {
  RegExpObjectCreationSink() {
    exists (InvokeExpr invk |
      invk.getCallee().accessesGlobal("RegExp") and
      this = invk.getArgument(0)
    )
  }
}

/**
 * A call to a function whose name suggests that it escapes regular
 * expression meta-characters.
 */
class RegExpSanitizationCall extends RegExpInjectionSanitizer, @callexpr {
  RegExpSanitizationCall() {
    exists (string calleeName, string sanitize, string regexp |
      calleeName = this.(CallExpr).getCalleeName() and
      sanitize = "(?:escape|saniti[sz]e)" and regexp = "regexp?" |
      calleeName.regexpMatch("(?i)(" + sanitize + regexp + ")" +
                                "|(" + regexp + sanitize + ")")
    )
  }
}
