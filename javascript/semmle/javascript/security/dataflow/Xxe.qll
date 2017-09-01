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
 * Provides a taint tracking configuration for reasoning about XML External Entity (XXE)
 * vulnerabilities.
 */

import javascript
import DOM

/**
 * A data flow source for XXE vulnerabilities.
 */
abstract class XxeSource extends DataFlowNode { }

/**
 * A data flow sink for XXE vulnerabilities.
 */
abstract class XxeSink extends DataFlowNode { }

/**
 * A sanitizer for XXE vulnerabilities.
 */
abstract class XxeSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about XXE vulnerabilities.
 */
class XxeTrackingConfig extends TaintTracking::Configuration {
  XxeTrackingConfig() {
    this = "Xxe"
  }

  override predicate isSource(DataFlowNode source) {
    source instanceof XxeSource or
    source instanceof RemoteFlowSource or
    isLocation(source)
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof XxeSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    node instanceof XxeSanitizer
  }
}

/**
 * A call to an XML parser that performs external entity expansion, viewed
 * as a data flow sink for XXE vulnerabilities.
 */
class XmlParsingWithExternalEntityResolution extends XxeSink {
  XmlParsingWithExternalEntityResolution() {
    exists (XML::ParserInvocation parse | this = parse.getSourceArgument() |
      parse.resolvesEntities(XML::ExternalEntity(_))
      or
      parse.resolvesEntities(XML::ParameterEntity(true)) and
      parse.resolvesEntities(XML::InternalEntity())
    )
  }
}
