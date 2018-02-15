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
 * Provides a taint tracking configuration for reasoning about XML External Entity (XXE)
 * vulnerabilities.
 */

import javascript
import semmle.javascript.security.dataflow.DOM

/**
 * A data flow source for XXE vulnerabilities.
 */
abstract class XxeSource extends DataFlow::Node { }

/**
 * A data flow sink for XXE vulnerabilities.
 */
abstract class XxeSink extends DataFlow::Node { }

/**
 * A sanitizer for XXE vulnerabilities.
 */
abstract class XxeSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about XXE vulnerabilities.
 */
class XxeTrackingConfig extends TaintTracking::Configuration {
  XxeTrackingConfig() {
    this = "Xxe"
  }

  override predicate isSource(DataFlow::Node source) {
    source instanceof XxeSource or
    source instanceof RemoteFlowSource or
    isLocation(source.asExpr())
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof XxeSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof XxeSanitizer
  }
}

/**
 * A call to an XML parser that performs external entity expansion, viewed
 * as a data flow sink for XXE vulnerabilities.
 */
class XmlParsingWithExternalEntityResolution extends XxeSink, DataFlow::ValueNode {
  XmlParsingWithExternalEntityResolution() {
    exists (XML::ParserInvocation parse | astNode = parse.getSourceArgument() |
      parse.resolvesEntities(XML::ExternalEntity(_))
      or
      parse.resolvesEntities(XML::ParameterEntity(true)) and
      parse.resolvesEntities(XML::InternalEntity())
    )
  }
}
