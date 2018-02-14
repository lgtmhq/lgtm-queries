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
 * Provides a taint tracking configuration for reasoning about XML-bomb
 * vulnerabilities.
 */

import javascript
import semmle.javascript.security.dataflow.DOM

/**
 * A data flow source for XML-bomb vulnerabilities.
 */
abstract class XmlBombSource extends DataFlow::Node { }

/**
 * A data flow sink for XML-bomb vulnerabilities.
 */
abstract class XmlBombSink extends DataFlow::Node { }

/**
 * A sanitizer for XML-bomb vulnerabilities.
 */
abstract class XmlBombSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about XML-bomb vulnerabilities.
 */
class XmlBombTrackingConfig extends TaintTracking::Configuration {
  XmlBombTrackingConfig() {
    this = "XmlBomb"
  }

  override predicate isSource(DataFlow::Node source) {
    source instanceof XmlBombSource or
    source instanceof RemoteFlowSource or
    isLocation(source.asExpr())
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof XmlBombSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof XmlBombSanitizer
  }
}

/**
 * A call to an XML parser that performs internal entity expansion, viewed
 * as a data flow sink for XML-bomb vulnerabilities.
 */
class XmlParsingWithEntityResolution extends XmlBombSink, DataFlow::ValueNode {
  XmlParsingWithEntityResolution() {
    exists (XML::ParserInvocation parse | astNode = parse.getSourceArgument() |
      parse.resolvesEntities(XML::InternalEntity())
    )
  }
}
