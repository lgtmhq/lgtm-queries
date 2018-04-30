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

module XmlBomb {
  /**
   * A data flow source for XML-bomb vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for XML-bomb vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for XML-bomb vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint-tracking configuration for reasoning about XML-bomb vulnerabilities.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() {
      this = "XmlBomb" and
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

  /** A source of remote user input, considered as a flow source for XML bomb vulnerabilities. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * An access to `document.location`, considered as a flow source for XML bomb vulnerabilities.
   */
  class LocationAsSource extends Source, DataFlow::ValueNode {
    LocationAsSource() {
      isLocation(astNode)
    }
  }

  /**
   * A call to an XML parser that performs internal entity expansion, viewed
   * as a data flow sink for XML-bomb vulnerabilities.
   */
  class XmlParsingWithEntityResolution extends Sink, DataFlow::ValueNode {
    XmlParsingWithEntityResolution() {
      exists (XML::ParserInvocation parse | astNode = parse.getSourceArgument() |
        parse.resolvesEntities(XML::InternalEntity())
      )
    }
  }
}

/** DEPRECATED: Use `XmlBomb::Source` instead. */
deprecated class XmlBombSource = XmlBomb::Source;

/** DEPRECATED: Use `XmlBomb::Sink` instead. */
deprecated class XmlBombSink = XmlBomb::Sink;

/** DEPRECATED: Use `XmlBomb::Sanitizer` instead. */
deprecated class XmlBombSanitizer = XmlBomb::Sanitizer;

/** DEPRECATED: Use `XmlBomb::Configuration` instead. */
deprecated class XmlBomTrackingConfig = XmlBomb::Configuration;
