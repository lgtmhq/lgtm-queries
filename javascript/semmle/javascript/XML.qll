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
 * Provides classes for working with XML parser APIs.
 */

import javascript as js

module XML {
  /**
   * A representation of the different kinds of entities in XML.
   */
  newtype EntityKind =
    /** Internal general entity. */
    InternalEntity()
    or
    /** External general entity, either parsed or unparsed. */
    ExternalEntity(boolean parsed) { parsed = true or parsed = false }
    or
    /** Parameter entity, either internal or external. */
    ParameterEntity(boolean external) { external = true or external = false }

  /**
   * A call to an XML parsing function.
   */
  abstract class ParserInvocation extends js::InvokeExpr {
    /** Gets an argument to this call that is parsed as XML. */
    abstract js::DataFlowNode getSourceArgument();

    /** Holds if this call to the XML parser resolves entities of the given `kind`. */
    abstract predicate resolvesEntities(EntityKind kind);
  }

  /**
   * An invocation of `libxmljs.parseXml` or `libxmljs.parseXmlString`.
   */
  class LibXmlJsParserInvocation extends ParserInvocation {
    LibXmlJsParserInvocation() {
      exists (js::ModuleInstance libxmljs, string m |
        libxmljs.getPath() = "libxmljs" and
        this = libxmljs.getAMethodCall(m) and
        m.matches("parseXml%")
      )
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(EntityKind kind) {
      // internal entities are always resolved
      kind = InternalEntity()
      or
      // other entities are only resolved if the configuration option `noent` is set to `true`
      exists (js::PropWriteNode pwn |
        getArgument(1).(js::DataFlowNode).getALocalSource() = pwn.getBase() and
        pwn.getPropertyName() = "noent" and
        pwn.getRhs().getALocalSource().(js::BooleanLiteral).getValue() = "true"
      )
    }
  }

  /**
   * An invocation of `libxmljs.SaxParser.parseString`.
   */
  class LibXmlJsSaxParserInvocation extends ParserInvocation {
    LibXmlJsSaxParserInvocation() {
      exists (js::DataFlowNode libxmljs, js::NewExpr saxParser, js::DataFlowNode recv |
        libxmljs.getALocalSource().(js::ModuleInstance).getPath() = "libxmljs" and
        saxParser.getCallee().(js::PropAccess).accesses(libxmljs, "SaxParser") and
        recv.getALocalSource() = saxParser and
        this.(js::MethodCallExpr).calls(recv, "parseString")
      )
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(EntityKind kind) {
      // entities are resolved by default
      any()
    }
  }

  /**
   * An invocation of `libxmljs.SaxPushParser.push`.
   */
  class LibXmlJsSaxPushParserInvocation extends ParserInvocation {
    LibXmlJsSaxPushParserInvocation() {
      exists (js::DataFlowNode libxmljs, js::NewExpr saxPushParser, js::DataFlowNode recv |
        libxmljs.getALocalSource().(js::ModuleInstance).getPath() = "libxmljs" and
        saxPushParser.getCallee().(js::PropAccess).accesses(libxmljs, "SaxPushParser") and
        recv.getALocalSource() = saxPushParser and
        this.(js::MethodCallExpr).calls(recv, "push")
      )
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(EntityKind kind) {
      // entities are resolved by default
      any()
    }
  }

  /**
   * An invocation of `expat.Parser.parse` or `expat.Parser.write`.
   */
  class ExpatParserInvocation extends ParserInvocation {
    ExpatParserInvocation() {
      exists (js::DataFlowNode expat, js::NewExpr parser, js::DataFlowNode recv, string m |
        expat.getALocalSource().(js::ModuleInstance).getPath() = "node-expat" and
        parser.getCallee().(js::PropAccess).accesses(expat, "Parser") and
        recv.getALocalSource() = parser and
        this.(js::MethodCallExpr).calls(recv, m) and
        (m = "parse" or m = "write")
      )
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(EntityKind kind) {
      // only internal entities are resolved by default
      kind = InternalEntity()
    }
  }

  /**
   * An invocation of `DOMParser.parseFromString`.
   */
  private class DOMParserXmlParserInvocation extends XML::ParserInvocation {
    DOMParserXmlParserInvocation() {
      exists (js::NewExpr newDOMParser, js::DataFlowNode recv |
        newDOMParser.getCallee().accessesGlobal("DOMParser") and
        recv.getALocalSource() = newDOMParser and
        this.(js::MethodCallExpr).calls(recv, "parseFromString") and
        // type contains the string `xml`, that is, it's not `text/html`
        getArgument(1).(js::StringLiteral).getValue().matches("%xml%")
      )
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(XML::EntityKind kind) {
      kind = InternalEntity()
    }
  }

  /**
   * An invocation of `loadXML` on an IE legacy XML DOM or MSXML object.
   */
  private class IELegacyXmlParserInvocation extends XML::ParserInvocation {
    IELegacyXmlParserInvocation() {
      exists (js::NewExpr activeXObject, string activeXType, js::DataFlowNode recv |
        activeXObject.getCallee().accessesGlobal("ActiveXObject") and
        activeXType = activeXObject.getArgument(0).(js::StringLiteral).getValue() and
        activeXType.regexpMatch("Microsoft\\.XMLDOM|Msxml.*\\.DOMDocument.*") and
        recv.getALocalSource() = activeXObject and
        this.(js::MethodCallExpr).calls(recv, "loadXML")
      )
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(XML::EntityKind kind) {
      any()
    }
  }

  /**
   * An invocation of `goog.dom.xml.loadXml`.
   */
  private class GoogDomXmlParserInvocation extends XML::ParserInvocation {
    GoogDomXmlParserInvocation() {
      this.getCallee().(js::PropAccess).getQualifiedName() = "goog.dom.xml.loadXml"
    }

    override js::DataFlowNode getSourceArgument() {
      result = getArgument(0)
    }

    override predicate resolvesEntities(XML::EntityKind kind) {
      kind = InternalEntity()
    }
  }
}
