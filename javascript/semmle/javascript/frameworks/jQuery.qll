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
 * Provides classes for working with jQuery code.
 */

import javascript

/**
 * Holds if `nd` may refer to the jQuery `$` function.
 */
private predicate isJQueryRef(DataFlowNode nd) {
  exists (Expr src | src = nd.getALocalSource() |
   // either a reference to a global variable `$` or `jQuery`
   src.accessesGlobal("$") or
   src.accessesGlobal("jQuery") or
   // or imported from a module named `jquery`
   src.(ModuleInstance).getPath() = "jquery"
  )
}

/**
 * A node that may refer to a jQuery object.
 *
 * Note that this class is an over-approximation: `nd instanceof JQueryObject)`
 * may hold for nodes `nd` that cannot, in fact, refer to a jQuery object.
 */
abstract class JQueryObject extends DataFlowNode {

}

/**
 * A jQuery object created from a jQuery method.
 */
private class OrdinaryJQueryObject extends JQueryObject {
  OrdinaryJQueryObject() {
    exists (JQueryMethodCall jq | jq = this.getALocalSource() |
      // `jQuery.val()` does _not_ return a jQuery object
      jq.getMethodName() != "val"
    )
  }
}

/**
 * A (possibly chained) call to a jQuery method.
 */
class JQueryMethodCall extends CallExpr {
  string name;

  JQueryMethodCall() {
    isJQueryRef(getCallee()) and name = "$"
    or
    exists (MethodCallExpr mce | mce = this and name = mce.getMethodName() |
      // initial call
      isJQueryRef(mce.getReceiver()) or
      // chained call
      mce.getReceiver() instanceof JQueryObject
    )
  }

  /**
   * Gets the name of the jQuery method this call invokes.
   */
  string getMethodName() {
    result = name
  }

  /**
   * Holds if this call interprets its arguments as HTML.
   */
  predicate interpretsArgumentsAsHtml() {
      name = "addClass" or
      name = "after" or
      name = "append" or
      name = "appendTo" or
      name = "before" or
      name = "html" or
      name = "insertAfter" or
      name = "insertBefore" or
      name = "parseHTML" or
      name = "prepend" or
      name = "prependTo" or
      name = "prop" or
      name = "replaceWith" or
      name = "wrap" or
      name = "wrapAll" or
      name = "wrapInner"
  }
}

/**
 * A call to `jQuery.parseXML`.
 */
private class JQueryParseXmlCall extends XML::ParserInvocation {
  JQueryParseXmlCall() {
    this.(JQueryMethodCall).getMethodName() = "parseXML"
  }

  override DataFlowNode getSourceArgument() {
    result = getArgument(0)
  }

  override predicate resolvesEntities(XML::EntityKind kind) {
    kind = XML::InternalEntity()
  }
}

/**
 * A call to `$(...)` that constructs a wrapped DOM element, such as `$("<div/>")`.
 */
private class JQueryDomElementDefinition extends DOM::ElementDefinition, @callexpr {
  string tagName;
  CallExpr call;

  JQueryDomElementDefinition() {
    this = call and
    isJQueryRef(call.getCallee()) and
    exists (string s | s = call.getArgument(0).(Expr).getStringValue() |
      // match an opening angle bracket followed by a tag name, followed by arbitrary
      // text and a closing angle bracket, potentially with whitespace in between
      tagName = s.regexpCapture("\\s*<\\s*(\\w+)\\b[^>]*>\\s*", 1).toLowerCase()
    )
  }

  override string getName() {
    result = tagName
  }

  /**
   * Gets a data flow node specifying the attributes of the constructed DOM element.
   *
   * For example, in `$("<a/>", { href: "https://semmle.com" })` the second argument
   * specifies the attributes of the new `<a>` element.
   */
  DataFlowNode getAttributes() {
    result = this.(CallExpr).getArgument(1).(DataFlowNode).getALocalSource()
  }

  override DOM::ElementDefinition getParent() { none() }
}

/**
 * An attribute defined using jQuery APIs.
 */
private abstract class JQueryAttributeDefinition extends DOM::AttributeDefinition {
}

/**
 * An attribute definition supplied when constructing a DOM element using `$(...)`.
 *
 * For example, in `$("<script/>", { src: mySource })`, the property `src : mySource`
 * defines an attribute of the newly constructed `<script>` element.
 */
private class JQueryAttributeDefinitionInElement extends JQueryAttributeDefinition {
  JQueryDomElementDefinition elt;

  JQueryAttributeDefinitionInElement() {
    this.(PropWriteNode).getBase().getALocalSource() = elt.getAttributes()
  }

  override string getName() {
    result = this.(PropWriteNode).getPropertyName()
  }

  override DataFlowNode getValueNode() {
    result = this.(PropWriteNode).getRhs()
  }

  override DOM::ElementDefinition getElement() {
    result = elt
  }
}

/**
 * An attribute definition using `elt.attr(name, value)` or `elt.prop(name, value)`
 * where `elt` is a wrapped set.
 */
private class JQueryAttr2Call extends JQueryAttributeDefinition, @callexpr {
  JQueryDomElementDefinition elt;

  JQueryAttr2Call() {
    exists (MethodCallExpr mce | this = mce |
      mce.getReceiver().(DOM::Element).getDefinition() = elt and
      (mce.getMethodName() = "attr" or mce.getMethodName() = "prop") and
      mce.getNumArgument() = 2
    )
  }

  override string getName() {
    result = this.(CallExpr).getArgument(0).getStringValue()
  }

  override DataFlowNode getValueNode() {
    result = this.(CallExpr).getArgument(1)
  }

  override DOM::ElementDefinition getElement() {
    result = elt
  }
}

/**
 * Holds if `mce` is a call to `elt.attr(attributes)` or `elt.prop(attributes)`.
 */
private predicate bulkAttributeInit(MethodCallExpr mce, JQueryDomElementDefinition elt,
                                    DataFlowNode attributes) {
  mce.getReceiver().(DOM::Element).getDefinition() = elt and
  (mce.getMethodName() = "attr" or mce.getMethodName() = "prop") and
  mce.getNumArgument() = 1 and
  attributes = mce.getArgument(0).(DataFlowNode).getALocalSource()
}

/**
 * An attribute definition using `elt.attr(attributes)` or `elt.prop(attributes)`
 * where `elt` is a wrapped set and `attributes` is an object of attribute-value pairs
 * to set.
 */
private class JQueryAttrCall extends JQueryAttributeDefinition, @callexpr {
  JQueryDomElementDefinition elt;
  PropWriteNode pwn;

  JQueryAttrCall() {
    exists (DataFlowNode attributes |
      bulkAttributeInit(this, elt, attributes) and
      pwn.getBase().getALocalSource() = attributes
    )
  }

  override string getName() {
    result = pwn.getPropertyName()
  }

  override DataFlowNode getValueNode() {
    result = pwn.getRhs()
  }

  override DOM::ElementDefinition getElement() {
    result = elt
  }
}

/**
 * An attribute definition using `jQuery.attr(elt, name, value)` or `jQuery.prop(elt, name, value)`
 * where `elt` is a wrapped set or a plain DOM element.
 */
private class JQueryAttr3Call extends JQueryAttributeDefinition, @callexpr {
  DOM::ElementDefinition elt;

  JQueryAttr3Call() {
    exists (MethodCallExpr mce | this = mce |
      isJQueryRef(mce.getReceiver()) and
      mce.getArgument(0).(DOM::Element).getDefinition() = elt and
      (mce.getMethodName() = "attr" or mce.getMethodName() = "prop") and
      mce.getNumArgument() = 3
    )
  }

  override string getName() {
    result = this.(CallExpr).getArgument(1).getStringValue()
  }

  override DataFlowNode getValueNode() {
    result = this.(CallExpr).getArgument(2)
  }

  override DOM::ElementDefinition getElement() {
    result = elt
  }
}

/**
 * A DOM element returned from a chained jQuery call.
 *
 * For example, the call `$("<script/>").attr("src", mySource)` returns
 * the DOM element constructed by `$("<script/>")`.
 */
private class JQueryChainedElement extends DOM::Element {
  DOM::Element inner;

  JQueryChainedElement() {
    exists (JQueryMethodCall jqmc | this = jqmc |
      jqmc.(MethodCallExpr).getReceiver() = inner and
      this instanceof JQueryObject and
      defn = inner.getDefinition()
    )
  }
}
