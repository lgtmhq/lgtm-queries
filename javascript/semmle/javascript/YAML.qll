// Copyright 2016 Semmle Ltd.
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

import Locations

/**
 * A node in the AST representation of a YAML file; this may either be
 * a YAML value (such as a scalar or a collection) or an alias node
 * referring to some other YAML value.
 */
class YAMLNode extends @yaml_node, Locatable {
  /**
   * Get the parent node of this node, which is always a collection.
   */
  YAMLCollection getParentNode() {
    yaml(this, _, result, _, _, _)
  }

  /**
   * Get the i-th child node of this node.
   *
   * <p>
   * Note: The index of a child node relative to its parent is considered
   * an implementation detail and may change between versions of the extractor.
   * </p>
   */
  YAMLNode getChildNode(int i) {
    yaml(result, _, this, i, _, _)
  }

  /**
   * Get some child node of this node.
   */
  YAMLNode getAChildNode() {
    result = getChildNode(_)
  }

  /**
   * Determine how many child nodes this node has.
   */
  int getNumChild() {
    result = count(getAChildNode())
  }

  /**
   * Get the i-th child of this node, as a YAML value.
   */
  YAMLValue getChild(int i) {
    result = getChildNode(i).eval()
  }

  /**
   * Get some child of this node, as a YAML value.
   */
  YAMLValue getAChild() {
    result = getChild(_)
  }

  /**
   * Get the tag of this node.
   */
  string getTag() {
    yaml(this, _, _, _, result, _)
  }

  /**
   * Is this node tagged with a standard type tag of the form
   * <code>tag:yaml.org,2002:&lt;t&gt;</code>?
   */
  predicate hasStandardTypeTag(string t) {
    t = getTag().regexpCapture("tag:yaml.org,2002:(.*)", 1)
  }

  string toString() {
    yaml(this, _, _, _, _, result)
  }

  /**
   * Get the anchor associated with this node, if any.
   */
  string getAnchor() {
    yaml_anchors(this, result)
  }

  /**
   * Get the toplevel document to which this node belongs.
   */
  YAMLDocument getDocument() {
    result = getParentNode*()
  }

  /**
   * Convert this node to a YAML value by resolving aliases and includes.
   */
  YAMLValue eval() {
    result = this
  }
}

/**
 * A YAML value; that is, either a scalar or a collection.
 */
abstract class YAMLValue extends YAMLNode {
}

/**
 * A YAML scalar.
 */
class YAMLScalar extends YAMLValue, @yaml_scalar_node {
  /**
   * Get the style of this scalar, which is one of the following:
   * <ul>
   * <li><code>""</code> (empty string): plain style</li>
   * <li><code>"\""</code> (double quote): double quoted style</li>
   * <li><code>"'"</code> (single quote): single quoted style</li>
   * <li><code>"&gt;"</code> (greater-than): folded style</li>
   * <li><code>"|"</code> (pipe): literal style</li>
   * </ul>
   */
  string getStyle() {
    exists (int s | yaml_scalars(this, s, _) |
      s =   0 and result = "" or
      s =  34 and result = "\"" or
      s =  39 and result = "'" or
      s =  62 and result = ">" or
      s = 124 and result = "|"
    )
  }

  /**
   * Get the value of this scalar, as a string.
   */
  string getValue() {
    yaml_scalars(this, _, result)
  }
}

/**
 * A YAML scalar representing an integer value.
 */
class YAMLInteger extends YAMLScalar {
  YAMLInteger() {
    hasStandardTypeTag("int")
  }

  /**
   * Get the value of this scalar, as an integer.
   */
  int getIntValue() {
    result = getValue().toInt()
  }
}

/**
 * A YAML scalar representing a floating point value.
 */
class YAMLFloat extends YAMLScalar {
  YAMLFloat() {
    hasStandardTypeTag("float")
  }

  /**
   * Get the value of this scalar, as a floating point number.
   */
  float getFloatValue() {
    result = getValue().toFloat()
  }
}

/**
 * A YAML scalar representing a time stamp.
 */
class YAMLTimestamp extends YAMLScalar {
  YAMLTimestamp() {
    hasStandardTypeTag("timestamp")
  }

  /**
   * Get the value of this scalar, as a date.
   */
  date getDateValue() {
    result = getValue().toDate()
  }
}

/**
 * A YAML scalar representing a Boolean value.
 */
class YAMLBool extends YAMLScalar {
  YAMLBool() {
    hasStandardTypeTag("bool")
  }

  /**
   * Get the value of this scalar, as a Boolean.
   */
  boolean getBoolValue() {
    if getValue() = "true" then
      result = true
    else
      result = false
  }
}

/**
 * A YAML scalar representing the null value.
 */
class YAMLNull extends YAMLScalar {
  YAMLNull() {
    hasStandardTypeTag("null")
  }
}

/**
 * A YAML scalar representing a string value.
 */
class YAMLString extends YAMLScalar {
  YAMLString() {
    hasStandardTypeTag("str")
  }
}

/**
 * A YAML scalar representing a merge key.
 */
class YAMLMergeKey extends YAMLScalar {
  YAMLMergeKey() {
    hasStandardTypeTag("merge")
  }
}

/**
 * A YAML scalar representing an <code>!include</code> directive.
 */
class YAMLInclude extends YAMLScalar {
  YAMLInclude() {
    getTag() = "!include"
  }

  YAMLValue eval() {
    exists (YAMLDocument targetDoc |
      targetDoc.getFile().getPath() = getTargetPath() and
      result = targetDoc.eval()
    )
  }

  /**
   * Get the absolute path of the file included by this directive.
   */
  private string getTargetPath() {
    exists (string path | path = getValue() |
      if path.charAt(0) = "/" then
        result = path
      else
        result = getDocument().getFile().getParent().getPath() + "/" + path
    )
  }
}

/**
 * A YAML collection, that is, either a mapping or a sequence.
 */
class YAMLCollection extends YAMLValue, @yaml_collection_node {
}

/**
 * A YAML mapping.
 */
class YAMLMapping extends YAMLCollection, @yaml_mapping_node {
  /**
   * Get the i-th key of this mapping.
   */
  YAMLNode getKeyNode(int i) {
    i >= 0 and
    exists (int j | i=j-1 and result = getChildNode(j)) 
  }

  /**
   * Get the i-th value of this mapping.
   */
  YAMLNode getValueNode(int i) {
    i >= 0 and
    exists (int j | i=-j-1 and result = getChildNode(j))
  }

  /**
   * Get the i-th key of this mapping, as a YAML value.
   */
  YAMLValue getKey(int i) {
    result = getKeyNode(i).eval()
  }

  /**
   * Get the i-th value of this mapping, as a YAML value.
   */
  YAMLValue getValue(int i) {
    result = getValueNode(i).eval()
  }

  /**
   * Bind key and value to a key-value pair in this mapping.
   */
  predicate maps(YAMLValue key, YAMLValue value) {
    exists (int i | key = getKey(i) and value = getValue(i)) or
    exists (YAMLMergeKey merge, YAMLMapping that | maps(merge, that) |
      that.maps(key, value)
    )
  }

  /**
   * Look up the value for a string-valued key.
   */
  YAMLValue lookup(string key) {
    exists (YAMLScalar s | s.getValue() = key |
      maps(s, result)
    )
  }
}

/**
 * A YAML sequence.
 */
class YAMLSequence extends YAMLCollection, @yaml_sequence_node {
  /**
   * Get the i-th element in this sequence.
   */
  YAMLNode getElementNode(int i) {
    result = getChildNode(i)
  }

  /**
   * Get the i-th element in this sequence, as a YAML value.
   */
  YAMLValue getElement(int i) {
    result = getElementNode(i).eval()
  }
}

/**
 * A YAML alias node referring to a target anchor.
 */
class YAMLAliasNode extends YAMLNode, @yaml_alias_node {
  YAMLValue eval() {
    result.getAnchor() = getTarget() and
    result.getDocument() = this.getDocument()
  }

  /**
   * Get the target anchor this alias refers to.
   */
  string getTarget() {
    yaml_aliases(this, result)
  }
}

/**
 * A YAML document.
 */
class YAMLDocument extends YAMLNode {
  YAMLDocument() {
    not exists(getParentNode())
  }
}

/**
 * An error message produced by the YAML parser while processing a YAML file.
 */
class YAMLParseError extends @yaml_error, Error {
  string getMessage() {
    yaml_errors(this, result)
  }

  string toString() {
    result = getMessage()
  }
}
