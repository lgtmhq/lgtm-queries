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

/** Provides classes for working with HTML documents. */

import Locations

/**
 * An HTML file, that is, a file with extension
 * `html`, `htm`, `xhtml` or `xhtm` (regardless of case).
 */
class HTMLFile extends File {
  HTMLFile() {
    getExtension().regexpMatch("(?i)x?html?")
  }
}

/**
 * An HTML element like `<a href="semmle.com">Semmle</a>`.
 */
class HTMLElement extends Locatable, @xmlelement {
  HTMLElement() {
    exists (HTMLFile f | xmlElements(this, _, _, _, f))
  }

  override Location getLocation() {
    xmllocations(this, result)
  }

  /**
   * Gets the name of this HTML element.
   *
   * For example, the name of `<br>` is `br`.
   */
  string getName() {
    xmlElements(this, result, _, _, _)
  }

  /**
   * Gets the parent element of this element, if any.
   */
  HTMLElement getParent() {
    xmlElements(this, _, result, _, _)
  }

  /**
   * Holds if this is a toplevel element, that is, if it does not have a parent element.
   */
  predicate isTopLevel() {
    not exists(getParent())
  }

  /**
   * Gets the `i`th child element (0-based) of this element.
   */
  HTMLElement getChild(int i) {
    xmlElements(result, _, this, i, _)
  }

  /**
   * Gets a child element of this element.
   */
  HTMLElement getChild() {
    result = getChild(_)
  }

  /**
   * Gets the `i`th attribute (0-based) of this element.
   */
  HTMLAttribute getAttribute(int i) {
    xmlAttrs(result, this, _, _, i, _)
  }

  /**
   * Gets an attribute of this element.
   */
  HTMLAttribute getAnAttribute() {
    result = getAttribute(_)
  }

  /**
   * Gets an attribute of this element that has the given name.
   */
  HTMLAttribute getAttributeByName(string name) {
    result = getAnAttribute() and
    result.getName() = name
  }

  override string toString() {
    result = "<" + getName() + ">...</>"
  }
}

/**
 * An attribute of an HTML element.
 *
 * For example, the element `<a href ="semmle.com" target=_blank>Semmle</a>`
 * has two attributes: `href ="semmle.com"` and `target=_blank`.
 */
class HTMLAttribute extends Locatable, @xmlattribute {
  HTMLAttribute() {
    exists (HTMLFile f | xmlAttrs(this, _, _, _, _, f))
  }

  override Location getLocation() {
    xmllocations(this, result)
  }

  /**
   * Gets the element to which this attribute belongs.
   */
  HTMLElement getElement() {
    xmlAttrs(this, result, _, _, _, _)
  }

  /**
   * Gets the name of this attribute.
   */
  string getName() {
    xmlAttrs(this, _, result, _, _, _)
  }

  /**
   * Gets the value of this attribute.
   *
   * For attributes without an explicitly specified value, the
   * result is the empty string.
   */
  string getValue() {
    xmlAttrs(this, _, _, result, _ ,_)
  }

  override string toString() {
    result = getName() + "=" + getValue()
  }
}

/**
 * An HTML `<script>` tag.
 */
class HTMLScriptTag extends HTMLElement {
  HTMLScriptTag() {
    getName() = "script"
  }

  /**
   * Gets the absolute file system path the value of the `src` attribute
   * of this script tag resolves to, if any.
   *
   * Path resolution is currently limited to absolute `file://` URLs,
   * absolute file system paths starting with `/`, and paths relative
   * to the enclosing HTML file. Base URLs are not taken into account.
   */
  string resolveSourcePath() {
    exists (string path | path = getSourcePath() |
      result = path.regexpCapture("file://(/.*)", 1)
      or
      not path.regexpMatch("(\\w+:)?//.*") and
      result = getSourcePath().(ScriptSrcPath).resolve(getSearchRoot()).toString()
    )
  }

  /**
   * Gets the value of the `src` attribute.
   */
  string getSourcePath() {
    result = getAttributeByName("src").getValue()
  }

  /**
   * Gets the folder relative to which the `src` attribute is resolved.
   */
  Folder getSearchRoot() {
    if getSourcePath().matches("/%") then
      result.getName() = ""
    else
      result = getFile().getParent()
  }

  /**
   * Gets the script referred to by the `src` attribute,
   * if it can be determined.
   */
  Script resolveSource() {
    result.getFile().getPath() = resolveSourcePath()
  }
}

/**
 * Holds if there is an HTML `<script>` tag with the given `src`
 * such that the script is resolved relative to `root`.
 */
private predicate scriptSrc(string src, Folder root) {
  exists (HTMLScriptTag script |
    src = script.getSourcePath() and
    root = script.getSearchRoot()
  )
}

/**
 * A path string arising from the `src` attribute of a `script` tag.
 */
private class ScriptSrcPath extends PathString {
  ScriptSrcPath() {
    scriptSrc(this, _)
  }

  override Folder getARootFolder() {
    scriptSrc(this, result)
  }
}