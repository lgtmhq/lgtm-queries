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
 * Provides classes and predicates for working with Javadoc documentation.
 */

import semmle.code.Location
import Element

/** A Javadoc parent is an element whose child can be some Javadoc documentation. */
class JavadocParent extends @javadocParent, Top {
  /** A documentation element attached to this parent. */
  JavadocElement getAChild() { result.getParent() = this }

  /** The child documentation element at the specified (zero-based) position. */
  JavadocElement getChild(int index) {
    result = this.getAChild() and result.getIndex() = index
  }

  /** The number of documentation elements attached to this parent. */
  int getNumChild() {
    result = count(getAChild())
  }

  /** A documentation element with the specified Javadoc tag name. */
  JavadocTag getATag(string name) {
    result = this.getAChild() and result.getTagName() = name
  }

  /*abstract*/ string toString() { result = "Javadoc" }
}

/** A Javadoc comment. */
class Javadoc extends JavadocParent, @javadoc {
 
  /** The number of lines in this Javadoc comment. */
  int getNumberOfLines() {
    result = this.getLocation().getNumberOfCommentLines()
  }

  /** The value of the `@version` tag, if any. */
  string getVersion() {
    result = this.getATag("@version").getChild(0).toString()
  }

  /** The value of the `@author` tag, if any. */
  string getAuthor() {
    result = this.getATag("@author").getChild(0).toString()
  }

  string toString() {
    result = toStringPrefix() + getChild(0) + toStringPostfix()
  }

  private string toStringPrefix() {
    if isEolComment(this) then
      result = "//"
    else (
      if isNormalComment(this) then
        result = "/* "
      else
        result = "/** "
    )
  }

  private string toStringPostfix() {
    if isEolComment(this) then
      result = ""
    else (
      if strictcount(getAChild()) = 1 then
        result = " */"
      else
        result = " ... */"
    )
  }

  /** The Java code element that is commented by this piece of Javadoc. */
  Documentable getCommentedElement() { result.getJavadoc() = this }
}

/** A documentable element that can have an attached Javadoc comment. */
class Documentable extends Element, @member {
  /** The Javadoc comment attached to this element. */
  Javadoc getJavadoc() { hasJavadoc(this,result) and not isNormalComment(result) }

  /** The name of the author(s) of this element, if any. */
  string getAuthor() {
   result = this.getJavadoc().getAuthor()
  }
}

/** A common super-class for Javadoc elements, which may be either tags or text. */
abstract class JavadocElement extends @javadocElement, Top {
  /** The parent of this Javadoc element. */
  JavadocParent getParent() {
    javadocTag(this,_,result,_) or javadocText(this,_,result,_)
  }

  /** The index of this child element relative to its parent. */
  int getIndex() {
    javadocTag(this,_,_,result) or javadocText(this,_,_,result)
  }

  /** A printable representation of this Javadoc element. */
  /*abstract*/ string toString() { result = "Javadoc element" }
  
  /** The line of text associated with this Javadoc element. */
  abstract string getText();
}

/** A Javadoc tag. */
class JavadocTag extends JavadocElement, JavadocParent, @javadocTag {
  /** The name of this Javadoc tag. */
  string getTagName() { javadocTag(this,result,_,_) }

  /** A printable representation of this Javadoc tag. */
  string toString() { result = this.getTagName() }
  
  /** The text associated with this Javadoc tag. */
  string getText() { result = this.getChild(0).toString() }
}

/** A Javadoc `@param` tag. */
class ParamTag extends JavadocTag {
  ParamTag() { this.getTagName() = "@param" }

  /** The name of the parameter. */
  string getParamName() { result = this.getChild(0).toString() }

  /** The documentation for the parameter. */
  string getText() { result = this.getChild(1).toString() }
}

/** A Javadoc `@throws` or `@exception` tag. */
class ThrowsTag extends JavadocTag {
  ThrowsTag() { this.getTagName() = "@throws" or this.getTagName() = "@exception" }

  /** The name of the exception. */
  string getExceptionName() { result = this.getChild(0).toString() }

  /** The documentation for the exception. */
  string getText() { result = this.getChild(1).toString() }
}

/** A Javadoc `@see` tag. */
class SeeTag extends JavadocTag {
  SeeTag() { getTagName() = "@see" }

  /** The name of the entity referred to. */
  string getReference() { result = getChild(0).toString() }
}

/** A Javadoc `@author` tag. */
class AuthorTag extends JavadocTag {
  AuthorTag() { this.getTagName() = "@author" }

  /** The name of the author. */
  string getAuthorName() { result = this.getChild(0).toString() }
}

/** A piece of Javadoc text. */
class JavadocText extends JavadocElement, @javadocText {

  /** The Javadoc comment that contains this piece of text. */
  Javadoc getJavadoc() { result.getAChild+() = this }

  /** The text itself. */
  string getText() { javadocText(this,result,_,_) }

  /** A printable representation of this Javadoc element. */
  string toString() { result = this.getText() }
}
