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

/** --- XML ---

   Classes to represent XML files and their content.
*/

import semmle.python.Files

/** An XML element that has a location */
abstract class XMLLocatable extends @xmllocatable {
  /** source location for this element */
  Location getLocation() { xmllocations(this,result) }

  predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
    exists(File f, Location l | l = this.getLocation() |
      locations_default(l,f,startline,startcolumn,endline,endcolumn) and
      filepath = f.getName()
    )
  }
  
  abstract string toString();
}

/** An XMLParent is either an XMLElement or an XMLFile. 
 *   Both classes can contain other elements and are therefore parents. */
class XMLParent extends @xmlparent {
   /** get this parent's name; should be overridden in subclasses */
   /*abstract*/ string getName() { result = "parent" }

   /** get the file this XML parent comes from */
   XMLFile getFile() { result = this or xmlElements(this,_,_,_,result) }

	 /** get the child element with a given index of this parent */
	 XMLElement getChild(int index) { xmlElements(result, _, this, index, _) }

   /** get an element that is a child of this parent */
   XMLElement getAChild() { xmlElements(result,_,this,_,_) }

   /** get a comment that is a child of this parent */
   XMLComment getAComment() { xmlComments(result,_,this,_)   }

   /** get a characters sequence that is a child of this parent */
   XMLCharacters getACharactersSet() { xmlChars(result,_,this,_,_,_)  }
   
   /** gets the depth in the tree. Overridden in XMLElement. */
   int getDepth() { result = 0 }   

   /** computes the number of children*/
   int getNumberOfChildren() { 
       result = count(XMLElement e | xmlElements(e,_,this,_,_)) 
   }

   /** gets the number of places in the body of an XML parent where text occurs */
   int getNumberOfCharacterSets() { 
       result = count(int pos | xmlChars(_,_,this,pos,_,_)) 
   }

   /** appends the character sets from left to right separated by a space */
   string charsSetUpTo(int n) {
      (n = 0 and xmlChars(_,result,this,0,_,_)) or
      (n > 0 and exists(string chars| xmlChars(_,chars,this,n,_,_) and
                           result = this.charsSetUpTo(n-1) + " " + chars))
   }

   /** produces the string that puts all chars next to each other */
   string allCharactersString() {
      exists(int n | n = this.getNumberOfCharacterSets() and
        ((n=0 and result = "") or
         (n>0 and result = this.charsSetUpTo(n-1))))
   }

   /** printable representation */
   string toString()    { result = this.getName() }  

   /** set icon to represent this parent */
   string getIconPath() { result = "icons/tag.png" }

}

/** A parsed XML file */
class XMLFile extends XMLParent, File {
   XMLFile() {
     xmlEncoding(this,_)
   }
   string toString() { result = XMLParent.super.toString() }

   /** get this file's name */
   string getName()     { files(this,result,_,_,_) }

   /** get this file's path */
   string getPath()     { files(this,_,result,_,_) }

   /** get this file's folder */
   string getFolder()   { 
     result = this.getPath().substring(0, 
                               this.getPath().length()-this.getName().length())
   }

   /** get this file's enconding */
   string getEncoding() { xmlEncoding(this,result) }
   
   /** get the file this entity belongs to */
   XMLFile getFile()    { result = this }

   /** gives a top most element in an XML file*/
   XMLElement getARootElement() { result = this.getAChild() }
   
   /** gives a DTD*/
   XMLDTD getADTD() { xmlDTDs(result,_,_,_,this) }
	
   /** set icon to represent this file */
   string getIconPath() { result = "icons/file.png" }
}

/** A Document Type Declarations of an XML file */
class XMLDTD extends @xmldtd {
   /** get this DTD's root element name */
   string getRoot()      { xmlDTDs(this,result,_,_,_) }

   /** get this DTD's public ID */
   string getPublicId()  { xmlDTDs(this,_,result,_,_) }

   /** get this DTD's system ID */
   string getSystemId()  { xmlDTDs(this,_,_,result,_) }

   /** is this DTD public? */
   predicate isPublic()  { not xmlDTDs(this,_,"",_,_) }

   /** get this DTD's parent */
   XMLParent getParent() { xmlDTDs(this,_,_,_,result) }

   /** printable representation */
   string toString() { 
      (this.isPublic() and result = this.getRoot() + " PUBLIC '" + 
                                    this.getPublicId() + "' '" + 
                                    this.getSystemId() + "'") or
      (not this.isPublic() and result = this.getRoot() + 
                                        " SYSTEM '" + 
                                        this.getSystemId() + "'")
   }
}

/** An XML tag in an XML file */
class XMLElement extends @xmlelement, XMLParent, XMLLocatable {
   /** get this element's name */
   string getName() { xmlElements(this,result,_,_,_) }
   
   /** get the file this element appears in */
   XMLFile getFile()             { xmlElements(this,_,_,_,result) }

   /** get this element's parent */
   XMLParent getParent()         { xmlElements(this,_,result,_,_) }
   
   /** get the index of this element among its parent's children */
   int getIndex()                { xmlElements(this, _, _, result, _) }

   /** does this element have a namespace? */
   predicate hasNamespace()      { xmlHasNs(this,_,_) }

   /** get this element's namespace (if any) */
   XMLNamespace getNamespace()   { xmlHasNs(this,result,_) }

   /** get the index of this element */
   int getElementPositionIndex() { xmlElements(this,_,_,result,_) }

   /** gets the depth of this element */
   int getDepth() { result = this.getParent().getDepth() + 1 }

   /** gives an attribute of this element */
   XMLAttribute getAnAttribute() { result.getElement() = this }

   /** gives an attribute with a specific name */
   XMLAttribute getAttribute(string name) { 
      result.getElement() = this and result.getName() = name 
   }

   /** does this element have an attribute name? */
   predicate hasAttribute(string name) {
      exists(XMLAttribute a| a = this.getAttribute(name))
   }

   /** gives the value of a specific attribute */
   string getAttributeValue(string name) { 
      result = this.getAttribute(name).getValue() 
   }

	string toString() { result = XMLParent.super.toString() }

}

/** An attribute that occurs inside an XML element */
class XMLAttribute extends @xmlattribute, XMLLocatable {
   /** get this attribute's name */
   string getName() { xmlAttrs(this,_,result,_,_,_) }
   
   /** get the element this attribute belongs to */
   XMLElement getElement()     { xmlAttrs(this,result,_,_,_,_) }

   /** does this attribute have a namespace? */
   predicate hasNamespace()    { xmlHasNs(this,_,_) }

   /** get this attribute's namespace (if any) */
   XMLNamespace getNamespace() { xmlHasNs(this,result,_) }
   
   /** get this attribute's value */
   string getValue()    { xmlAttrs(this,_,_,result,_,_) }

   /** printable representation */
   string toString()    { result = this.getName() + "=" + this.getValue() }

   /** set icon to represent this attribute */
   string getIconPath() { result = "icons/publicfield.png" }
}

/** A namespace used in an XML file */
class XMLNamespace extends @xmlnamespace {
   /** get the namespace prefix */
   string getPrefix() { xmlNs(this,result,_,_) }

   /** get the namespace URI */
   string getURI()    { xmlNs(this,_,result,_) }

   /** if this namespace has no prefix, then it is default */
   predicate isDefault() { this.getPrefix() = "" }
   
   /** printable representation */
   string toString() { 
      (this.isDefault() and result = this.getURI()) or
      (not this.isDefault() and result = this.getPrefix() + ":" + this.getURI())
   }

   /** set icon to represent this namespace */
   string getIconPath() { result = "icons/publicfield.png" }
}

/** A comment of the form &lt;!-- ... --> */
class XMLComment extends @xmlcomment, XMLLocatable {
   /** get comment content */
   string getText()      { xmlComments(this,result,_,_) }

   /** get parent of this comment */
   XMLParent getParent() { xmlComments(this,_,result,_) }

   /** printable representation */
   string toString()    { result = this.getText() }

   /** set icon to represent this comment */
   string getIconPath() { result = "icons/publicfield.png" }
}

/* A sequence of characters that occurs between opening and 
*  closing tags of an XML element, excluding other elements */
class XMLCharacters extends @xmlcharacters, XMLLocatable {
   /** get content of this character sequence */
   string getCharacters() { xmlChars(this,result,_,_,_,_) }

   /** get the parent of this character sequence */
   XMLParent getParent()  { xmlChars(this,_,result,_,_,_) }

   /** is this character sequence CDATA? */
   predicate isCDATA()    { xmlChars(this,_,_,_,1,_) }

   /** printable representation */
   string toString()    { result = this.getCharacters() }

   /** set icon to represent this character sequence */
   string getIconPath() { result = "icons/publicfield.png" }
}

