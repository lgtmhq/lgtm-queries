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
 * Provides a class that represents named elements in Java programs.
 */

import CompilationUnit
import semmle.code.Location
import Javadoc

/** A program element that has a name. */
class Element extends @element, Top {
  /** Holds if this element has the specified `name`. */
  predicate hasName(string name) { hasName(this,name) }

  /** The name of this element. */
  string getName() { this.hasName(result) }

  /**
   * Holds if this element transitively contains the specified element `e`.
   */
  predicate contains(Element e) { this.hasChildElement+(e) }

  /**
   * Holds if this element is the immediate parent of the specified element `e`.
   *
   * It is usually preferable to use more specific predicates such as
   * `getEnclosingCallable()`, `getDeclaringType()` and/or `getEnclosingType()`
   * instead of this general predicate.
   */
  predicate hasChildElement(Element e) { hasChildElement(this, e) }

  /**
   * Holds if this element pertains to a source file.
   *
   * Elements pertaining to source files may include generated elements
   * not visible in source code, such as implicit default constructors.
   */
  predicate fromSource() { 
    getCompilationUnit().getExtension() = "java" 
  }

  /** The compilation unit that this element belongs to. */
  CompilationUnit getCompilationUnit() { result = getFile() }

  /** Cast this element to a `Documentable`. */
  Documentable getDoc() { result = this }
}

/**
 * Holds if element `parent` is immediately above element `e` in the syntax tree.
 */
private predicate hasChildElement(Element parent, Element e) {
  cupackage(e,parent) or
  enclInReftype(e,parent) or
  (not(enclInReftype(e,_)) and e.(Class).getCompilationUnit() = parent) or
  (not(enclInReftype(e,_)) and e.(Interface).getCompilationUnit() = parent) or
  methods(e,_,_,_,parent,_) or
  constrs(e,_,_,_,parent,_) or
  params(e,_,_,parent,_) or
  fields(e,_,_,parent,_) or
  typeVars(e,_,_,_,parent)
}
