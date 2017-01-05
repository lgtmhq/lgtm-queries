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
 * A library for working with locations.
 *
 * Locations represent parts of files and are used to map elements to their source location.
 */

import FileSystem
import semmle.code.java.Element

/** Whether element `e` has name `name`. */
predicate hasName(Element e, string name) {
  classes(e,name,_,_) or
  interfaces(e,name,_,_) or
  primitives(e,name) or
  constrs(e,name,_,_,_,_) or
  methods(e,name,_,_,_,_) or
  fields(e,name,_,_,_) or
  packages(e,name) or
  files(e,_,name,_,_) or
  exists(int pos | params(e,name,_,pos,_,_) |
    not exists(string other | params(e,other,_,_,_,_) and other != name) or
    exists(string other | params(e,other,_,_,_,_) and name != "p"+pos)
  ) or
  localvars(e,name,_,_) or
  typeVars(e,name,_,_,_) or
  wildcards(e,name,_) or
  arrays(e,name,_,_,_) or
  modifiers(e,name)
}

/**
 * Top is the root of the QL type hierarchy; it defines some default
 * methods for obtaining locations and a standard `toString()` method.
 */
class Top extends @top {
  /** The source location for this element. */
  Location getLocation() { fixedHasLocation(this, result, _) }

  /**
   * Whether this element has the specified location information,
   * including file path, start line, start column, end line and end column.
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
    exists(File f, Location l | fixedHasLocation(this, l, f) |
      locations_default(l,f,startline,startcolumn,endline,endcolumn) and
      filepath = f.getFullName()
    )
  }
  
  /** Returns the file associated with this element. */
  File getFile() {
    fixedHasLocation(this, _, result)
  }

  /**
   * The total number of lines that this element ranges over,
   * including lines of code, comment and whitespace-only lines.
   */
  int getTotalNumberOfLines() {
    numlines(this, result, _, _)
  }

  /** The number of lines of code that this element ranges over. */
  int getNumberOfLinesOfCode() {
    numlines(this, _, result, _)
  }

  /** The number of comment lines that this element ranges over. */
  int getNumberOfCommentLines() {
    numlines(this, _, _, result)
  }

  /** A printable representation of this element. */
  string toString() { hasName(this, result) }
}

/** A location maps language elements to positions in source files. */
class Location extends @location {
  /** The line number where this location starts. */
  int getStartLine() { locations_default(this,_,result,_,_,_) }

  /** The column number where this location starts. */
  int getStartColumn() { locations_default(this,_,_,result,_,_) }

  /** The line number where this location ends. */
  int getEndLine() { locations_default(this,_,_,_,result,_) }

  /** The column number where this location ends. */
  int getEndColumn() { locations_default(this,_,_,_,_,result) }

  /**
   * The total number of lines that this location ranges over,
   * including lines of code, comment and whitespace-only lines.
   */
  int getNumberOfLines() {
    exists(@sourceline s | hasLocation(s, this) |
      numlines(s,result,_,_) or
      (not numlines(s,_,_,_) and result = 0)
    )
  }

  /** The number of lines of code that this location ranges over. */
  int getNumberOfLinesOfCode() {
    exists(@sourceline s | hasLocation(s, this) |
      numlines(s,_,result,_) or
      (not numlines(s,_,_,_) and result = 0)
    )
  }

  /** The number of comment lines that this location ranges over. */
  int getNumberOfCommentLines() {
    exists(@sourceline s | hasLocation(s, this) |
      numlines(s,_,_,result) or
      (not numlines(s,_,_,_) and result = 0)
    )
  }

  /** The file containing this location. */
  File getFile() { locations_default(this,result,_,_,_,_) } 

  /** A string representation containing the file and range for this location. */
  string toString() {
    exists(File f, int startLine, int endLine | locations_default(this,f,startLine,_,endLine,_) |
      if endLine = startLine then
        result = f.toString() + ":" + startLine.toString()
      else 
        result = f.toString() + ":" + startLine.toString() + "-" + endLine.toString()
    )
  }

  /**
   * Whether this location has the specified location information,
   * including file path, start line, start column, end line and end column.
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
    exists(File f | locations_default(this,f,startline,startcolumn,endline,endcolumn) |
      filepath = f.getFullName()
    )
  }
}

private predicate hasSourceLocation(Top l, Location loc, File f) {
  hasLocation(l, loc) and f = loc.getFile() and f.getExtension() = "java"
}

cached
private predicate fixedHasLocation(Top l, Location loc, File f) {
  hasSourceLocation(l, loc, f) or
  (hasLocation(l, loc) and not hasSourceLocation(l, _, _) and locations_default(loc, f, _, _, _, _))
}
