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

import AST

/** A file or folder */
abstract class Container extends @container {
  /** Get the full path of this file or folder. */
  abstract string getPath();

  /** Get the base name of this file or folder. */
  abstract string getName();

  string toString() {
    result = getName()
  }

  /** Get the parent folder of this file or folder. */
  Folder getParent() {
    containerparent(result, this)
  }
}

/** A filesystem folder. */
class Folder extends Container, @folder {
  /** Get the full path of the folder. */
  string getPath() {
    folders(this, result, _)
  }
  
  /** Get the name of the folder. */
  string getName() {
    folders(this, _, result)
  }

  /** Get a file or subfolder contained in this folder. */
  Container getAChild() {
    result.getParent() = this
  }

  /** Look up a file or subfolder in this folder by name. */
  Container getChild(string name) {
    result = getAChild() and
    result.getName() = name
  }

  /** Get a file from this folder. */
  File getAFile() {
    result = getAChild()
  }

  /** Look up a file in this folder by name. */
  File getFile(string name) {
    result = getChild(name)
  }

  /** Get a subfolder contained in this folder. */
  Folder getASubFolder() {
    result = getAChild()
  }
  
  string toString() {
    result = this.getName()
  }

  /** Get the URL of this folder. */
  string getURL() {
    result = "folder://" + getPath()
  }

  /** Get the icon to be used when displaying folders as query results. */
  string getIconPath() {
    result = "icons/folder.png"
  }
}

/** A file. */
class File extends Container, @file, Locatable {
  /** Get the full path of this file. */
  string getPath() {
    files(this, result, _, _, _)
  }

  /**
   * Get the relative path of this file from the root of the analyzed source
   * location, or has no result if this file is not under the source location (i.e.
   * if `getFullName` does not have the source location as a prefix).
   */
  string getRelativePath() {
    exists (string fullPath, string prefix |
      fullPath = getPath() and
      sourceLocationPrefix(prefix) |
      (
        fullPath.matches(prefix + "/%") and
        result = fullPath.suffix(prefix.length()+1)
      ) or
      (
        // special case for prefix = "/" and "/" at the beginning of path
        prefix = "/" and
        fullPath.charAt(0) = "/" and
        result = fullPath.suffix(1)
      )
    )
  }

  /** Get the base name of this file including extension. */
  string getName() {
    result = getShortName() + "." + getExtension()
  }

  /** Get the short name of this file without extension. */
  string getShortName() {
    files(this, _, result, _, _)
  }

  /** Get the extension of this file. */
  string getExtension() {
    files(this, _,_ , result, _)
  }
  
  /** Get the number of lines in this file. */
  int getNumberOfLines() {
    result = sum(TopLevel tl | tl = getATopLevel() | tl.getNumberOfLines())
  }
  
  /** Get the number of lines containing code in this file. */
  int getNumberOfLinesOfCode() {
    result = sum(TopLevel tl | tl = getATopLevel() | tl.getNumberOfLinesOfCode())
  }
  
  /** Get the number of lines containing comments in this file. */
  int getNumberOfLinesOfComments() {
    result = sum(TopLevel tl | tl = getATopLevel() | tl.getNumberOfLinesOfComments())
  }
  
  /** Get a toplevel piece of JavaScript code embedded in this file. */
  TopLevel getATopLevel() {
    result.getFile() = this
  }
  
  string toString() {
    result = Container.super.toString()
  }

  /** Get the URL of this file. */
  string getURL() {
    result = "file://" + this.getPath() + ":0:0:0:0"
  }

  /** Get the icon to be used when displaying files as query results. */
  string getIconPath() {
    result = "icons/file.png"
  }
}
