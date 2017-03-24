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

/** Provides classes for working with files and folders. */

import AST

/** A file or folder. */
abstract class Container extends @container {
  /** Gets the full path of this file or folder. */
  abstract string getPath();

  /**
   * Gets the base name of this file or folder, including any extension.
   *
   * For example, the base name of `/tmp/tst.js` is `tst.js`.
   */
  abstract string getName();

  /** Gets a textual representation of this element. */
  string toString() {
    result = getName()
  }

  /** Gets the parent folder of this file or folder. */
  Folder getParent() {
    containerparent(result, this)
  }
}

/** A folder. */
class Folder extends Container, @folder {
  override string getPath() {
    folders(this, result, _)
  }

  /**
   * Gets the base name of this folder.
   *
   * For example, the base name of `/usr/home` is `home`.
   */
  override string getName() {
    folders(this, _, result)
  }

  /** Gets a file or subfolder contained in this folder. */
  Container getAChild() {
    result.getParent() = this
  }

  /** Gets the file or subfolder in this folder that has the given `name`, if any. */
  Container getChild(string name) {
    result = getAChild() and
    result.getName() = name
  }

  /** Gets a file in this folder. */
  File getAFile() {
    result = getAChild()
  }

  /** Gets the file in this folder that has the given `name`, if any. */
  File getFile(string name) {
    result = getChild(name)
  }

  /** Gets a subfolder contained in this folder. */
  Folder getASubFolder() {
    result = getAChild()
  }

  override string toString() {
    result = this.getName()
  }

  /** Gets the URL of this folder. */
  string getURL() {
    result = "folder://" + getPath()
  }
}

/** A file. */
class File extends Container, @file, Locatable {
  /** Gets the full path of this file. */
  override string getPath() {
    files(this, result, _, _, _)
  }

  /**
   * Gets the relative path of this file from the root of the analyzed source
   * location.
   *
   * This has no result if the file is not under the source location (that is,
   * if `getPath` does not have the source location as a prefix).
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

  /**
   * Gets the base name of this file, including any extension.
   *
   * For example, the base name of `/tmp/tst.js` is `tst.js`.
   */
  override string getName() {
    result = getShortName() + "." + getExtension()
  }

  /**
   * Gets the short name of this file without extension.
   *
   * For example, the short name of `/tmp/tst.js` is `tst`.
   */
  string getShortName() {
    files(this, _, result, _, _)
  }

  /** Gets the extension of this file. */
  string getExtension() {
    files(this, _,_ , result, _)
  }

  /** Gets the number of lines in this file. */
  int getNumberOfLines() {
    numlines(this, result, _, _)
  }

  /** Gets the number of lines containing code in this file. */
  int getNumberOfLinesOfCode() {
    numlines(this, _, result, _)
  }

  /** Gets the number of lines containing comments in this file. */
  int getNumberOfLinesOfComments() {
    numlines(this, _, _, result)
  }

  /** Gets a toplevel piece of JavaScript code in this file. */
  TopLevel getATopLevel() {
    result.getFile() = this
  }

  override string toString() {
    result = Container.super.toString()
  }

  /** Gets the URL of this file. */
  string getURL() {
    result = "file://" + this.getPath() + ":0:0:0:0"
  }
}
