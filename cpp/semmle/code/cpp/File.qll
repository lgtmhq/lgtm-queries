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

import semmle.code.cpp.Element
import semmle.code.cpp.Declaration
import semmle.code.cpp.metrics.MetricFile

/**
 * A folder which was observed on disk during the build process.
 *
 * For the example folder name of "/usr/home/me", the path decomposes to:
 *
 *  1. "/usr/home" - see `getParent`.
 *  2. "me" - see `getShortName`.
 *
 * For the full path, see any of `getName`, `hasName`, `getFullName`, or
 * `toString`.
 */
class Folder extends @folder {

  /** Gets the name of this folder. */
  string getName() { folders(this,result,_) }

  /** Holds if this element is named `name`. */
  predicate hasName(string name) { name = this.getName() }

  /** Gets the full name of this folder. */
  string getFullName() { result = this.getName() }

  /** Gets the last part of the folder name. */
  string getShortName() {
    exists (string longnameRaw, string longname
    | folders(this,_,longnameRaw) and
      longname = longnameRaw.replaceAll("\\", "/")
    | exists (int index
      | result = longname.splitAt("/", index) and
        not exists (longname.splitAt("/", index+1))))
  }

  /** Gets a textual representation of this folder. */
  string toString() { result = this.getName() }

  /** Gets the URL of this folder. */
  string getURL() { result = "folder://" + this.getName() }

  /** Gets the parent folder. */
  Folder getParent() { containerparent(result,this) }

  /** Gets a file in this folder. */
  File getAFile() { result.getParent() = this }

  /** Gets a folder in this folder. */
  Folder getAFolder() { result.getParent() = this }
}

/**
 * A file which was observed on disk during the build process.
 *
 * For the example filename of "/usr/home/me/myprogram.c", the filename
 * decomposes to:
 *
 *  1. "/usr/home/me" - see `getParent`.
 *  2. "myprogram" - see `getShortName`.
 *  3. "c" - see `getExtension`.
 *
 * For the full filename, see any of `getName`, `hasName`, `getFullName`,
 * or `toString`.
 */
class File extends @file {
  /** Holds if this file was compiled as C (at any point). */
  predicate compiledAsC() {
    fileannotations(this,1,"compiled as c","1")
  }

  /** Holds if this file was compiled as C++ (at any point). */
  predicate compiledAsCpp() {
    fileannotations(this,1,"compiled as c++","1")
  }

  /** Holds if this file was compiled as Objective C (at any point). */
  predicate compiledAsObjC() {
    fileannotations(this,1,"compiled as obj c","1")
  }

  /** Holds if this file was compiled as Objective C++ (at any point). */
  predicate compiledAsObjCpp() {
    fileannotations(this,1,"compiled as obj c++","1")
  }

  /** Gets a top-level element declared in this file. */
  Declaration getATopLevelDeclaration() {
    result.getAFile() = this and result.isTopLevel()
  }

  /** Gets a declaration in this file. */
  Declaration getADeclaration() { result.getAFile() = this }

  /** Holds if this file uses the given macro. */
  predicate usesMacro(Macro m) {
    exists(MacroInvocation mi | mi.getFile() = this and
                                mi.getMacro() = m)
  }

  /**
   * Gets a file that is directly included from this file (using a
   * pre-processor directive like `#include`).
   */
  File getAnIncludedFile() {
    exists(Include i | i.getFile() = this and i.getIncludedFile() = result)
  }

  /** Gets the folder which contains this file. */
  Folder getParent() { containerparent(result,this) }

  /**
   * Holds if this file may be from source.
   *
   * Note: this predicate is provided for consistency with the libraries
   * for other languages, such as Java and Python. In C++, all files are
   * classified as source files, so this predicate is always true.
   */
  predicate fromSource() { numlines(this,_,_,_) }

  /**
   * Holds if this file may be from a library.
   *
   * DEPRECATED: For historical reasons this is true for any file.
   */
  deprecated
  predicate fromLibrary() { any() }

  /** Gets the metric file. */
  MetricFile getMetrics() { result = this }

  /**
   * Gets the full name of this file, for example:
   * "/usr/home/me/myprogram.c".
   */
  string getName() { files(this,result,_,_,_) }

  /**
   * Gets the relative path of this file from the root of the analyzed
   * source location. There is no result if the file is not in a
   * sub-directory of the source location (`getFullName` does not have the
   * source location as a prefix).
   */
  string getRelativePath() {
    exists(string prefix |
      sourceLocationPrefix(prefix) |
      (
        getFullName().matches(prefix + "/%") and
        // remove source location and the following slash
        result = getFullName().suffix(prefix.length() + 1)
      ) or (
        // Special case for prefix = "/" and "/" at the beginning of path.
        prefix = "/" and
        getFullName().charAt(0) = "/" and
        result = getFullName().suffix(1)
      )
    )
  }

  /**
   * Holds if this file has the specified full name.
   *
   * Example usage: `f.hasName("/usr/home/me/myprogram.c")`.
   */
  predicate hasName(string name) { name = this.getName() }

  /**
   * Gets the full name of this file, for example
   * "/usr/home/me/myprogram.c".
   */
  string getFullName() { result = this.getName() }

  /** Gets a textual representation of this file. */
  string toString() { result = this.getName() }

  /** Gets the URL of this file. */
  string getURL() { result = "file://" + this.getName() + ":0:0:0:0" }

  /** Gets the extension of this file, for example "c". */
  string getExtension() { files(this,_,_,result,_) }

  /**
   * Gets the name and extension(s), but not path, of a file. For example,
   * if the full name is "/path/to/filename.a.bcd" then the filename is
   * "filename.a.bcd".
   */
  string getFileName() {
      // [a/b.c/d/]fileName
      //         ^ beginAfter
      exists(string fullName, int beginAfter |
          fullName = this.getName() and
          beginAfter = max(int i | i = -1 or fullName.charAt(i) = "/" | i) and
          result = fullName.suffix(beginAfter + 1)
      )
  }

  /**
   * Gets the short name of this file. For example, if the full name is
   * "/path/to/filename.a.bcd" then the short name is "filename".
   */
  string getShortName() { files(this,_,result,_,_) }
}

/**
 * A C/C++ header file, as determined (mainly) by file extension.
 *
 * For the related notion of whether a file is included anywhere (using a
 * pre-processor directive like `#include`), use `Include.getIncludedFile`.
 */
class HeaderFile extends File {

  HeaderFile() {
    exists(string ext | ext = this.getExtension().toLowerCase() |
      ext = "h" or ext = "r"
      or (ext = "" and exists(Include i | i.getIncludedFile() = this))

      /*    ---   */ or ext = "hpp" or ext = "hxx" or ext = "h++" or ext = "hh" or ext = "hp"
      or ext = "tcc" or ext = "tpp" or ext = "txx" or ext = "t++" /*    ---         ---    */
    )
  }

}

/**
 * A C source file, as determined by file extension.
 *
 * For the related notion of whether a file is compiled as C code, use
 * `File.compiledAsC`.
 */
class CFile extends File {

  CFile() {
    exists(string ext | ext = this.getExtension().toLowerCase() |
      ext = "c" or ext = "i"
    )
  }

}

/**
 * A C++ source file, as determined by file extension.
 *
 * For the related notion of whether a file is compiled as C++ code, use
 * `File.compiledAsCpp`.
 */
class CppFile extends File {

  CppFile() {
    exists(string ext | ext = this.getExtension().toLowerCase() |
      /*     ---     */ ext = "cpp" or ext = "cxx" or ext = "c++" or ext = "cc" or ext = "cp"
      or ext = "icc" or ext = "ipp" or ext = "ixx" or ext = "i++" or ext = "ii" /*  ---    */
      // Note: .C files are indistinguishable from .c files on some
      // file systems, so we just treat them as CFile's.
    )
  }

}

/**
 * An Objective C source file, as determined by file extension.
 *
 * For the related notion of whether a file is compiled as Objective C
 * code, use `File.compiledAsObjC`.
 */
class ObjCFile extends File {

  ObjCFile() {
    exists(string ext | ext = this.getExtension().toLowerCase() |
      ext = "m" or ext = "mi"
    )
  }

}

/**
 * An Objective C++ source file, as determined by file extension.
 *
 * For the related notion of whether a file is compiled as Objective C++
 * code, use `File.compiledAsObjCpp`.
 */
class ObjCppFile extends File {

  ObjCppFile() {
    exists(string ext | ext = this.getExtension().toLowerCase() |
      ext = "mm" or ext = "mii"
      // Note: .M files are indistinguishable from .m files on some
      // file systems, so we just treat them as ObjCFile's.
    )
  }

}
