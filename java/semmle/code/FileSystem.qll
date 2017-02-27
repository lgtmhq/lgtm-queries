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
 * This library provides classes that represent objects in the file system,
 * such as individual files or folders.
 */

import Location

/**
 * A container is an abstract representation of a file system object that can
 * hold elements of interest.
 */
class Container extends @container, Top {
  /** The name of this container. */
  string getName() {
    folders(this,result,_) or
    files(this,result,_,_,_)
  }

  /** The short name of this container, excluding its path and extension. */
  string getShortName() {
    folders(this,_,result) or
    files(this,_,result,_,_)
  }

  /** The full name of this container, including its path and extension (if any). */
  string getFullName() {
    folders(this,result,_) or
    files(this,result,_,_,_)
  }

  /**
   * The relative path of this container from the root of the analyzed source
   * location, provided this container is located under the source location
   * (that is, the source location is a prefix of `getFullName()`).
   */
  string getRelativePath() {
    exists(string fullPath, string prefix |
      fullPath = getFullName() and
      sourceLocationPrefix(prefix) |
      (
        fullPath.matches(prefix + "/%") and
        result = fullPath.suffix(prefix.length()+1)
      ) or
      (
        // Special case for `prefix` = "/" and "/" at the beginning of `fullPath`.
        prefix = "/" and
        fullPath.charAt(0) = "/" and
        result = fullPath.suffix(1)
      )
    )
  }

  /** A printable representation of this container. */
  string toString() { result = this.getName() }

  /** A child of this container. */
  Container getAChildContainer() { containerparent(this,result) }

  /** The parent of this container. */
  Container getParentContainer() { result.getAChildContainer() = this }
}

/** A folder holds files. */
class Folder extends Container, @folder {
  /** A file contained within this folder. */
  File getAFile() { containerparent(this,result) }
  
  /** The URL of this folder. */
  string getURL() { result = "folder://" + getName() }
}

/**
 * A file on disk.
 *
 * Note that `File` extends `Container` as it may be a `jar` file.
 */
class File extends Container, @file {
  /** The name of this file. */
  string getName() { files(this,result,_,_,_) }

  /** Whether this file has a specific name. */
  predicate hasName(string name) { name = this.getName() }

  string toString() { result = this.getName() }  

  /** The extension of this file. */
  string getExtension() { files(this,_,_,result,_) }

  /** The short name of this file, excluding its path and extension. */
  string getShortName() { files(this,_,result,_,_) }
  
  /** The URL of this file. */
  string getURL() { result = "file://" + this.getFullName() + ":0:0:0:0" }
}

/**
 * A Java archive file with a ".jar" extension.
 */
class JarFile extends File {
  JarFile() {
    getExtension() = "jar"
  }

  /**
   * Gets the main attribute with the specified `key`
   * from this JAR file's manifest.
   */
  string getManifestMainAttribute(string key) {
    jarManifestMain(this, key, result)
  }

  /**
   * Gets the "Specification-Version" main attribute
   * from this JAR file's manifest.
   */
  string getSpecificationVersion() {
    result = getManifestMainAttribute("Specification-Version")
  }

  /**
   * Gets the "Implementation-Version" main attribute
   * from this JAR file's manifest.
   */
  string getImplementationVersion() {
    result = getManifestMainAttribute("Implementation-Version")
  }

  /**
   * Gets the per-entry attribute for the specified `entry` and `key`
   * from this JAR file's manifest.
   */
  string getManifestEntryAttribute(string entry, string key) {
    jarManifestEntries(this, entry, key, result)
  }
}
