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

import semmle.code.cpp.Class
import semmle.code.cpp.File
import semmle.code.cpp.Function

/**
 * A linker call during the build process, typically resulting in an
 * executable or a shared library.
 *
 * Note that if linkage information isn't captured as part of the snapshot,
 * then everything is grouped together into a single dummy link target.
 */
class LinkTarget extends @link_target {
  /**
   * Gets the file which was built.
   */
  File getBinary() {
    link_targets(this, result)
  }

  /**
   * Holds if this is the dummy link target: if linkage information isn't
   * captured as part of the snapshot, then everything is grouped together
   * into a single dummy link target.
   */
  predicate isDummy() {
    getBinary().getName() = ""
  }

  /** Gets a textual representation of this element. */
  string toString() {
    result = getBinary().getName()
  }

  /**
   * Gets a function which was compiled into this link target, or had its
   * declaration included by one of the translation units which contributed
   * to this link target.
   */
  Function getAFunction() {
    link_parent(result, this)
  }

  /**
   * Gets a class which had its declaration included by one of the
   * translation units which contributed to this link target.
   */
  Class getAClass() {
    link_parent(result, this)
  }
}

/**
 * Holds if this database was created with the linker awareness feature
 * switched on.
 */
cached predicate isLinkerAwareExtracted() {
  exists(LinkTarget lt | not lt.isDummy())
}
