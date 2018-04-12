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

/** Provides classes for restricting the locations reported for program elements. */

import javascript

/**
 * A program element with its location restricted to its first line, unless the element
 * is less than one line long to begin with.
 *
 * This is useful for avoiding multi-line violations.
 */
class FirstLineOf extends Locatable {
  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/help/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                             int endline, int endcolumn) {
    exists (int xl, int xc |
      getLocation().hasLocationInfo(filepath, startline, startcolumn, xl, xc) and
      startline = endline and
      if xl = startline then
        endcolumn = xc
      else
        endcolumn = max(int c | any(Location l).hasLocationInfo(filepath, startline, _,
                                                                          startline, c))
    )
  }
}

/**
 * A program element with its location restricted to its last line, unless the element
 * is less than one line long to begin with.
 *
 * This is useful for avoiding multi-line violations.
 */
class LastLineOf extends Locatable {
  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/help/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                             int endline, int endcolumn) {
    exists (int xl, int xc |
      getLocation().hasLocationInfo(filepath, xl, xc, endline, endcolumn)
      and startline = endline
      and if xl = endline then startcolumn = xc else startcolumn = 1
    )
  }
}