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

/** Provides classes for working with locations and program elements that have locations. */

import Files
import Lines
import Tokens

/**
 * A location as given by a file, a start line, a start column,
 * an end line, and an end column.
 *
 * For more information about locations see [LGTM locations](https://lgtm.com/docs/ql/locations).
 */
class Location extends @location {
  /** Gets the file for this location. */
  File getFile() {
    locations_default(this, result, _, _, _, _)
  }

  /** Gets the start line of this location. */
  int getStartLine() {
    locations_default(this, _, result, _, _, _)
  }

  /** Gets the start column of this location. */
  int getStartColumn() {
    locations_default(this, _, _, result, _, _)
  }

  /** Gets the end line of this location. */
  int getEndLine() {
    locations_default(this, _, _, _, result, _)
  }

  /** Gets the end column of this location. */
  int getEndColumn() {
    locations_default(this, _, _, _, _, result)
  }

  /** Gets the number of lines covered by this location. */
  int getNumLines() {
    result = getEndLine() - getStartLine() + 1
  }

  /** Holds if this location starts before location `that`. */
  predicate startsBefore(Location that) {
    exists (File f, int sl1, int sc1, int sl2, int sc2 |
      locations_default(this, f, sl1, sc1, _, _) and
      locations_default(that, f, sl2, sc2, _, _) |
      sl1 < sl2
      or
      sl1 = sl2 and sc1 < sc2
    )
  }

  /** Holds if this location ends after location `that`. */
  predicate endsAfter(Location that) {
    exists (File f, int el1, int ec1, int el2, int ec2 |
      locations_default(this, f, _, _, el1, ec1) and
      locations_default(that, f, _, _, el2, ec2) |
      el1 > el2
      or
      el1 = el2 and ec1 > ec2
    )
  }

  /**
   * Holds if this location contains location `that`, meaning that it starts
   * before and ends after it.
   */
  predicate contains(Location that) {
    this.startsBefore(that) and this.endsAfter(that)
  }

  /** Holds if this location is empty. */
  predicate isEmpty() {
    exists (int l, int c | locations_default(this, _, l, c, l, c-1))
  }

  /** Gets a textual representation of this element. */
  string toString() {
    result = this.getFile().getName() + ":" + this.getStartLine().toString()
  }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/docs/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                             int endline, int endcolumn) {
    exists(File f |
      locations_default(this, f, startline, startcolumn, endline, endcolumn) and
      filepath = f.getPath()
    )
  }
}

/** A program element with a location. */
class Locatable extends @locatable {
  /** Gets the file this program element comes from. */
  File getFile() {
    result = getLocation().getFile()
  }

  /** Gets this element's location. */
  Location getLocation() {
    hasLocation(this, result)
  }

  /** Gets the line on which this element starts. */
  Line getStartLine() {
    exists (Location l1, Location l2 |
      l1 = this.getLocation() and
      l2 = result.getLocation() and
      l1.getFile() = l2.getFile() and
      l1.getStartLine() = l2.getStartLine()
    )
  }

  /** Gets the line on which this element ends. */
  Line getEndLine() {
    exists (Location l1, Location l2 |
      l1 = this.getLocation() and
      l2 = result.getLocation() and
      l1.getFile() = l2.getFile() and
      l1.getEndLine() = l2.getStartLine()
    )
  }

  /** Gets the first token belonging to this element. */
  Token getFirstToken() {
    exists (Location l1, Location l2 |
      l1 = this.getLocation() and
      l2 = result.getLocation() and
      l1.getFile() = l2.getFile() and
      l1.getStartLine() = l2.getStartLine() and
      l1.getStartColumn() = l2.getStartColumn()
    )
  }

  /** Gets the last token belonging to this element. */
  Token getLastToken() {
    exists (Location l1, Location l2 |
      l1 = this.getLocation() and
      l2 = result.getLocation() and
      l1.getFile() = l2.getFile() and
      l1.getEndLine() = l2.getEndLine() and
      l1.getEndColumn() = l2.getEndColumn()
    ) and
    // exclude empty EOF token
    not result instanceof EOFToken
  }

  /** Gets a token belonging to this element. */
  Token getAToken() {
    exists (string path, int sl, int sc, int el, int ec,
                  int tksl, int tksc, int tkel, int tkec |
      this.getLocation().hasLocationInfo(path, sl, sc, el, ec) and
      result.getLocation().hasLocationInfo(path, tksl, tksc, tkel, tkec) |
      (sl < tksl or (sl = tksl and sc <= tksc))
      and
      (tkel < el or (tkel = el and tkec <= ec))
    ) and
    // exclude empty EOF token
    not result instanceof EOFToken
  }

  /** Gets the number of lines covered by this element. */
  int getNumLines() {
    result = getLocation().getNumLines()
  }

  /** Gets a textual representation of this element. */
  string toString() {
    // to be overridden by subclasses
    none()
  }
}