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

import Locations

/**
 * Restrict the location of a syntactic element to its first line, unless the element
 * is less than one line long to begin with.
 *
 * This is useful for avoiding multi-line violations.
 */
class FirstLineOf extends Locatable {
  predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
    exists (int xl, int xc |
      getLocation().hasLocationInfo(filepath, bl, bc, xl, xc) and
      bl = el and
      if xl = bl then
        ec = xc
      else
        exists (Line l | l.getLocation().hasLocationInfo(filepath, bl, 1, bl, ec))
    )
  }
}
/**
 * Restrict the location of a syntactic element to its last line, unless the element
 * is less than one line long to begin with.
 *
 * This is useful for avoiding multi-line violations.
 */
class LastLineOf extends Locatable {
  predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
    exists (int xl, int xc |
      getLocation().hasLocationInfo(filepath, xl, xc, el, ec)
      and bl = el
      and if xl = el then bc = xc else bc = 1
    )
  }
}