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
 * @name Jump-to-definition links
 * @description Generates use-definition pairs that provide the data
 *              for jump-to-definition in the code viewer.
 * @kind definitions
 */

import cpp

/**
 * An element with a `hasLocationInfo()` predicate.
 *
 * We need to give locations that may not be in the database, so
 * we use `hasLocationInfo()` rather than `getLocation()`.
 */
class ElementWithHasLocationInfo extends @element {
  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/docs/ql/locations).
   */
  predicate hasLocationInfo(string filepath,
                            int startline, int startcolumn,
                            int endline, int endcolumn) {
    exists(Location l | l = this.(Element).getLocation()
                    and filepath    = l.getFile().getFullName()
                    and startline   = l.getStartLine()
                    and startcolumn = l.getStartColumn()
                    and endline     = l.getEndLine()
                    and endcolumn   = l.getEndColumn())
  }

  /** Gets a textual representation of this element. */
  string toString() { result = this.(Element).toString() }
}

/**
 * A `MacroAccess` with a `hasLocationInfo` predicate.
 *
 * This has a location that covers only the name of the accessed
 * macro, not its arguments (which are included by `MacroAccess`'s
 * `getLocation()`).
 */
class MacroAccessWithHasLocationInfo extends ElementWithHasLocationInfo {
  MacroAccessWithHasLocationInfo() {
    this instanceof MacroAccess
  }

  override
  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    exists(MacroAccess ma, Location l |
           ma = this
       and l = ma.getLocation()
       and path = l.getFile().getFullName()
       and sl = l.getStartLine()
       and sc = l.getStartColumn()
       and el = sl
       and ec = sc + ma.getMacroName().length() - 1)
  }
}

/**
 * Gets the location of an entity, of kind `kind`, that element `e` uses,
 * if any.
 *
 * The `kind` is a string representing what kind of use it is.
 * It is `"M"` for function and method calls, `"T"` for uses of types,
 * `"V"` for variable access, and `"X"` for macro accesses.
 */
Location definitionOf(Element e, string kind) {
     (kind = "M" and result = e.(Call).getTarget().getLocation())
  or (kind = "V" and result = e.(Access).getTarget().getLocation())
  or (kind = "X" and result = e.(MacroAccess).getMacro().getLocation())
}

from ElementWithHasLocationInfo e, Location def, string kind
where not e.(Element).isInMacroExpansion()
  and not exists(e.(MacroAccess).getParentInvocation())
  and def = definitionOf(e, kind)
select e, def, kind
