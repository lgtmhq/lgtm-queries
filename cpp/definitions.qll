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

/**
 * Provides classes and predicates related to jump-to-definition links
 * in the code viewer.
 */

import cpp

/**
 * Any element that might be the source or target of a jump-to-definition
 * link.
 *
 * In some cases it is preferable to modify locations (the
 * `hasLocationInfo()` predicate) so that they are short, and
 * non-overlapping with other locations that might be highlighted in
 * the LGTM interface.
 *
 * We need to give locations that may not be in the database, so
 * we use `hasLocationInfo()` rather than `getLocation()`.
 */
class Top extends Element {
  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/help/ql/locations).
   */
  predicate hasLocationInfo(string filepath,
                            int startline, int startcolumn,
                            int endline, int endcolumn) {
    // Element
    exists(Location l | l = this.getLocation()
                    and filepath    = l.getFile().getAbsolutePath()
                    and startline   = l.getStartLine()
                    and startcolumn = l.getStartColumn()
                    and endline     = l.getEndLine()
                    and endcolumn   = l.getEndColumn())
    or
    // File (does not have a `.getLocation()`)
    exists(File f | f = this
                and filepath    = f.getAbsolutePath()
                and startline   = 1
                and startcolumn = 1
                and endline     = 1
                and endcolumn   = 1)
  }
}

/**
 * A `MacroAccess` with a `hasLocationInfo` predicate.
 *
 * This has a location that covers only the name of the accessed
 * macro, not its arguments (which are included by `MacroAccess`'s
 * `getLocation()`).
 */
class MacroAccessWithHasLocationInfo extends Top {
  MacroAccessWithHasLocationInfo() {
    this instanceof MacroAccess
  }

  override
  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    exists(MacroAccess ma, Location l |
           ma = this
       and l = ma.getLocation()
       and path = l.getFile().getAbsolutePath()
       and sl = l.getStartLine()
       and sc = l.getStartColumn()
       and el = sl
       and ec = sc + ma.getMacroName().length() - 1)
  }
}

/**
 * An `Include` with a `hasLocationInfo` predicate.
 *
 * This has a location that covers only the name of the included
 * file, not the `#include` text or whitespace before it.
 */
class IncludeWithHasLocationInfo extends Top {
  IncludeWithHasLocationInfo() {
    this instanceof Include
  }

  override
  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    exists(Include i, Location l |
      i = this and
      l = i.getLocation() and
      path = l.getFile().getAbsolutePath() and
      sl = l.getEndLine() and
      sc = l.getEndColumn() + 1 - i.getIncludeText().length() and
      el = l.getEndLine() and
      ec = l.getEndColumn()
    )
  }
}

/**
 * Gets an element, of kind `kind`, that element `e` uses, if any.
 *
 * The `kind` is a string representing what kind of use it is:
 *  - `"M"` for function and method calls
 *  - `"T"` for uses of types
 *  - `"V"` for variable accesses
 *  - `"X"` for macro accesses
 *  - `"I"` for import / include directives
 */
Top definitionOf(Top e, string kind) {
  (
    (
      // call -> function called
      kind = "M" and
      result = e.(Call).getTarget() and
      not e.(Expr).isCompilerGenerated()
    ) or (
      // access -> function, variable or enum constant accessed
      kind = "V" and
      result = e.(Access).getTarget() and
      not e.(Expr).isCompilerGenerated()
    ) or (
      // macro access -> macro accessed
      kind = "X" and
      result = e.(MacroAccess).getMacro()
    ) or (
      // class derivation -> base class
      kind = "T" and
      result = e.(ClassDerivation).getBaseClass()
    ) or (
      // include -> included file
      kind = "I" and
      result = e.(Include).getIncludedFile() and

      // exclude `#include` directives containing macros
      not exists(MacroInvocation mi, Location l1, Location l2 |
        l1 = e.(Include).getLocation() and
        l2 = mi.getLocation() and
        l1.getFile() = l2.getFile() and
        l1.getStartLine() = l2.getStartLine()
        // (an #include directive must be always on it's own line)
      )
    )
  ) and (
    // exclude things inside macro invocations, as they will overlap
    // with the macro invocation.
    not e.(Element).isInMacroExpansion() and

    // exclude nested macro invocations, as they will overlap with
    // the top macro invocation.
    not exists(e.(MacroAccess).getParentInvocation()) and

    // exclude results from template instantiations, as:
    // (1) these dependencies will often be caused by a choice of
    // template parameter, which is non-local to this part of code; and
    // (2) overlapping results pointing to different locations will
    // be very common.
    // It's possible we could allow a subset of these dependencies
    // in future, if we're careful to ensure the above don't apply.
    not e.isFromTemplateInstantiation(_)
  )
}
