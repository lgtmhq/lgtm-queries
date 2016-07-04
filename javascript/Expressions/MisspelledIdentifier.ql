// Copyright 2016 Semmle Ltd.
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
 * @name Misspelled identifier
 * @description Misspelled identifiers make code harder to read and understand.
 * @kind problem
 * @problem.severity recommendation
 */

import javascript

// import typo database (generated from Wikipedia, licensed under CC BY-SA 3.0)
import TypoDatabase

/**
 * Typos that aren't interesting enough to complain about.
 */
predicate whitelisted(string wrong, string right) {
  wrong = "thru" and right = "through" or
  wrong = "cant" and right = "cannot" or
  wrong = "inbetween" and right = "between"
}

/**
 * Case-insensitive typo table.
 */
cached
predicate lc_typo(string wrong, string right) {
  exists (string w, string r |
    typos(w, r) and
    wrong = w.toLowerCase() and
    right = r.toLowerCase() and
    wrong != right
  ) and
  not whitelisted(wrong, right)
}

/**
 * Extract parts of identifiers together with their offset within the identifier.
 *
 * <p>
 * An identifier part is a maximal substring of an identifier that falls into one
 * of the following categories:
 * </p>
 * <ol>
 * <li>it consists of two or more upper-case characters;</li>
 * <li>it consists of a single initial upper-case character followed by one or more
 *     lower-case characters, and is not preceded by another upper-case character
 *     (and hence does not overlap with the previous case);</li>
 * <li>it consists entirely of lower-case characters, which are not preceded by
 *     a single upper-case character (and hence not covered by the previous case).</li>
 * </ol>
 *
 * <p>
 * For instance, <code>memberVariable</code> has two parts, <code>member</code> and
 * <code>Variable</code>, as does <code>member_Variable</code>.
 * </p>
 */
predicate idPart(Identifier id, string part, int offset) {
  exists (string idname, string str |
    idname = id.getName() and
    part = str.toLowerCase() |
    str = idname.regexpFind("(?<![A-Z])[A-Z]{2,}(?![A-Z])", _, offset) or
    str = idname.regexpFind("(?<![A-Z])[A-Z][a-z]+(?![a-z])", _, offset) or
    str = idname.regexpFind("(?<=^|[^A-Za-z]|[A-Z]{2,})[a-z]+(?![a-z])", _, offset)
  )
}

/**
 * An identifier part, packaged as a QL class that provides location information.
 */
class IdentifierPart extends string {
  IdentifierPart() {
    idPart(_, this, _)
  }

  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    exists (Identifier id, int start, Location l, int len | occursIn(id, start, len) and l = id.getLocation() |
      path = l.getFile().getPath() and
      sl = l.getStartLine() and sc = l.getStartColumn() + start and
      // identifiers cannot span more than one line
      el = sl and ec = sc + len - 1
    )
  }

  predicate occursIn(Identifier id, int start, int len) {
    idPart(id, this, start) and len = this.length() and
    // throw out cases where the wrong word appears as a prefix or postfix of the right word,
    // and thus the result is most likely a false positive caused by our word segmentation algorithm
    not exists (string right, int rightlen |
      lc_typo(this, right) and rightlen = right.length() and rightlen > len |
      id.getName().substring(start+len-rightlen, start+len).toLowerCase() = right or
      id.getName().substring(start, start+rightlen).toLowerCase() = right
    )
  }
}


from IdentifierPart wrong, IdentifierPart right
where lc_typo(wrong, right) and
      // make sure we have at least one unambiguous occurrence of the wrong word
      wrong.occursIn(_, _, _) and
      // omit very short identifiers, which are often idiosyncratic abbreviations
      wrong.length() > 3
select wrong, "This may be a typo for " + right + "."
