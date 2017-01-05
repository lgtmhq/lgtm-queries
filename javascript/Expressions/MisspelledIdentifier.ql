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
 * @name Misspelled identifier
 * @description Misspelled identifiers make code harder to read and understand.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       readability
 */

import javascript

// import typo database (generated from Wikipedia, licensed under CC BY-SA 3.0)
import TypoDatabase

/**
 * Typos that may be intentional or aren't interesting enough to complain about.
 */
predicate whitelisted(string wrong, string right) {
  wrong = "thru" and right = "through" or
  wrong = "cant" and right = "cannot" or
  wrong = "inbetween" and right = "between" or
  wrong = "strat" and right = "start" // often used as abbreviation for "strategy"
}

/**
 * Normalized list of typos with whitelisted entries removed. Additionally, we
 * record for every entry the first and last characters of both the typo and
 * its correction; this is used when determining prefixes and suffixes below.
 */
cached
predicate normalised_typos(string wrong, string right,
    string wrongstart, string wrongend, string rightstart, string rightend) {
  typos(wrong, right) and
  not whitelisted(wrong, right) and
  // omit very short identifiers, which are often idiosyncratic abbreviations
  wrong.length() > 3 and
  // record first and last characters
  wrongstart = wrong.charAt(0) and wrongend = wrong.charAt(wrong.length()-1) and
  rightstart = right.charAt(0) and rightend = right.charAt(right.length()-1)
}

/**
 * Extract parts of identifiers together with their offset within the identifier.
 *
 * An identifier part is a maximal substring of an identifier that falls into one
 * of the following categories:
 *
 * 1.  it consists of two or more upper-case characters;
 * 2.  it consists of a single initial upper-case character followed by one or more
 *     lower-case characters, and is not preceded by another upper-case character
 *     (and hence does not overlap with the previous case);
 * 3.  it consists entirely of lower-case characters, which are not preceded by
 *     a single upper-case character (and hence not covered by the previous case).
 *
 * For instance, `memberVariable` has two parts, `member` and
 * `Variable`, as does `member_Variable`.
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
    idPart(id, this, start) and len = this.length()
  }
}

/**
 * An identifier part that corresponds to a typo in `normalised_typos`.
 */
class WrongIdentifierPart extends IdentifierPart {
  WrongIdentifierPart() {
    normalised_typos(this, _, _, _, _, _)
  }

  /**
   * An identifier part that corresponds to a correction of this typo.
   */
  IdentifierPart getASuggestion() {
    normalised_typos(this, result, _, _, _, _)
  }

  /**
   * An identifier part that corresponds to the `i`-th correction of
   * this typo in lexicographical order (1-based).
   */
  IdentifierPart getSuggestion(int i) {
    result = rank[i](getASuggestion())
  }

  /**
   * The number of suggestions for this typo that actually appear as
   * an identifier part in the code.
   */
  int getNumSuggestions() {
    result = count(getASuggestion())
  }

  /**
   * A pretty-printed string representation of all corrections of
   * this typo that appear as identifier parts in the code.
   */
  string ppSuggestions() {
    exists (int n | n = getNumSuggestions() |
      // short-circuit the simple case
      n = 1 and result = getASuggestion() or
      // first pretty-print as a comma-separated list, then replace the last
      // comma by "or"
      result = (getSuggestion(1) + ", " + ppSuggestions(2)).regexpReplaceAll(", ([^,]++)$", " or $1")
    )
  }

  /**
   * Helper predicate: pretty-print all corrections of this typo
   * that appear as identifier parts in the code, starting with the
   * `i`-th one.
   */
  string ppSuggestions(int i) {
    exists (int n | n = getNumSuggestions() |
      i = n and result = getSuggestion(i) or
      i in [2..n-1] and result = getSuggestion(i) + ", " + ppSuggestions(i+1)
    )
  }

  predicate occursIn(Identifier id, int start, int len) {
    super.occursIn(id, start, len) and
    // throw out cases where the wrong word appears as a prefix or suffix of a right word,
    // and thus the result is most likely a false positive caused by our word segmentation algorithm
    exists (string lowerid | lowerid = id.getName().toLowerCase() |
      not exists (string right, int rightlen |
        this.prefixOf(right, rightlen) and lowerid.substring(start, start+rightlen) = right or
        this.suffixOf(right, rightlen) and lowerid.substring(start+len-rightlen, start+len) = right
      )
    )
  }

  /**
   * Is this identifier part a (proper) prefix of `right`, which is
   * a correct spelling of length `rightlen`?
   */
  predicate prefixOf(string right, int rightlen) {
    exists (string c, int wronglen |
      normalised_typos(this, _, c, _, _, _) and normalised_typos(_, right, _, _, c, _) and
      wronglen = this.length() and rightlen = right.length() and
      wronglen < rightlen and right.prefix(wronglen) = this
    )
  }

  /**
   * Is this identifier part a (proper) suffix of `right`, which is
   * a correct spelling of length `rightlen`?
   */
  predicate suffixOf(string right, int rightlen) {
    exists (string c, int wronglen |
      normalised_typos(this, _, _, c, _, _) and normalised_typos(_, right, _, _, _, c) and
      wronglen = this.length() and rightlen = right.length() and
      wronglen < rightlen and right.suffix(rightlen-wronglen) = this
    )
  }
}

from WrongIdentifierPart wrong
where // make sure we have at least one occurrence of a correction
      exists(wrong.getASuggestion()) and
      // make sure we have at least one unambiguous occurrence of the wrong word
      wrong.occursIn(_, _, _)
select wrong, "This may be a typo for " + wrong.ppSuggestions() + "."