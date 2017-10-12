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

import java
import semmle.code.java.frameworks.gwt.GWT
import semmle.code.java.frameworks.j2objc.J2ObjC

/**
 * Guess if the given `JavadocText` is a line of code.
 *
 * Matches comment lines ending with `{`, `}` or `;` that do not start with `>` or `@`, but first filters out:
 *
 * - Lines containing `//`
 * - Substrings between `{@` and `}` (including the brackets themselves)
 * - HTML entities in common notation (e.g. `&gt;` and `&eacute;`)
 * - HTML entities in decimal notation (e.g. `&#768;`)
 * - HTML entities in hexadecimal notation (e.g. `&#x705F;`)
 */
private predicate looksLikeCode(JavadocText line) {
  exists(string trimmed |
    trimmed = trimmedCommentText(line) |
    (
      trimmed.matches("%;") or
      trimmed.matches("%{") or
      trimmed.matches("%}")
    ) and
    not trimmed.matches(">%") and
    not trimmed.matches("@%")
  )
}

/**
 * Remove things from comments that may look like code but are not code:
 *
 * - Lines containing `//`
 * - Substrings between `{@` and `}` (including the brackets themselves)
 * - HTML entities in common notation (e.g. `&gt;` and `&eacute;`)
 * - HTML entities in decimal notation (e.g. `&#768;`)
 * - HTML entities in hexadecimal notation (e.g. `&#x705F;`)
 */
private string trimmedCommentText(JavadocText line) {
  result = line.getText().trim()
                         .regexpReplaceAll("\\s*//.*$", "")
                         .regexpReplaceAll("\\{@[^}]+\\}", "")
                         .regexpReplaceAll("(?i)&#?[a-z0-9]{1,31};", "") 
}

/**
 * Holds if this comment contains opening and closing `<code>` or `<pre>` tags.
 */
private predicate hasCodeTags(Javadoc j) {
  exists(string tag | tag = "pre" or tag = "code" |
    j.getAChild().(JavadocText).getText().matches("%<" + tag + ">%") and
    j.getAChild().(JavadocText).getText().matches("%</"+ tag + ">%")
  )
}

/**
 * The comment immediately following `c`.
 */
private Javadoc getNextComment(Javadoc c) {
  exists(int n, File f | javadocLines(c, f, _, n) |
    javadocLines(result, f, n+1, _)
  )
}

private predicate javadocLines(Javadoc j, File f, int start, int end) {
  f = j.getFile() and
  start = j.getLocation().getStartLine() and
  end = j.getLocation().getEndLine()
}

/**
 * The number of lines that look like code in the comment `first`, or ones that follow it.
 */
private int codeCount(Javadoc first) {
  result = sum(Javadoc following |
    following = getNextComment*(first) and not hasCodeTags(following) |
    count(JavadocText line | line = following.getAChild() and looksLikeCode(line))
  )
}

/**
 * The number of lines in the comment `first`, or ones that follow it.
 */
private int anyCount(Javadoc first) {
  result = sum(Javadoc following |
    following = getNextComment*(first) and not hasCodeTags(following) |
    count(JavadocText line | line = following.getAChild() and
      not exists(string trimmed | trimmed = line.getText().trim() |
        trimmed.regexpMatch("(|/\\*|/\\*\\*|\\*|\\*/)") or
        trimmed.matches("@%")
      )
    )
  )
}

/**
 * A piece of commented-out code, identified using heuristics.
 */
class CommentedOutCode extends Javadoc {
  CommentedOutCode() {
    not exists(Javadoc prev | this = getNextComment(prev)) and
    anyCount(this) > 0 and
    ((float)codeCount(this))/((float)anyCount(this)) > 0.5 and
    not this instanceof JSNIComment and
    not this instanceof OCNIComment
  }
  
  /**
   * The number of lines that appear to be commented-out code.
   */
  int getCodeLines(){
    result = codeCount(this)
  }
  
  private Javadoc getLastSuccessor() {
    result = getNextComment*(this) and
    not exists(getNextComment(result))
  }
  
  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    path = getLocation().getFile().getAbsolutePath() and
    sl = getLocation().getStartLine() and
    sc = getLocation().getStartColumn() and
    exists(Location end | end = this.getLastSuccessor().getLocation() |
      el = end.getEndLine() and
      ec = end.getEndColumn()
    )
  }
}
