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

/** Library for recognizing commented-out code. */

import semmle.javascript.Comments

/** Get a line in comment c that looks like commented-out code? */
private string getALineOfCommentedOutCode(Comment c) {
  result = c.getLine(_) and
  // line ends with ';', '{', or '}', optionally followed by a comma,
  ((result.regexpMatch(".*[;{}],?\\s*") and
    // but it doesn't look like a JSDoc-like annotation
    not result.regexpMatch(".*@\\w+\\s*\\{.*\\}\\s*") and
    // and it does not contain three consecutive words (which is uncommon in code)
    not result.regexpMatch("[^'\\\"]*\\w\\s++\\w++\\s++\\w[^'\\\"]*")) or
  // line is part of a block comment and ends with something that looks
  // like a line comment; character before '//' must not be ':' to
  // avoid matching URLs
  (not c instanceof SlashSlashComment and
   result.regexpMatch("(.*[^:]|^)//.*[^/].*")) or
  // similar, but don't be fooled by '//// this kind of comment' and
  // '//// this kind of comment ////'
  (c instanceof SlashSlashComment and
   result.regexpMatch("/*([^/].*[^:]|[^:/])//.*[^/].*") and
   // exclude externalization comments
   not result.regexpMatch(".*\\$NON-NLS-\\d+\\$.*")))
}

/** Comments containing code examples should be disregarded. */
private predicate containsCodeExample(Comment c) {
  exists (string text | text = c.getText() |
    text.matches("%<pre>%</pre>%") or
    text.matches("%<code>%</code>%") or
    text.matches("%@example%") or
    text.matches("%```%")
  )
}

/** Auxiliary predicate: comment c spans lines start to end in file f. */
private predicate commentOnLines(Comment c, File f, int start, int end) {
  exists (Location loc | loc = c.getLocation() |
    f = loc.getFile() and
    start = loc.getStartLine() and
    end = loc.getEndLine()
  )
}

/**
 * Return comment that belongs to a run of consecutive comments starting
 * with c, where c itself contains commented-out code, but the comment
 * preceding it (if any) does not.
 */
private Comment getCommentInRun(File f, Comment c) {
  exists (int n |
    commentOnLines(c, f, n, _) and
    countCommentedOutLines(c) > 0 and
    not exists (Comment d | commentOnLines(d, f, _, n-1) |
      countCommentedOutLines(d) > 0
    )
  ) and
  (result = c or
   exists (Comment prev, int n |
     prev = getCommentInRun(f, c) and
     commentOnLines(prev, f, _, n) and
     commentOnLines(result, f, n+1, _)
   )
  )
}

/**
 * Return comment that follows c in a run of consecutive comments and
 * does not contain a code example.
 */
private Comment getRelevantCommentInRun(Comment c) {
  result = getCommentInRun(_, c) and not containsCodeExample(result)
}

/** How many lines in comment c look like commented-out code? */
private int countCommentedOutLines(Comment c) {
  result = count(getALineOfCommentedOutCode(c))
}

/** How many non-blank lines does c have? */
private int countNonBlankLines(Comment c) {
	result = count(string line | line = c.getLine(_) and not line.regexpMatch("\\s*"))
}

/**
 * How many lines in comment c and subsequent comments look like
 * commented-out code?
 */
private int countCommentedOutLinesInRun(Comment c) {
	result = sum(Comment d | d = getRelevantCommentInRun(c) | countCommentedOutLines(d))
}

/** How many non-blank lines are there in c and subsequent comments? */
private int countNonBlankLinesInRun(Comment c) {
	result = sum(Comment d | d = getRelevantCommentInRun(c) | countNonBlankLines(d))
}

/**
 * Comments containing a high percentage of lines that look like commented-out code.
 *
 * To avoid false positives, we treat runs of consecutive comments as one comment by
 * means of the getNextComment predicate.
 */
class CommentedOutCode extends Comment {
  CommentedOutCode(){
    exists(int codeLines, int nonBlankLines |
      countCommentedOutLines(this) > 0 and
      not exists(Comment prev | this = getCommentInRun(_, prev) and this != prev) and
      nonBlankLines = countNonBlankLinesInRun(this) and
      codeLines = countCommentedOutLinesInRun(this) and
      nonBlankLines > 0 and
      2*codeLines > nonBlankLines
    )
  }
  
  int getNumCodeLines() {
    result = countCommentedOutLinesInRun(this)
  }
  
  int getNumNonBlankLines() {
  	result = countNonBlankLinesInRun(this)
  }
  
  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    exists (Location loc, File f | loc = getLocation() and f = loc.getFile() |
      path = f.getPath() and
      sl = loc.getStartLine() and
      sc = loc.getStartColumn() and
      exists(Location last |
        last = getCommentInRun(f, this).getLocation() and
        last.getEndLine() = max(getCommentInRun(f, this).getLocation().getEndLine()) |
        el = last.getEndLine() and
        ec = last.getEndColumn()
      )
    )
  }
}

