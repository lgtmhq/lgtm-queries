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

/** Provides classes for working with JavaScript comments. */

import javascript

/** A JavaScript source code comment. */
class Comment extends @comment, Locatable {
  override Location getLocation() {
    hasLocation(this, result)
  }

  /** Gets the toplevel element this comment belongs to. */
  TopLevel getTopLevel() {
    comments(this, _, result, _, _)
  }

  /** Gets the text of this comment, not including delimiters. */
  string getText() {
    comments(this, _, _, result, _)
  }

  /** Gets the `i`th line of comment text. */
  string getLine(int i) {
    result = getText().splitAt("\n", i)
  }

  /** Gets the next token after this comment. */
  Token getNextToken() {
    next_token(this, result)
  }

  override int getNumLines() {
    result = count(getLine(_))
  }

  override string toString() {
    comments(this, _, _, _, result)
  }

  /** Holds if this comment spans lines `start` to `end` (inclusive) in file `f`. */
  predicate onLines(File f, int start, int end) {
    exists (Location loc | loc = getLocation() |
      f = loc.getFile() and
      start = loc.getStartLine() and
      end = loc.getEndLine()
    )
  }

}

/** A line comment, that is, either an HTML comment or a `//` comment. */
class LineComment extends @linecomment, Comment {}

/** An HTML comment start/end token interpreted as a line comment. */
class HtmlLineComment extends @htmlcomment, LineComment {}

/** An HTML comment start token interpreted as a line comment. */
class HtmlCommentStart extends @htmlcommentstart, HtmlLineComment {}

/** An HTML comment end token interpreted as a line comment. */
class HtmlCommentEnd extends @htmlcommentend, HtmlLineComment {}

/** DERECATED: Use `HtmlLineComment` instead. */
deprecated class HTMLComment = HtmlLineComment;

/** DERECATED: Use `HtmlCommentStart` instead. */
deprecated class HTMLCommentStart = HtmlCommentStart;

/** DERECATED: Use `HtmlCommentEnd` instead. */
deprecated class HTMLCommentEnd = HtmlCommentEnd;

/** A `//` comment. */
class SlashSlashComment extends @slashslashcomment, LineComment {}

/** A block comment (which may be a JSDoc comment). */
class BlockComment extends @blockcomment, Comment {}

/** A C-style block comment which is not a JSDoc comment. */
class SlashStarComment extends @slashstarcomment, BlockComment {}

/** A JSDoc comment. */
class DocComment extends @doccomment, BlockComment {}