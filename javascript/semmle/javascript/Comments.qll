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

import javascript

/** A source code comment. */
class Comment extends @comment, Locatable {
  /** Get the toplevel element this comment belongs to. */
  TopLevel getTopLevel() {
    comments(this, _, result, _, _)
  }

  /** Get the text of this comment, not including delimiters. */
  string getText() {
    comments(this, _, _, result, _)
  }
  
  /** Get the ith line of comment text. */
  string getLine(int i) {
  	result = getText().splitAt("\n", i)
  }

  /** Get the next token after this comment. */
  Token getNextToken() {
    next_token(this, result)
  }

  int getNumLines() {
  	result = count(getLine(_))
  }
  
  string toString() {
    comments(this, _, _, _, result)
  }
}

/** A line comment, i.e., either an HTML comment or a BCPL-style comment. */
class LineComment extends @linecomment, Comment {}

/** An HTML comment start/end token interpreted as a line comment. */
class HTMLComment extends @htmlcomment, LineComment {}

/** An HTML comment start token interpreted as a line comment. */
class HTMLCommentStart extends @htmlcommentstart, HTMLComment {}

/** An HTML comment end token interpreted as a line comment. */
class HTMLCommentEnd extends @htmlcommentend, HTMLComment {}

/** A BCPL-style line comment. */
class SlashSlashComment extends @slashslashcomment, LineComment {}

/** A block comment (which may be a doc comment). */
class BlockComment extends @blockcomment, Comment {}

/** A C-style block comment which isn't a doc comment. */
class SlashStarComment extends @slashstarcomment, BlockComment {}

/** A doc comment. */
class DocComment extends @doccomment, BlockComment {}