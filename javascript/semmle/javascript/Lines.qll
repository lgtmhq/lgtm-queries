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

import javascript

/** A line of text (code, comment, or whitespace) in a source file. */
class Line extends @line, Locatable {
  /** Get the toplevel element this line belongs to. */
  TopLevel getTopLevel() {
    lines(this, result, _, _)
  }

  /** Get the text of this line, excluding the terminator character(s). */
  string getText() {
    lines(this, _, result, _)
  }

  /** Get the terminator character(s) of this line.
   *
   * <p>
   * This predicate may return:
   * </p>
   *
   * <ul>
   * <li> the empty string if this line is the last line in a file
   *      and there is no line terminator after it;</li>
   * <li> a single-character string containing the character '\n' (newline),
   *     '\r' (carriage return), '\u2028' (Unicode character LINE SEPARATOR)
   *     or '\u2029' (Unicode character PARAGRAPH SEPARATOR);</li>
   * <li> the two-character string "\r\n" (carriage return followed by newline).</li>
   * </ul>
   */
  string getTerminator() {
    lines(this, _, _, result)
  }

  /** Get the indentation character used by this line.
   *
   * <p>
   * The indentation character of a line is defined to be the whitespace character
   * c such that the line starts with one or more instances of c, followed by a
   * non-whitespace character.
   * </p>
   *
   * <p>
   * If the line does not start with a whitespace character, or with a mixture of
   * different whitespace characters, its indentation character is undefined.
   * </p>
   */
  string getIndentChar() {
    result = getText().regexpCapture("(\\s)\\1*\\S.*", 1)
  }

  /** Return a string representation of the line, which is simply its text. */
  string toString() {
    result = getText()
  }
}
