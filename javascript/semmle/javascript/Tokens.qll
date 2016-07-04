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

import Locations
import Files
import Stmt

/** A token occurring in a piece of source code. */
class Token extends Locatable, @token {
  /** The toplevel syntactic structure to which this token belongs. */
  TopLevel getTopLevel() {
  	tokeninfo(this, _, result, _, _)
  }
  
  /** The index of the token inside its toplevel structure. */
  int getIndex() {
    tokeninfo(this, _, _, result, _)
  }
  
  /** The source text of this token. */
  string getValue() {
  	tokeninfo(this, _, _, _, result)
  }
  
  /** The token following this token inside the same toplevel structure, if any. */
  Token getNextToken() {
  	this.getTopLevel() = result.getTopLevel() and
  	this.getIndex() + 1 = result.getIndex()
  }
  
  /** The token preceding this token inside the same toplevel structure, if any. */
  Token getPreviousToken() {
  	result.getNextToken() = this
  }
  
  string toString() {
    result = getValue()
  }
}

/** An end-of-file token. */
class EOFToken extends Token, @token_eof {}

/** A null literal token. */
class NullLiteralToken extends Token, @token_null_literal {}

/** A Boolean literal token. */
class BooleanLiteralToken extends Token, @token_boolean_literal {}

/** A numeric literal token. */
class NumericLiteralToken extends Token, @token_numeric_literal {}

/** A string literal token. */
class StringLiteralToken extends Token, @token_string_literal {}

/** A regular expression literal token. */
class RegularExpressionToken extends Token, @token_regular_expression {}

/** An identifier token. */
class IdentifierToken extends Token, @token_identifier {}

/** A keyword token. */
class KeywordToken extends Token, @token_keyword {}

/** A punctuator token. */
class PunctuatorToken extends Token, @token_punctuator {}
