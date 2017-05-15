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
 * @name Missing space in string concatenation
 * @description Joining constant strings into a longer string where
 *              two words are concatenated without a separating space
 *              usually indicates a text error.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @tags readability
 */

import javascript

Expr rightChild(Expr e) {
  result = e.(ParExpr).getExpression() or
  result = e.(AddExpr).getRightOperand()
}

Expr leftChild(Expr e) {
  result = e.(ParExpr).getExpression() or
  result = e.(AddExpr).getLeftOperand()
}

from AddExpr e, StringLiteral l, StringLiteral r, string word
where // l and r are appended together
      l = rightChild*(e.getLeftOperand()) and
      r = leftChild*(e.getRightOperand()) and

      // `l + r` is of the form `... word" + "word2...`, possibly including some
      // punctuation after `word`.
      // Only the first character of `word2` is matched, whereas `word` is matched
      // completely to distinguish grammatical punctuation after which a space is
      // needed, and intra-identifier punctuation in, for example, a qualified name.
      word = l.getValue().regexpCapture(".* (([-A-Za-z/'\\.:,]*[a-zA-Z]|[0-9]+)[\\.:,!?']*)", 1) and
      r.getValue().regexpMatch("[a-zA-Z].*") and
      not word.regexpMatch(".*[,\\.:].*[a-zA-Z].*[^a-zA-Z]")
select l, "This string appears to be missing a space after '" + word + "'."