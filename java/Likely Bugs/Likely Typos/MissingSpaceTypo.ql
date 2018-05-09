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
 * @name Missing space in string literal
 * @description Joining strings at compile-time to construct a string literal
 *              so that two words are concatenated without a separating space
 *              usually indicates a text error.
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id java/missing-space-in-concatenation
 * @tags readability
 */
import java

class SourceStringLiteral extends StringLiteral {
  SourceStringLiteral() {
    this.getCompilationUnit().fromSource()
  }
}

from SourceStringLiteral s, string word
where
  // Match ` word" + "word2` taking punctuation after `word` into account.
  // `word2` is only matched on the first character whereas `word` is matched
  // completely to distinguish grammatical punctuation after which a space is
  // needed, and intra-identifier punctuation in, for example, a fully
  // qualified java class name.
  s.getLiteral().regexpCapture(".* (([-A-Za-z/'\\.:,]*[a-zA-Z]|[0-9]+)[\\.:,;!?']*)\"[^\"]*\\+[^\"]*\"[a-zA-Z].*", 1) = word
  and not word.regexpMatch(".*[,\\.:].*[a-zA-Z].*[^a-zA-Z]")
select s, "This string appears to be missing a space after '" + word + "'."
