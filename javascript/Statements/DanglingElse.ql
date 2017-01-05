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
 * @name Misleading indentation of dangling 'else'
 * @description The 'else' clause of an 'if' statement should be aligned with the 'if' it belongs to.
 * @kind problem
 * @problem.severity warning
 * @tags changeability
 *       readability
 */

import javascript

/**
 * A helper function for computing the "semantic indentation" of a token.
 *
 * The semantic indentation of a token `tk` is defined as follows:
 * 
 *   1. If `tk` is the first token on its line, its semantic indentation is its start column.
 *   2. Otherwise, if `tk` is an `if` token preceded by an `else` token, or an `else` token
 *      preceded by an `}` token, its semantic indentation is the semantic indentation of that
 *      preceding token.
 *   3. Otherwise, the token has no semantic indentation.
 *
 * The intuitive idea is that the `if` token of an `else if` branch is assigned the indentation
 * of the preceding `else` token, or even that of the `}` token preceding the `else`, but only
 * if these tokens are on the same line as the `if`.
 */
int semanticIndent(Token tk) {
  exists (Token prev | prev = tk.getPreviousToken() |
    if prev.getLocation().getEndLine() != tk.getLocation().getStartLine() then
      result = tk.getLocation().getStartColumn()
    else
      exists (string tkVal, string prevVal |
        tkVal = tk.getValue() and prevVal = prev.getValue() |
        (tkVal = "if" and prevVal = "else" or
         tkVal = "else" and prevVal = "}") and
        result = semanticIndent(prev)
      )
  )
}

int ifIndent(IfStmt i) {
  result = semanticIndent(i.getIfToken())
}

int elseIndent(IfStmt i) {
  result = semanticIndent(i.getElseToken())
}

from IfStmt outer, IfStmt inner, Token outerIf, Token innerIf, Token innerElse, int outerIndent
where inner = outer.getThen().getAChildStmt*() and
      outerIf = outer.getIfToken() and outerIndent = ifIndent(outer) and
      innerIf = inner.getIfToken() and innerElse = inner.getElseToken() and
      outerIndent < ifIndent(inner) and
      outerIndent = elseIndent(inner) and
      not outer.getTopLevel().isMinified()
select innerElse, "This else branch belongs to $@, but its indentation suggests it belongs to $@.",
                innerIf, "this if statement", outerIf, "this other if statement"