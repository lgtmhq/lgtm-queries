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

/* Definitions used by `SqlUnescaped.ql`. */

import semmle.code.java.security.ControlledString
import semmle.code.java.security.DataFlow

/**
 * A string concatenation that includes a string
 * not known to be programmer controlled.
 */
predicate builtFromUncontrolledConcat(Expr expr, Expr uncontrolled) {
  // Base case
  exists (AddExpr concat | concat = expr |
    endsInQuote(concat.getLeftOperand())
    and uncontrolled = concat.getRightOperand()
    and not controlledString(uncontrolled)
  )
  // Recursive cases
  or exists (Expr other | builtFromUncontrolledConcat(other, uncontrolled) |
    expr.(AddExpr).getAnOperand() = other
    or exists (Variable var | var.getAnAssignedValue() = other and var.getAnAccess() = expr)
  )
}

/**
 * A query built with a StringBuilder, where one of the
 * items appended is uncontrolled.
 */
predicate uncontrolledStringBuilderQuery(StringBuilderVar sbv, Expr uncontrolled) {
  // A single append that has a problematic concatenation.
  exists (MethodAccess append |
    append = sbv.getAnAppend()
    and builtFromUncontrolledConcat(append.getArgument(0), uncontrolled)
  )
  // Two calls to append, one ending in a quote, the next being uncontrolled.
  or exists (MethodAccess quoteAppend, MethodAccess uncontrolledAppend |
    sbv.getAnAppend() = quoteAppend
    and endsInQuote(quoteAppend.getArgument(0))
    and uncontrolledAppend = ((ExprStmt) quoteAppend.getEnclosingStmt().getASuccessor()).getExpr() 
    and sbv.getAnAppend() = uncontrolledAppend
    and uncontrolled = uncontrolledAppend.getArgument(0)
    and not controlledString(uncontrolled)
  )
}
