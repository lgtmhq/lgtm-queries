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
 * @name String concatenation in loop
 * @description Concatenating strings in loops has quadratic performance.
 * @kind problem
 * @tags efficiency
 *       maintainability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 * @id py/string-concatenation-in-loop
 */

import python

predicate string_concat_in_loop(BinaryExpr b) {
    b.getOp() instanceof Add
    and
    exists(SsaVariable d, SsaVariable u, BinaryExprNode add, ClassObject str_type |
           add.getNode() = b and d = u.getAnUltimateDefinition() |
           d.getDefinition().(DefinitionNode).getValue() = add and u.getAUse() = add.getAnOperand() and
           add.getAnOperand().refersTo(_, str_type, _) and
           (str_type = theBytesType() or str_type = theUnicodeType())
    )
}


from BinaryExpr b, Stmt s
where string_concat_in_loop(b) and s.getASubExpression() = b
select s, "String concatenation in a loop is quadratic in the number of iterations."
