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
 * @name Imprecise assert
 * @description Using 'assertTrue' or 'assertFalse' rather than a more specific assertion can give uninformative failure messages.
 * @kind problem
 * @tags maintainability
 *       testability
 * @problem.severity recommendation
 * @sub-severity high
 * @precision very-high
 * @id py/imprecise-assert
 */

import python

/* Helper predicate for CallToAssertOnComparison class */
predicate callToAssertOnComparison(Call call, string assertName, Cmpop op) {
    call.getFunc().(Attribute).getName() = assertName
    and
    (assertName = "assertTrue" or assertName = "assertFalse")
    and
    exists(Compare cmp |
        cmp = call.getArg(0) and
        /* Exclude complex comparisons like: a < b < c */
        not exists(cmp.getOp(1)) and
        op = cmp.getOp(0)
    )
}

class CallToAssertOnComparison extends Call {

    CallToAssertOnComparison() {
        callToAssertOnComparison(this, _, _)
    }

    Cmpop getOperator() {
        callToAssertOnComparison(this, _, result) 
    }

    string getMethodName() {
        callToAssertOnComparison(this, result, _)
    }

    string getBetterName() {
        exists(Cmpop op |
            callToAssertOnComparison(this, "assertTrue", op) and
            (
                op instanceof Eq and result = "assertEqual"
                or
                op instanceof NotEq and result = "assertNotEqual"
                or
                op instanceof Lt and result = "assertLess"
                or
                op instanceof LtE and result = "assertLessEqual"
                or
                op instanceof Gt and result = "assertGreater"
                or
                op instanceof GtE and result = "assertGreaterEqual"
                or
                op instanceof In and result = "assertIn"
                or
                op instanceof NotIn and result = "assertNotIn"
                or
                op instanceof Is and result = "assertIs"
                or
                op instanceof IsNot and result = "assertIsNot"
            )
            or
            callToAssertOnComparison(this, "assertFalse", op) and
            (
                op instanceof NotEq and result = "assertEqual"
                or
                op instanceof Eq and result = "assertNotEqual"
                or
                op instanceof GtE and result = "assertLess"
                or
                op instanceof Gt and result = "assertLessEqual"
                or
                op instanceof LtE and result = "assertGreater"
                or
                op instanceof Lt and result = "assertGreaterEqual"
                or
                op instanceof NotIn and result = "assertIn"
                or
                op instanceof In and result = "assertNotIn"
                or
                op instanceof IsNot and result = "assertIs"
                or
                op instanceof Is and result = "assertIsNot"
            )
        )
    }

}


from CallToAssertOnComparison call
where 
  /* Exclude cases where an explicit message is provided*/
  not exists(call.getArg(1))
select call, call.getMethodName() + "(a " + call.getOperator().getSymbol() + " b) " +
             "cannot provide an informative message. Using " + call.getBetterName() + "(a, b) instead will give more informative messages."
