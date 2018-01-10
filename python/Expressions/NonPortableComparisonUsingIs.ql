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
 * @name Non-portable comparison using is when operands support __eq__
 * @description Comparison using 'is' when equivalence is not the same as identity and may not be portable.
 * @kind problem
 * @tags portability
 *       maintainability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 * @id py/comparison-using-is-non-portable
 */

import python
import IsComparisons

from Compare comp, Cmpop op, ClassObject c
where invalid_portable_is_comparison(comp, op, c) and
exists(Expr sub | 
    sub = comp.getASubExpression() |
    cpython_interned_constant(sub) and
    not universally_interned_constant(sub)
)
select comp, "The result of this comparison with '" + op.getSymbol() + "' may differ between implementations of Python."