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
 * @name Bad check for overflow of integer addition
 * @description Checking for overflow of integer addition by comparing
 *              against one of the arguments of the addition does not work
 *              when the result of the addition is automatically promoted
 *              to a larger type.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @id cpp/bad-addition-overflow-check
 * @tags reliability
 *       correctness
 */

import cpp
import BadAdditionOverflowCheck

from RelationalOperation cmp, AddExpr a
where badAdditionOverflowCheck(cmp, a)
select cmp, "Bad overflow check."
