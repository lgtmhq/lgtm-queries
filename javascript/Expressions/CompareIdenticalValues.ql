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

/**
 * @name Comparison of identical values
 * @description If the same expression occurs on both sides of a comparison
 *              operator, the operator is redundant, and probably indicates a mistake.
 * @kind problem
 * @problem.severity error
 */

import Clones

from OperandComparedToSelf e
where e.same(_)
select e.getParent(), "This expression compares $@ to itself.", e, e.toString()
