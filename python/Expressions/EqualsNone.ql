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
 * @name Testing equality to None
 * @description Testing whether an object is 'None' using the == operator is inefficient, there are
 *              faster methods.
 * @kind problem
 * @problem.severity recommendation
 * @tags efficiency
 *       maintainability
 */

import python

from Compare c
where c.getOp(0) instanceof Eq and c.getAComparator() instanceof None
select c, "Testing for None should use the 'is' operator."
