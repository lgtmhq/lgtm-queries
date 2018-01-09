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
 * @name Unsigned comparison to zero
 * @description An unsigned value is always non-negative, even if it has been
 *              assigned a negative number, so the comparison is redundant and
 *              may mask a bug because a different check was intended.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/unsigned-comparison-zero
 * @tags maintainability
 *       readability
 */
import cpp
import UnsignedGEZero

from UnsignedGEZero ugez, string msg
where unsignedGEZero(ugez, msg)
select ugez, msg
