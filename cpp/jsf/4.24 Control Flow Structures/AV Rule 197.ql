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
 * @name Avoid floats in for loops
 * @description Floating point variables should not be used as loop counters. For loops are best suited to simple increments and termination conditions; while loops are preferable for more complex uses.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/loop-variable-float
 * @tags reliability
 *       readability
 */
import default

from LoopCounter lc
where lc.getUnderlyingType() instanceof FloatingPointType
select lc, "Floating point variables should not be used as loop counters."
