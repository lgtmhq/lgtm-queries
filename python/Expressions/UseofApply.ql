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
 * @name 'apply' function used
 * @description The builtin function 'apply' is obsolete and should not be used.
 * @kind problem
 * @tags changeability
 *       maintainability
 * @problem.severity warning
 * @sub-severity high
 * @precision very-high
 * @id py/use-of-apply
 */

import python

from CallNode call, ControlFlowNode func
where
major_version() = 2 and call.getFunction() = func and func.refersTo(theApplyFunction())
select call, "Call to the obsolete builtin function 'apply'."
