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
 * @name Non-exception in 'except' clause
 * @description An exception handler specifying a non-exception type will never handle any exception.
 * @kind problem
 * @tags reliability
 *       correctness
 *       types
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/useless-except
 */

import python

from ExceptFlowNode ex, Object t, ClassObject c, ControlFlowNode origin, string what
where ex.handledException(t, c, origin) and 
(
  exists(ClassObject x | x = t |
    not x.isLegalExceptionType() and
    not x.failedInference() and
    what = "class '" + x.getName() + "'"
  )
  or
  not t instanceof ClassObject and
  what = "instance of '" + c.getName() + "'"
)

select ex.getNode(), "Non-exception $@ in exception handler which will never match raised exception.", origin, what

