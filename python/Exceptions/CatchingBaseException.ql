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
 * @name Except block handles 'BaseException'
 * @description Handling 'BaseException' means that system exits and keyboard interrupts may be mis-handled.
 * @kind problem
 * @tags reliability
 *       readability
 *       convention
 * @problem.severity recommendation
 * @sub-severity high
 * @precision very-high
 * @id py/catch-base-exception
 */

import python

predicate doesnt_reraise(ExceptStmt ex) {
    ex.getAFlowNode().getBasicBlock().reachesExit()
}

predicate catches_base_exception(ExceptStmt ex) {
     ex.getType().refersTo(theBaseExceptionType())
     or
     not exists(ex.getType())
}

from ExceptStmt ex
where catches_base_exception(ex) and
doesnt_reraise(ex)
select ex, "Except block directly handles BaseException."
