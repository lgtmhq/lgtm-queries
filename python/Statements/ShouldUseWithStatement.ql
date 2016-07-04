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
 * @name Should use a 'with' statement
 * @description Using a 'try-finally' block to ensure only that a resource is closed makes code more
 *  difficult to read.
 * @kind problem
 * @problem.severity recommendation
 */

import python


predicate calls_close(Call c) {
    exists (Attribute a | c.getFunc() = a and a.getName() = "close")
}

predicate
only_stmt_in_finally(Try t, Call c) {
		exists(ExprStmt s | t.getAFinalstmt() = s and s.getValue() = c and strictcount(t.getAFinalstmt()) = 1)
}

predicate points_to_context_manager(ControlFlowNode f, ClassObject cls) {
    cls.isContextManager() and
    forex(Object obj | f.refersTo(obj) | f.refersTo(obj, cls, _))
}

from Call close, Try t, ClassObject cls
where only_stmt_in_finally(t, close) and calls_close(close) and
exists(ControlFlowNode f | f = close.getFunc().getAFlowNode().(AttrNode).getObject() |
			 points_to_context_manager(f, cls))
select close, "Instance of context-manager class $@ is closed in a finally block. Consider using 'with' statement.", cls, cls.getName()

