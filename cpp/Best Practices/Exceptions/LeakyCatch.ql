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
 * @name Leaky catch
 * @description If an exception is allocated on the heap, then it should be deleted when caught.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/catch-missing-free
 * @tags efficiency
 *       correctness
 *       exceptions
 *       external/cwe/cwe-401
 */

import default

predicate doesRethrow(Function f) {
  exists(ReThrowExpr e | e.getEnclosingFunction() = f |
    not e.getEnclosingStmt().getParent*() instanceof CatchBlock
  )
  or
  exists(FunctionCall fc | fc.getEnclosingFunction() = f |
    doesRethrow(fc.getTarget())
  )
}

predicate deletesException(Expr expr, Parameter exception) {
  exists(FunctionCall fc | fc = expr |
    // Calling a delete function on the exception will free it (MFC's CException has a Delete function).
    (fc.getQualifier() = exception.getAnAccess() and fc.getTarget().getName().toLowerCase().matches("%delete%")) or
    // Passing the exception to a function might free it.
    (fc.getAnArgument() = exception.getAnAccess()) or
    // Calling a function which rethrows the current exception might cause the exception to be freed.
    doesRethrow(fc.getTarget())
  ) or
  // Calling operator delete on the exception will free it.
  exists(DeleteExpr d | d = expr |
    d.getExpr() = exception.getAnAccess()
  )
}

from CatchBlock cb
where cb.getParameter().getType().getUnderlyingType() instanceof PointerType
and not exists(Expr e | e.getEnclosingBlock().getParent*() = cb |
  deletesException(e, cb.getParameter())
)
and not is_objc_try_stmt(cb.getTryStmt())
select cb, "This catch block does not free the caught exception, thereby leaking memory."
