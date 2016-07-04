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
 * @name Array constant vulnerable to change
 * @description Array constants are mutable and can be changed by malicious code or by accident.
 * @kind problem
 * @problem.severity warning
 * @cwe 582
 */
import java

predicate nonEmptyArrayLiteralOrNull(Expr e) {
  exists(ArrayCreationExpr arr | arr = e |
    // Array initializer expressions such as `{1, 2, 3}`.
    // Array is empty if the initializer expression is empty.
    exists(Expr arrayValue | arrayValue = arr.getInit().getAnInit())
    or
    // Array creation with dimensions (but without initializers).
    // Empty if the first dimension is 0.
    exists (Expr dim | dim = arr.getDimension(0) |
      not (dim.(CompileTimeConstantExpr).getIntValue() = 0)
    )
  )
  or 
  e instanceof NullLiteral
  or
  exists(ConditionalExpr cond | cond = e |
    nonEmptyArrayLiteralOrNull(cond.getTrueExpr()) and
    nonEmptyArrayLiteralOrNull(cond.getFalseExpr())
  )
}      

from Field f
where f.isPublic() and
      f.isStatic() and
      f.isFinal() and
      f.getType() instanceof Array and
      f.fromSource() and
      forall(AssignExpr a | a.getDest() = f.getAnAccess() |
        nonEmptyArrayLiteralOrNull(a.getSource())
      )
select f, "The array constant " + f.getName() + " is vulnerable to mutation."
