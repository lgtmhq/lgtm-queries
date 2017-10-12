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
 * @name Overloaded assignment does not return 'this'
 * @description An assignment operator should return a reference to *this. Both the standard library types and the built-in types behave in this manner.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/assignment-does-not-return-this
 * @tags reliability
 *       readability
 *       language-features
 */
import default

predicate callOnThis(FunctionCall fc) {
  // `this->f(...)`
  fc.getQualifier() instanceof ThisExpr or

  // `(*this).f(...)`
  fc.getQualifier().(PointerDereferenceExpr).getChild(0) instanceof ThisExpr
}

predicate pointerThis(Expr e) {
  e instanceof ThisExpr or

  // `f(...)`
  // (includes `this = ...`, where `=` is overloaded so a `FunctionCall`)
  exists(FunctionCall fc | fc = e and callOnThis(fc) |
    exists(fc.getTarget().getBlock()) implies returnsPointerThis(fc.getTarget())
  ) or

  // `this = ...` (where `=` is not overloaded, so an `AssignExpr`) 
  pointerThis(e.(AssignExpr).getLValue())
}

predicate dereferenceThis(Expr e) {
  pointerThis(e.(PointerDereferenceExpr).getChild(0)) or

  // `f(...)`
  // (includes `*this = ...`, where `=` is overloaded so a `FunctionCall`)
  exists(FunctionCall fc | fc = e and callOnThis(fc) |
    exists(fc.getTarget().getBlock()) implies returnsDereferenceThis(fc.getTarget())
  ) or

  // `*this = ...` (where `=` is not overloaded, so an `AssignExpr`) 
  dereferenceThis(e.(AssignExpr).getLValue())
}

predicate returnsPointerThis(Function f) {
  forex(ReturnStmt s | s.getEnclosingFunction() = f |
    // `return this`
    pointerThis(s.getExpr())
  )
}

predicate returnsDereferenceThis(Function f) {
  forex(ReturnStmt s | s.getEnclosingFunction() = f |
    // `return *this`
    dereferenceThis(s.getExpr())
  )
}

predicate assignOperatorWithWrongType(Operator op, string msg) {
  op.hasName("operator=")
  and exists(op.getBlock())
  and exists(Class c |
        c = op.getDeclaringType()
    and op.getType() = c
    and msg = "Assignment operator in class " + c.getName() + " should have return type " + c.getName() + "&. Otherwise a copy is created at each call."
  )
}

predicate assignOperatorWithWrongResult(Operator op, string msg) {
  op.hasName("operator=")
  and not returnsDereferenceThis(op)
  and exists(op.getBlock())
  and not op.getType() instanceof VoidType
  and not assignOperatorWithWrongType(op, _)
  and msg = "Assignment operator in class " + op.getDeclaringType().getName() + " does not return a reference to *this."
}

// Applies to all assignment operators, not just a copy assignment operator

from Operator op, string msg
where assignOperatorWithWrongType(op, msg)
  or assignOperatorWithWrongResult(op, msg)
select op, msg
