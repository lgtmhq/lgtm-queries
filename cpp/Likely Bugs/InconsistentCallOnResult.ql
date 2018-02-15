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
 * @name Inconsistent operation on return value
 * @description A function is called, and the same operation is usually performed on the return value - for example, free, delete, close etc. However, in some cases it is not performed. These unusual cases may indicate misuse of the API and could cause resource leaks.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/inconsistent-call-on-result
 * @tags reliability
 *       correctness
 *       statistical
 *       non-attributable
 *       external/cwe/cwe-252
 */
import default

predicate exclude(Function f) {
  exists(string name | name = f.getName() |
    name.toLowerCase().matches("get%") or
    name.matches("strto%")
  )
}

predicate checkExpr(Expr e, string operation, Variable v) {
  exists(FunctionCall fc | fc = e and not exclude(fc.getTarget()) |
    fc.getTarget().getName() = operation and
    (fc.getAnArgument() = v.getAnAccess() or fc.getQualifier() = v.getAnAccess())
  )
  or
  exists(DeleteExpr del | del = e |
    del.getExpr() = v.getAnAccess() and
    operation = "delete"
  )
  or
  exists(DeleteArrayExpr del | del = e |
    del.getExpr() = v.getAnAccess() and
    operation = "delete[]"
  )
}

predicate checkedFunctionCall(FunctionCall fc, string operation) {
  relevantFunctionCall(fc, _) and
  exists (Variable v, Expr check | v.getAnAssignedValue() = fc |
    checkExpr(check, operation, v) and
    check != fc
  )
}

predicate relevantFunctionCall(FunctionCall fc, Function f) {
  fc.getTarget() = f and
  exists (Variable v | v.getAnAssignedValue() = fc) and
  not okToIgnore(fc)
}

predicate okToIgnore(FunctionCall fc) {
  fc.isInMacroExpansion()
}

predicate functionStats(Function f, string operation, int used, int total, int percentage) {
  exists(PointerType pt | pt.getATypeNameUse() = f.getADeclarationEntry()) and
  used = strictcount(FunctionCall fc | checkedFunctionCall(fc, operation) and f = fc.getTarget()) and
  total = strictcount(FunctionCall fc | relevantFunctionCall(fc, f)) and
  percentage = used * 100 / total
}

from FunctionCall unchecked, Function f, string operation, int percent
where
  relevantFunctionCall(unchecked, f) and
  not checkedFunctionCall(unchecked, operation) and
  functionStats(f, operation, _, _, percent) and
  percent >= 70
  and unchecked.getFile().getFullName().matches("%fbcode%")
  and not unchecked.getFile().getFullName().matches("%\\_build%")
select unchecked, "After " + percent.toString() + "% of calls to " + f.getName() + " there is a call to " + operation + " on the return value. The call may be missing in this case."
