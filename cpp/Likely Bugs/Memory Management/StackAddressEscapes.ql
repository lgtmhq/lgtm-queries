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
 * @name Local variable address stored in non-local memory
 * @description Storing the address of a local variable in non-local
 *              memory can cause a dangling pointer bug if the address
 *              is used after the function returns.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/stack-address-escape
 * @tags reliability
 */
import cpp
import semmle.code.cpp.dataflow.StackAddress

/**
 * Find assignments where the rhs might be a stack pointer and the lhs is
 * not a stack variable. Such assignments might allow a stack address to
 * escape.
 */
predicate stackAddressEscapes(AssignExpr assignExpr, Expr source, boolean isLocal) {
  stackPointerFlowsToUse(assignExpr.getRValue(), _, source, isLocal)  and
  not stackReferenceFlowsToUse(assignExpr.getLValue(), _, _, _)
}

from Expr use, Expr source, boolean isLocal, string msg, string srcStr
where
  stackAddressEscapes(use, source, isLocal) and
  if isLocal = true
    then (msg = "A stack address ($@) may be assigned to a non-local variable." and
          srcStr = "source")
    else (msg = "A stack address which arrived via a $@ may be assigned to a non-local variable." and
          srcStr = "parameter")
select
  use, msg, source, srcStr
