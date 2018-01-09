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
 * @name Not enough memory allocated for array of pointer type
 * @description Calling 'malloc', 'calloc' or 'realloc' without allocating enough memory to contain
 *              multiple instances of the type of the pointer may result in a buffer overflow
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/suspicious-allocation-size
 * @tags reliability
 *       security
 *       external/cwe/cwe-131
 *       external/cwe/cwe-122
 */
import default

class Allocation extends FunctionCall
{
  Allocation() {
    exists(string name |
      this.getTarget().hasQualifiedName(name) and
      (name = "malloc" or name = "calloc" or name = "realloc"))
  }

  string getName() { result = this.getTarget().getQualifiedName() }

  int getSize() {
      (this.getName() = "malloc" and
      this.getArgument(0).getValue().toInt() = result)
    or
      (this.getName() = "realloc" and
      this.getArgument(1).getValue().toInt() = result)
    or
      (this.getName() = "calloc" and
      result =
        this.getArgument(0).getValue().toInt() *
        this.getArgument(1).getValue().toInt())
  }
}

predicate baseType(Allocation alloc, Type base)
{
  exists(PointerType pointer |
    pointer.getBaseType() = base and
    (
      exists(AssignExpr assign |
        assign.getRValue() = alloc and assign.getLValue().getType() = pointer)
      or
      exists(Variable v |
        v.getInitializer().getExpr() = alloc and v.getType() = pointer)
    )
  )
}

from Allocation alloc, Type base, int basesize, int allocated
where baseType(alloc, base)
  and allocated = alloc.getSize()
  // If the codebase has more than one type with the same name, check if any matches
  and not exists(int size | base.getSize() = size |
    size = 0
    or (allocated / size) * size = allocated)
  and basesize = min(base.getSize())
select alloc, "Allocated memory (" + allocated.toString() +
  " bytes) is not a multiple of the size of '" +
  base.getName() + "' (" + basesize.toString() + " bytes)."
