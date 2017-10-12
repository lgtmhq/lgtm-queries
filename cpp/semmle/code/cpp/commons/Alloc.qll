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

import default

/**
 * A library routine that allocates memory.
 */
predicate allocationFunction(Function f)
{
  exists(string name |
    f.hasQualifiedName(name) and
    (
      name = "malloc" or
      name = "calloc" or
      name = "realloc" or
      name = "strdup" or
      name = "wcsdup" or
      name = "_strdup" or
      name = "_wcsdup" or
      name = "_mbsdup"
    )
  )
}

/**
 * A call to a library routine that allocates memory.
 */
predicate allocationCall(FunctionCall fc)
{
  allocationFunction(fc.getTarget()) and
  (
    // realloc(ptr, 0) only frees the pointer
    fc.getTarget().hasQualifiedName("realloc") implies
    not fc.getArgument(1).getValue() = "0"
  )
}

/**
 * A library routine that frees memory.
 */
predicate freeFunction(Function f, int argNum)
{
  exists(string name |
    f.hasQualifiedName(name) and
    (
      (name = "free" and argNum = 0) or
      (name = "realloc" and argNum = 0)
    )
  )
}

/**
 * A call to a library routine that frees memory.
 */
predicate freeCall(FunctionCall fc, Expr arg)
{
  exists(int argNum |
    freeFunction(fc.getTarget(), argNum) and
    arg = fc.getArgument(argNum)
  )
}

/**
 * Is e some kind of allocation or deallocation (`new`, `alloc`, `realloc`, `delete`, `free` etc)?
 */
predicate isMemoryManagementExpr(Expr e) {
  isAllocationExpr(e) or isDeallocationExpr(e)
}

/**
 * Is e an allocation from stdlib.h (`malloc`, `realloc` etc)?
 */
predicate isStdLibAllocationExpr(Expr e)
{
  allocationCall(e)
}

/**
 * Is e some kind of allocation (`new`, `alloc`, `realloc` etc)?
 */
predicate isAllocationExpr(Expr e) {
  allocationCall(e)
  or e instanceof NewExpr
  or e instanceof NewArrayExpr
}

/**
 * Is e some kind of allocation (`new`, `alloc`, `realloc` etc) with a fixed size?
 */
predicate isFixedSizeAllocationExpr(Expr allocExpr, int size) {
exists (FunctionCall fc, string name | fc = allocExpr and name = fc.getTarget().getName() |
  (
      name = "malloc" and
      size = fc.getArgument(0).getValue().toInt()
    ) or (
      name = "alloca" and
      size = fc.getArgument(0).getValue().toInt()
    ) or (
      name = "calloc" and
      size = fc.getArgument(0).getValue().toInt() * fc.getArgument(1).getValue().toInt()
    ) or (
      name = "realloc" and
      size = fc.getArgument(1).getValue().toInt() and
      size > 0 // realloc(ptr, 0) only frees the pointer
    )
  ) or (
    size = allocExpr.(NewExpr).getAllocatedType().getSize()
  ) or (
    size = allocExpr.(NewArrayExpr).getAllocatedType().getSize()
  )
}

/**
 * Is e some kind of deallocation (`delete`, `free`, `realloc` etc)?
 */
predicate isDeallocationExpr(Expr e) {
  freeCall(e, _)
  or e instanceof DeleteExpr
  or e instanceof DeleteArrayExpr
}

/**
 * Holds if `sizeof(s)` occurs as part of the parameter of a dynamic
 * memory allocation (`malloc`, `realloc`, etc.), except if `sizeof(s)`
 * only ever occurs as the immediate parameter to allocations.
 *
 * For example, holds for `s` if it occurs as
 * ```
 * malloc(sizeof(s) + 100 * sizeof(char))
 * ```
 * but not if it only ever occurs as
 * ```
 * malloc(sizeof(s))
 * ```
*/
private predicate isDynamicallyAllocatedWithDifferentSize(Class s) {
  exists(SizeofTypeOperator sof |
    sof.getTypeOperand().getUnspecifiedType() = s |
    // Check all ancestor nodes except the immediate parent for
    // allocations.
    isStdLibAllocationExpr(sof.getParent().(Expr).getParent+())
  )
}

/**
 * Holds if `v` is a member variable of `c` that looks like it might be variable sized in practice.  For
 * example:
 * ```
 * struct myStruct { // c
 *   int amount;
 *   char data[1]; // v
 * };
 * ```
 * This requires that `v` is an array of size 0 or 1, and `v` is the last member of `c`.  In addition,
 * there must be at least one instance where a `c` pointer is allocated with additional space. 
 */
predicate memberMayBeVarSize(Class c, MemberVariable v) {
  exists(int i |
    i = max(int j | exists(c.getMember(j)) | j) and
    v = c.getMember(i) and
    v.getType().getUnspecifiedType().(ArrayType).getSize() <= 1
  ) and
  isDynamicallyAllocatedWithDifferentSize(c)
}
