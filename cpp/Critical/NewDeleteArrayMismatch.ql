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
 * @name 'new' object freed with 'delete[]'
 * @description An object that was allocated with 'new' is being freed using 'delete[]'. Behavior in such cases is undefined and should be avoided. Use 'delete' instead.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/new-delete-array-mismatch
 * @tags reliability
 */
import NewDelete

from Expr alloc, Expr free, Expr freed
where
  allocReaches(freed, alloc, "new") and
  freeExprOrIndirect(free, freed, "delete[]")
select
  free, "This memory may have been allocated with '$@', not 'new[]'.",
  alloc, "new"
