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
 * @name Mismatching new/free or malloc/delete
 * @description An object that was allocated with 'malloc' or 'new' is being freed using a mismatching 'free' or 'delete'.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/new-free-mismatch
 * @tags reliability
 *       security
 *       external/cwe/cwe-401
 */
import NewDelete

/**
 * Holds if `allocKind` and `freeKind` indicate corresponding
 * types of allocation and free.
 */
predicate correspondingKinds(string allocKind, string freeKind) {
  (
    allocKind = "malloc" and
    freeKind = "free"
  ) or (
    allocKind = "new" and
    freeKind = "delete"
  )
}

from
  Expr alloc, string allocKind, string allocKindSimple,
  Expr free, Expr freed, string freeKind, string freeKindSimple
where
  allocReaches(freed, alloc, allocKind) and
  freeExprOrIndirect(free, freed, freeKind) and
  allocKindSimple = allocKind.replaceAll("[]", "") and
  freeKindSimple = freeKind.replaceAll("[]", "") and
  not correspondingKinds(allocKindSimple, freeKindSimple)
select free, "There is a " + allocKindSimple + "/" + freeKindSimple + " mismatch between this " + freeKind + " and the corresponding $@.", alloc, allocKind
