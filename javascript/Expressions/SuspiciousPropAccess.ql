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
 * @name Property access on null or undefined
 * @description Trying to access a property of "null" or "undefined" will result
 *              in a runtime exception.
 * @kind problem
 * @problem.severity error
 * @id js/property-access-on-non-object
 * @tags correctness
 *       external/cwe/cwe-476
 * @precision high
 */

import javascript
private import semmle.javascript.dataflow.InferredTypes

/**
 * Holds if `e` is a direct reference to a const enum or namespace declaration.
 *
 * Reference to const enum members are constant-folded by the TypeScript compiler,
 * even if the surrounding namespace object would not have been initialized at that point.
 *
 * If the base expression of a property access is a namespace, we can't currently tell
 * if it is part of a const enum access, so we conservatively silence the alert in that case.
 */
predicate namespaceOrConstEnumAccess(VarAccess e) {
  exists (NamespaceDeclaration decl | e.getVariable().getADeclaration() = decl.getId())
  or
  exists (EnumDeclaration decl | e.getVariable().getADeclaration() = decl.getIdentifier() | decl.isConst())
}

from PropAccess pacc, DataFlow::AnalyzedNode base
where base.asExpr() = pacc.getBase() and
      forex (InferredType tp | tp = base.getAType() | tp = TTNull() or tp = TTUndefined()) and
      not namespaceOrConstEnumAccess(pacc.getBase())
select pacc, "The base expression of this property access is always " + base.ppTypes() + "."
