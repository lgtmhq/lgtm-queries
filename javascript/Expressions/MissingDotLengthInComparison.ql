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
 * @name Missing '.length' in comparison
 * @description Two variables are being compared using a relational operator, but one is also used
 *             to index into the other, suggesting a ".length" is missing from the comparison.
 * @kind problem
 * @problem.severity warning
 * @id js/missing-dot-length-in-comparison
 * @precision high
 * @tags correctness
 */

import javascript

/**
 * Holds for a comparison and index expression with the same operands,
 * such as `base < index` and `base[index]`.
 *
 * Such expressions make contradictory assumptions about the types of `base` and `index`.
 */
predicate contradictoryAccess(RelationalComparison compare, IndexExpr lookup) {
  exists (SsaVariable base, SsaVariable index |
    base != index and
    compare.hasOperands(base.getAUse(), index.getAUse()) and
    lookup.getBase() = base.getAUse() and
    lookup.getIndex() = index.getAUse())
  or
  // We allow `base` to be a global, since globals rarely undergo radical type changes
  // that depend on local control flow.
  // We could do the same for `index`, but it rarely matters for the pattern we are looking for.
  sameIndex(compare, lookup) and
  exists (GlobalVariable base |
    compare.getAnOperand() = base.getAnAccess() and
    lookup.getBase() = base.getAnAccess())
}

predicate sameIndex(RelationalComparison compare, IndexExpr lookup) {
  exists (SsaVariable index |
    compare.getAnOperand() = index.getAUse() and
    lookup.getIndex() = index.getAUse())
}

predicate relevantBasicBlocks(ReachableBasicBlock b1, ReachableBasicBlock b2) {
  contradictoryAccess(b1.getANode(), b2.getANode())
}

predicate sameBranch(ReachableBasicBlock b1, ReachableBasicBlock b2) {
  relevantBasicBlocks(b1, b2) and
  (b1 = b2 or b1.strictlyDominates(b2) or b2.strictlyDominates(b1))
}

from RelationalComparison compare, IndexExpr lookup
where contradictoryAccess(compare, lookup)
  and sameBranch(compare.getBasicBlock(), lookup.getBasicBlock())
select compare, "Missing .length in comparison, or erroneous $@.", lookup, "index expression"
