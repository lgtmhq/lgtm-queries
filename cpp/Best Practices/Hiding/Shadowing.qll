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

import default

predicate ancestorScope(Element b1, Element b2) {
  b1.getParentScope+() = b2
}

pragma[noopt]
predicate localVariablesSameNameInNestedScopes(LocalVariable lv1, LocalVariable lv2) {
  exists(Element b1, Element b2
                            | b1 = lv1.getParentScope() and
                              not b1 instanceof Namespace and
                              lv1 instanceof LocalVariable and
                              ancestorScope(b1, b2) and
                              not b2 instanceof Namespace and
                              b2 = lv2.getParentScope() and
                              lv2 instanceof LocalVariable and
                              lv1.getName() = lv2.getName())
}

predicate shadowing(LocalVariable lv1, LocalVariable lv2) {
  localVariablesSameNameInNestedScopes(lv1, lv2) and
  exists(Location l1, Location l2 |
    l1 = lv1.getLocation() and
    l2 = lv2.getLocation() and
    (
    // variables declared later in parent scope are not shadowed
    l2.getEndLine() < l1.getStartLine()
    or (l2.getEndLine() = l1.getStartLine() and
        l2.getEndColumn() <= l1.getStartColumn())
    )
  )
}

