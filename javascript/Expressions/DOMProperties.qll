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
 * Provides predicates for working with the DOM type hierarchy.
 */

import semmle.javascript.Externs

/** Holds if `et` is a root interface of the DOM type hierarchy. */
predicate isDOMRootType(ExternalType et) {
  exists (string n | n = et.getName() |
    n = "EventTarget" or n = "StyleSheet"
  )
}

/** Holds if `p` is declared as a property of a DOM class or interface. */
predicate isDOMProperty(string p) {
  exists (ExternalMemberDecl emd | emd.getName() = p |
    isDOMRootType(emd.getDeclaringType().getASupertype*())
  )
}
