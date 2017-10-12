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
 * Provides predicates for reasoning about DOM types.
 */

import javascript

/** Holds if `tp` is one of the roots of the DOM type hierarchy. */
predicate isDomRootType(ExternalType tp) {
  exists (string qn | qn = tp.getQualifiedName() | qn = "EventTarget" or qn = "StyleSheet")
}

/** A global variable whose declared type extends a DOM root type. */
class DOMGlobalVariable extends GlobalVariable {
  DOMGlobalVariable() {
    exists (ExternalVarDecl d | d.getQualifiedName() = this.getName() |
      isDomRootType(d.getTypeTag().getTypeDeclaration().getASupertype*())
    )
  }
}

/** Holds if `nd` could hold a value that comes from the DOM. */
predicate isDomValue(DataFlowNode nd) {
  nd.(VarAccess).getVariable() instanceof DOMGlobalVariable or
  isDomValue(nd.(PropAccess).getBase()) or
  isDomValue(nd.getALocalSource())
}

/** Holds if `nd` could refer to the `location` property of a DOM node. */
predicate isLocation(DataFlowNode location) {
  exists (PropAccess pacc | pacc = location |
    isDomValue(pacc.getBase()) and pacc.getPropertyName() = "location"
  )
  or
  location.(Expr).accessesGlobal("location")
}

/** Holds if `nd` could refer to the `document` object. */
predicate isDocument(DataFlowNode nd) {
  nd.getALocalSource().(Expr).accessesGlobal("document")
}

/** Holds if `nd` could refer to the document URL. */
predicate isDocumentURL(DataFlowNode nd) {
  exists (Expr base, string propName | nd.(PropAccess).accesses(base, propName) |
    isDocument(base) and
    (propName = "documentURI" or
     propName = "documentURIObject" or
     propName = "location" or
     propName = "referrer" or
     propName = "URL")
    or
    isDomValue(base) and propName = "baseUri"
  )
  or
  nd.(Expr).accessesGlobal("location")
}

/**
 * Holds if `pacc` accesses a part of `document.location` that is
 * not considered user-controlled, that is, anything except
 * `href`, `hash` and `search`.
 */
predicate isSafeLocationProperty(PropAccess pacc) {
  exists (DataFlowNode loc, string prop |
    isLocation(loc) and pacc.accesses(loc, prop) |
    prop != "href" and prop != "hash" and prop != "search"
  )
}
