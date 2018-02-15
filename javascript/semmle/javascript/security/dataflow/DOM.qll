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

/** Holds if `e` could refer to the `location` property of a DOM node. */
predicate isLocation(Expr e) {
  exists (PropAccess pacc | pacc = e |
    isDomValue(pacc.getBase()) and pacc.getPropertyName() = "location"
  )
  or
  e.accessesGlobal("location")
}

/** Holds if `nd` could refer to the `document` object. */
predicate isDocument(DataFlowNode nd) {
  nd.getALocalSource().(Expr).accessesGlobal("document")
}

/** Holds if `e` could refer to the document URL. */
predicate isDocumentURL(Expr e) {
  exists (Expr base, string propName | e.(PropAccess).accesses(base, propName) |
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
  e.accessesGlobal("location")
}

/**
 * Holds if `pacc` accesses a part of `document.location` that is
 * not considered user-controlled, that is, anything except
 * `href`, `hash` and `search`.
 */
predicate isSafeLocationProperty(PropAccess pacc) {
  exists (Expr loc, string prop |
    isLocation(loc) and pacc.accesses(loc, prop) |
    prop != "href" and prop != "hash" and prop != "search"
  )
}

/**
 * A call to a DOM method.
 */
class DomMethodCallExpr extends MethodCallExpr {
  DomMethodCallExpr() {
    isDomValue(getReceiver())
  }

  /**
   * Holds if `arg` is an argument that is interpreted as HTML.
   */
  predicate interpretsArgumentsAsHTML(Expr arg){
    exists (int argPos, string name |
      arg = getArgument(argPos) and
      name = getMethodName() |
      // individual signatures:
      name = "write" or
      name = "writeln" or
      name = "insertAdjacentHTML" and argPos = 0 or
      name = "insertAdjacentElement" and argPos = 0 or
      name = "insertBefore" and argPos = 0 or
      name = "createElement" and argPos = 0 or
      name = "appendChild" and argPos = 0 or
      name = "setAttribute" and argPos = 0
    )
  }
}

/**
 * An assignment to a property of a DOM object.
 */
class DomPropWriteNode extends Assignment {

  PropAccess lhs;

  DomPropWriteNode (){
    lhs = getLhs() and
    isDomValue(lhs.getBase())
  }

  /**
   * Holds if the assigned value is interpreted as HTML.
   */
  predicate interpretsValueAsHTML(){
    lhs.getPropertyName() = "innerHTML" or
    lhs.getPropertyName() = "outerHTML"
  }
}

/**
 * Holds if `e` is an access to `window.localStorage` or `window.sessionStorage`.
 */
private predicate isWebStorage(Expr e) {
  e.accessesGlobal(any(string name | name = "localStorage" or name = "sessionStorage"))
}

/**
 * A value written to web storage, like localStorage or sessionStorage.
 */
class WebStorageWrite extends Expr {
  WebStorageWrite(){
    // an assignment to `window.localStorage[someProp]`
    exists(PropWriteNode pwn |
      isWebStorage(pwn.getBase()) and
      this = pwn.getRhs()) or
    // an invocation of `window.localStorage.setItem`
    exists (MethodCallExpr mce |
      isWebStorage(mce.getReceiver()) and
      mce.getMethodName() = "setItem" and
      this = mce.getArgument(1)
    )
  }
}
