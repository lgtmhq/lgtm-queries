// Copyright 2016 Semmle Ltd.
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
 * A library for working with Java modifiers.
 */

import Element

/**
 * Whether element `e` has a modifier named `m`.
 *
 * DEPRECATED: use `Modifiable.hasModifier` instead.
 */
deprecated
predicate hasStrModifier(Element e, string m) {
  e.(Modifiable).hasModifier(m)
}

/**
 * Whether element `e` has the modifier `static`.
 *
 * DEPRECATED: use `Modifiable.isStatic` instead.
 */
deprecated
predicate isStatic(Element e) {
  e.(Modifiable).hasModifier("static")
}

/**
 * Whether element `e` has the modifier `public`.
 *
 * DEPRECATED: use `Modifiable.isPublic` instead.
 */
deprecated
predicate isPublic(Element e) {
	e.(Modifiable).hasModifier("public")
}

/**
 * Whether element `e` has the modifier `protected`.
 *
 * DEPRECATED: use `Modifiable.isProtected` instead.
 */
deprecated
predicate isProtected(Element e) {
	e.(Modifiable).hasModifier("protected")
}

/**
 * Whether element `e` has the modifier `private`.
 *
 * DEPRECATED: use `Modifiable.isPrivate` instead.
 */
deprecated
predicate isPrivate(Element e) {
  e.(Modifiable).hasModifier("private")
}

/**
 * Whether callable `e` is package protected, i.e. it is neither public nor private nor protected.
 *
 * DEPRECATED: use `Member.isPackageProtected` instead.
 */
deprecated
predicate isCallablePackageProtected(Callable e) {
  not e.(Modifiable).hasModifier("private") and
  not e.(Modifiable).hasModifier("protected") and
  not e.(Modifiable).hasModifier("public")
}

/**
 * Whether element `e` is package protected, i.e. it is neither public nor private nor protected.
 *
 * DEPRECATED: use `Member.isPackageProtected` instead.
 */
deprecated
predicate isPackageProtected(Element e) {
  not e.(Modifiable).hasModifier("private") and
  not e.(Modifiable).hasModifier("protected") and
  not e.(Modifiable).hasModifier("public")
}

/** A modifier such as `private`, `static` or `abstract`. */
class Modifier extends Element, @modifier {
  /** The element to which this modifier applies. */
  Element getElement() { hasModifier(result,this) }
}

/** An element of the Java syntax tree that may have a modifier. */
abstract class Modifiable extends Element {
  /**
   * Whether this element has modifier `m`.
   *
   * For most purposes, the more specialized predicates `isAbstract`, `isPublic`, etc.
   * should be used, which also take implicit modifiers into account.
   * For instance, non-default instance methods in interfaces are implicitly
   * abstract, so `isAbstract()` will hold for them even if `hasModifier("abstract")`
   * does not.
   */
  predicate hasModifier(string m) {
    modifiers(getAModifier(), m)
  }

  /** Whether this element has no modifier. */
  predicate hasNoModifier() { not hasModifier(this,_) }

  /** A modifier of this element. */
  Modifier getAModifier() { this = result.getElement() }

  /** Whether this element has an `abstract` modifier or is implicitly abstract. */
  predicate isAbstract() { hasModifier("abstract") }

  /** Whether this element has a `static` modifier or is implicitly static. */
  predicate isStatic() { hasModifier("static") }

  /** Whether this element has a `final` modifier or is implicitly final. */
  predicate isFinal() { hasModifier("final") }

  /** Whether this element has a `public` modifier or is implicitly public. */
  predicate isPublic() { hasModifier("public") }

  /** Whether this element has a `protected` modifier. */
  predicate isProtected() { hasModifier("protected") }

  /** Whether this element has a `private` modifier or is implicitly private. */
  predicate isPrivate() { hasModifier("private") }

  /** Whether this element has a `volatile` modifier. */
  predicate isVolatile() { hasModifier("volatile") }

  /** Whether this element has a `synchronized` modifier. */
  predicate isSynchronized() { hasModifier("synchronized") }

  /** Whether this element has a `native` modifier. */
  predicate isNative() { hasModifier("native") }

  /** Whether this element has a `default` modifier. */
  predicate isDefault() { this.hasModifier("default") }

  /** Whether this element has a `transient` modifier. */
  predicate isTransient() { this.hasModifier("transient") }

  /** Whether this element has a `strictfp` modifier. */
  predicate isStrictfp() { this.hasModifier("strictfp") }
}
