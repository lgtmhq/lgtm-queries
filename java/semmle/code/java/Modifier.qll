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
 * Provides classes and predicates for working with Java modifiers.
 */

import Element

/** A modifier such as `private`, `static` or `abstract`. */
class Modifier extends Element, @modifier {
  /** The element to which this modifier applies. */
  Element getElement() { hasModifier(result,this) }
}

/** An element of the Java syntax tree that may have a modifier. */
abstract class Modifiable extends Element {
  /**
   * Holds if this element has modifier `m`.
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

  /** Holds if this element has no modifier. */
  predicate hasNoModifier() { not hasModifier(this,_) }

  /** A modifier of this element. */
  Modifier getAModifier() { this = result.getElement() }

  /** Holds if this element has an `abstract` modifier or is implicitly abstract. */
  predicate isAbstract() { hasModifier("abstract") }

  /** Holds if this element has a `static` modifier or is implicitly static. */
  predicate isStatic() { hasModifier("static") }

  /** Holds if this element has a `final` modifier or is implicitly final. */
  predicate isFinal() { hasModifier("final") }

  /** Holds if this element has a `public` modifier or is implicitly public. */
  predicate isPublic() { hasModifier("public") }

  /** Holds if this element has a `protected` modifier. */
  predicate isProtected() { hasModifier("protected") }

  /** Holds if this element has a `private` modifier or is implicitly private. */
  predicate isPrivate() { hasModifier("private") }

  /** Holds if this element has a `volatile` modifier. */
  predicate isVolatile() { hasModifier("volatile") }

  /** Holds if this element has a `synchronized` modifier. */
  predicate isSynchronized() { hasModifier("synchronized") }

  /** Holds if this element has a `native` modifier. */
  predicate isNative() { hasModifier("native") }

  /** Holds if this element has a `default` modifier. */
  predicate isDefault() { this.hasModifier("default") }

  /** Holds if this element has a `transient` modifier. */
  predicate isTransient() { this.hasModifier("transient") }

  /** Holds if this element has a `strictfp` modifier. */
  predicate isStrictfp() { this.hasModifier("strictfp") }
}
