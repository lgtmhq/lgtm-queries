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

import semmle.code.cpp.Type

/**
 * A C/C++ typedef type. See 4.9.1.
 */
class TypedefType extends UserType {

  TypedefType() { usertypes(this,_,5) }

  /** the base type of this typedef type */
  Type getBaseType() { typedefbase(this,result) }

  /** the underlying type of this type */
  Type getUnderlyingType() { result = this.getBaseType().getUnderlyingType() }

  int getSize() { result = this.getBaseType().getSize() }

  /** the pointer indirection level of this type */
  int getPointerIndirectionLevel() {
    result = this.getBaseType().getPointerIndirectionLevel()
  }

  // Overriding, see Type
  string explain() { result =  "typedef {" + this.getBaseType().explain() + "} as \"" + this.getName() + "\"" }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConst() { this.getBaseType().isDeeplyConst() } // Just an alias

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConstBelow() } // Just an alias

  override Specifier internal_getAnAdditionalSpecifier() {
    result = this.getBaseType().getASpecifier()
  }

  /**
   * Recursively checks whether the specified type involves a reference.
   */
  predicate involvesReference() {
    getBaseType().involvesReference()
  }

  /**
   * Recursively resolves any typedefs in a type. For example, given typedef C T, this would resolve
   * const T&amp; to const C&amp;. Note that this will only work if the resolved type actually appears on its
   * own elsewhere in the program.
   */
  Type resolveTypedefs() {
    result = getBaseType().resolveTypedefs()
  }

  /**
   * Strips a type, removing pointers, references and cv-qualifiers, and resolving typedefs.
   * For example, given typedef const C&amp; T, stripType(T) = C.
   */
  Type stripType() {
    result = getBaseType().stripType()
  }
}

/**
 * A C++ typedef type that is directly enclosed by a function.
 */
class LocalTypedefType extends TypedefType {
  LocalTypedefType() {
    isLocal()
  }
}

class NestedTypedefType extends TypedefType {
  NestedTypedefType() { member(_,_,this) }

  /** Whether this member is private. */
  predicate isPrivate() { this.hasSpecifier("private") }

  /** Whether this member is protected. */
  predicate isProtected() { this.hasSpecifier("protected") }

  /** Whether this member is public. */
  predicate isPublic() { this.hasSpecifier("public") }

}
