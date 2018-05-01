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

import semmle.code.cpp.Type

/**
 * A C/C++ typedef type. See 4.9.1.
 */
class TypedefType extends UserType {

  TypedefType() { usertypes(this,_,5) }

  /** 
   * Gets the base type of this typedef type.
   */
  Type getBaseType() { typedefbase(this,result) }

  override Type getUnderlyingType() { result = this.getBaseType().getUnderlyingType() }

  override int getSize() { result = this.getBaseType().getSize() }

  override int getPointerIndirectionLevel() {
    result = this.getBaseType().getPointerIndirectionLevel()
  }

  override string explain() { result =  "typedef {" + this.getBaseType().explain() + "} as \"" + this.getName() + "\"" }

  override predicate isDeeplyConst() { this.getBaseType().isDeeplyConst() } // Just an alias

  override predicate isDeeplyConstBelow() { this.getBaseType().isDeeplyConstBelow() } // Just an alias

  override Specifier internal_getAnAdditionalSpecifier() {
    result = this.getBaseType().getASpecifier()
  }

  override predicate involvesReference() {
    getBaseType().involvesReference()
  }

  override Type resolveTypedefs() {
    result = getBaseType().resolveTypedefs()
  }

  override Type stripType() {
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

/**
 * A C++ typedef type that is directly enclosed by a class, struct or union.
 */
class NestedTypedefType extends TypedefType {
  NestedTypedefType() {
    this.isMember()
  }

  /**
   * DEPRECATED
   * Holds if this member is private.
   */
  deprecated predicate isPrivate() { this.hasSpecifier("private") }

  /**
   * DEPRECATED
   * Holds if this member is protected.
   */
  deprecated predicate isProtected() { this.hasSpecifier("protected") }

  /**
   * DEPRECATED
   * Holds if this member is public.
   */
  deprecated predicate isPublic() { this.hasSpecifier("public") }
}
