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
import semmle.code.cpp.Class

/**
 * A C/C++ structure or union.
 */
class Struct extends Class {

  Struct() { usertypes(this,_,1) or usertypes(this,_,3) }

  /** Descriptive string for a type (debug - expensive). Overridden method. See Type.explain() */
  string explain() { result =  "struct " + this.getName() }

  /** See Type.isDeeplyConst() and Type.isDeeplyConstBelow(). Internal */
  predicate isDeeplyConstBelow() { any() } // No subparts
}

/**
 * A C++ struct that is directly enclosed by a function.
 */
class LocalStruct extends Struct {
  LocalStruct() {
    isLocal()
  }
}

/**
 * A C++ nested struct. See 11.12.
 */
class NestedStruct extends Struct {
  NestedStruct() {
    this.isMember()
  }

  /** Whether this member is private. */
  predicate isPrivate() { this.hasSpecifier("private") }

  /** Whether this member is protected. */
  predicate isProtected() { this.hasSpecifier("protected") }

  /** Whether this member is public. */
  predicate isPublic() { this.hasSpecifier("public") }

}
