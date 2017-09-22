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

import semmle.code.cpp.Location
import semmle.code.cpp.Element

/**
 * A C/C++ comment.
 */
class Comment extends Locatable, @comment {
  override string toString() { result = this.getContents() }
  override Location getLocation() { comments(this,_,result) }
  string getContents() { comments(this,result,_) }
  Element getCommentedElement() { commentbinding(this,result) }
}

/**
 * A C style comment (one which starts with `/*`).
 */
class CStyleComment extends Comment {
  CStyleComment() {
    this.getContents().matches("/*%")
  }
}

/**
 * A CPP style comment (one which starts with `//`).
 */
class CppStyleComment extends Comment {
  CppStyleComment() {
    this.getContents().prefix(2) = "//"
  }
}
