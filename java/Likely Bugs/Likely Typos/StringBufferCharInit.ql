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
 * @name Character passed to StringBuffer or StringBuilder constructor
 * @description A character value is passed to the constructor of 'StringBuffer' or 'StringBuilder'. This value will
 *              be converted to an integer and interpreted as the buffer's initial capacity, which is probably not intended.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       maintainability
 */
import java

class NewStringBufferOrBuilder extends ClassInstanceExpr {
  NewStringBufferOrBuilder() {
    exists(Class c | c = this.getConstructedType() |
      c.hasQualifiedName("java.lang", "StringBuilder") or
      c.hasQualifiedName("java.lang", "StringBuffer")
    )
  }
  
  string getName() {
    result = this.getConstructedType().getName()
  }
}

from NewStringBufferOrBuilder nsb
where nsb.getArgument(0).getType().hasName("char")
select nsb, "A character value passed to 'new " + nsb.getName() +
  "' is interpreted as the buffer capacity."
