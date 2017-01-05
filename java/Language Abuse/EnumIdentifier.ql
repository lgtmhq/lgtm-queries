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
 * @name String 'enum' used as identifier
 * @description Using 'enum' as an identifier makes the code incompatible with Java 5 and later.
 * @kind problem
 * @problem.severity warning
 * @tags portability
 *       readability
 *       naming
 */

import java

Element elementNamedEnum() {
  result.(CompilationUnit).getPackage().getName().regexpMatch("(.*\\.|)enum(\\..*|)")
  or
  result.getName() = "enum"
}

select elementNamedEnum(), "Code using 'enum' as an identifier will not compile with a recent version of Java."
