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

/* Definitions related to the Apache Commons Exec library. */

import semmle.code.java.Type

library
class TypeCommandLine extends Class {
  TypeCommandLine() {
    hasQualifiedName("org.apache.commons.exec", "CommandLine")
  }
}

library
class MethodCommandLineParse extends Method {
  MethodCommandLineParse() {
    getDeclaringType() instanceof TypeCommandLine
    and hasName("parse")
  }
}

library
class MethodCommandLineAddArguments extends Method {
  MethodCommandLineAddArguments() {
    getDeclaringType() instanceof TypeCommandLine
    and hasName("addArguments")
  }
}
