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
 * Reading from the environment, for example with 'getenv'.
 */

import cpp

/**
 * An expression that reads from an environment variable.
 */
class EnvironmentRead extends Expr {
  EnvironmentRead() {
    readsEnvironment(this, _)
  }

  /**
   * The name of the environment variable.
   */
  string getEnvironmentVariable() {
    // Conveniently, it's always the first argument to the call
    this.(Call).getArgument(0).(TextLiteral).getValue() = result
  }

  /**
   * A very short description of the source, suitable for use in
   * an error message.
   */
  string getSourceDescription() {
    readsEnvironment(this, result)
  }
}


private predicate readsEnvironment(Expr read, string sourceDescription) {
  exists(FunctionCall call, string name |
    read = call and
    call.getTarget().hasGlobalName(name) and
    (name = "getenv" or name = "secure_getenv" or name = "_wgetenv") and
    sourceDescription = name) or
  exists(MessageExpr getObjectKey, MessageExpr getEnviron |
    read = getObjectKey and
    getObjectKey.getTarget().getQualifiedName().matches("NSDictionary%::-objectForKey:") and
    getObjectKey.getQualifier() = getEnviron and
    getEnviron.getTarget().getQualifiedName().matches("NSProcessInfo%:-environment") and
    sourceDescription = "NSProcessInfo")
}
