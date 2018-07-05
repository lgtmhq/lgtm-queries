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
 * Provides a class for modelling expressions used to supply
 * credentials.
 */

import javascript

/**
 * An expression whose value is used to supply credentials such
 * as a user name, a password, or a key.
 */
abstract class CredentialsExpr extends Expr {
  /**
   * Gets a description of the kind of credential this expression is used as,
   * such as `"user name"`, `"password"`, `"key"`.
   */
  abstract string getCredentialsKind();
}
