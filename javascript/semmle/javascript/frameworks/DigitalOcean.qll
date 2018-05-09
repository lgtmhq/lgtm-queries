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
 * Provides classes for working with [DigitalOcean](https://www.npmjs.com/package/digitalocean) applications.
 */
import javascript

module DigitalOcean {

  /**
   * An expression that is used for authentication at DigitalOcean: `digitalocean.client(<token>)`.
   */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (CallExpr mce |
        mce = DataFlow::moduleMember("digitalocean", "client").getACall().asExpr() |
        this = mce.getArgument(0) and kind = "token"
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }
}