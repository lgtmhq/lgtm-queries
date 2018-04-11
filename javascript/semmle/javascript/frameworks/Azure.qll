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
 * Provides classes for working with [Azure](https://github.com/Azure/azure-sdk-for-node) applications.
 */
import javascript

module Azure {

  /**
   * An expression that is used for authentication at Azure`.
   */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (MethodCallExpr mce, string methodName |
        (methodName = "loginWithUsernamePassword" or methodName = "loginWithServicePrincipalSecret") and
        mce = DataFlow::moduleImport("ms-rest-azure").getAMemberCall(methodName).asExpr() |
        this = mce.getArgument(0) and kind = "user name" or
        this = mce.getArgument(1) and kind = "password"
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }
}