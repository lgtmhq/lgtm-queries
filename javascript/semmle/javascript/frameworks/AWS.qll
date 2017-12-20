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
 * Provides classes for working with [AWS-SDK](https://aws.amazon.com/sdk-for-node-js/) applications.
 */
import javascript

module AWS {

  /**
   * Holds if the `i`th argument of `invk` is an object hash for `AWS.Config`.
   */
  private predicate takesConfigurationObject(InvokeExpr invk, int i) {
    exists (ModuleInstance mod |
      mod.getPath() = "aws-sdk" |
      exists (CallExpr call, PropReadNode update |
        // `AWS.config.update(nd)`
        update.getBase() = mod.getAPropertyRead("config") and
        update.getPropertyName() = "update" and
        call.getCallee() = update and
        invk = call and i = 0
      ) or
      exists (NewExpr ne |
        ne.getCallee() = mod.getAPropertyRead("Config") |
        // `new AWS.Config(nd)`
        invk = ne and i = 0 or
        exists (MethodCallExpr mce |
          // `var config = new AWS.Config(...); config.update(nd);`
          mce.getReceiver().(DataFlowNode).getALocalSource() = ne and
          mce.getMethodName() = "update" and
          invk = mce and i = 0
        )
      )
    )
  }

  /**
   * An expression that is used as an AWS config value: `{ accessKeyId: <user>, secretAccessKey: <password>}`.
   */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (string prop, InvokeExpr invk, int i |
        takesConfigurationObject(invk, i) and
        invk.hasOptionArgument(i, prop, this) |
        prop = "accessKeyId" and kind = "user name" or
        prop = "secretAccessKey" and kind = "password"
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }
}