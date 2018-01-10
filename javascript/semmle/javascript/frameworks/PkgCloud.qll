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
 * Provides classes for working with [pkgcloud](https://github.com/pkgcloud/pkgcloud) applications.
 */
import javascript

module PkgCloud {

  /**
   * Holds if the `i`th argument of `invk` is an object hash for pkgcloud client creation.
   */
  private predicate takesConfigurationObject(InvokeExpr invk, int i) {
    exists (ModuleInstance mod, DataFlowNode receiver, MethodCallExpr mce, string type |
      mod.getPath() = "pkgcloud" and
      (
        type = "compute" or
        type = "storage" or
        type = "database" or
        type = "dns" or
        type = "blockstorage" or
        type = "loadbalancer" or
        type = "network" or
        type = "orchestration" or
        type = "cdn"
      ) and
      (
        // require('pkgcloud').compute
        receiver = mod.getAPropertyRead(type) or
        // require('pkgcloud').providers.joyent.compute
        exists (PropReadNode providers, PropReadNode provider, PropReadNode service |
          // Implementation details: syntactic matching
          providers = mod.getAPropertyRead("providers") and
          provider.getBase() = providers and // NB: no restriction on provider name
          service.getBase() = provider and
          service.getPropertyName() = type and
          receiver = service
        )
      ) and
      mce.getReceiver().(DataFlowNode).getALocalSource() = receiver and
      mce.getMethodName() = "createClient" and
      invk = mce and i = 0
    )
  }

  /**
   * An expression that is used for authentication through pkgcloud.
   */
  class Credentials extends CredentialsExpr {

    string kind;

    Credentials() {
      exists (string propertyName, InvokeExpr invk, int i |
        takesConfigurationObject(invk, i) and
        invk.hasOptionArgument(0, propertyName, this) |
        /*
         * Catch-all support for the following providers:
         * - Amazon
         * - Azure
         * - DigitalOcean
         * - HP Helion
         * - Joyent
         * - OpenStack
         * - Rackspace
         * - IrisCouch
         * - MongoLab
         * - MongoHQ
         * - RedisToGo
         */
        (kind = "user name" and (
          propertyName = "account" or
          propertyName = "keyId" or
          propertyName = "storageAccount" or
          propertyName = "username"
        )) or
        (kind = "password" and (
          propertyName = "key" or
          propertyName = "apiKey" or
          propertyName = "storageAccessKey" or
          propertyName = "password"
        )) or
        (kind = "token" and (
          propertyName = "token"
        ))
      )
    }

    override string getCredentialsKind() {
      result = kind
    }

  }
}