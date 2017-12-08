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
 * Provides a data flow configuration for reasoning about hardcoded credentials.
 */
import javascript
private import semmle.javascript.flow.Tracking
private import semmle.javascript.security.SensitiveActions

/**
 * A data flow source for hardcoded credentials.
 */
abstract class HardcodedCredentialsSource extends DataFlowNode { }

/**
 * A data flow sink for hardcoded credentials.
 */
abstract class HardcodedCredentialsSink extends DataFlowNode {
  abstract string getKind();
}

/**
 * A sanitizer for hardcoded credentials.
 */
abstract class HardcodedCredentialsSanitizer extends DataFlowNode { }

/**
 * A data flow tracking configuration for hardcoded credentials.
 */
class HardcodedCredentialsTrackingConfiguration extends FlowTrackingConfiguration {
  HardcodedCredentialsTrackingConfiguration() {
    this = "HardcodedCredentials"
  }

  override
  predicate isSource(DataFlowNode source) {
    source instanceof HardcodedCredentialsSource or
    source instanceof ConstantString
  }

  override
  predicate isSink(DataFlowNode sink) {
    sink instanceof HardcodedCredentialsSink
  }
}

/**
 * A subclass of `HardcodedCredentialsSink` that includes every `CredentialsExpr`
 * as a credentials sink.
 */
class DefaultCredentialsSink extends HardcodedCredentialsSink {
  DefaultCredentialsSink() {
    this instanceof CredentialsExpr
  }

  override string getKind() {
    result = this.(CredentialsExpr).getCredentialsKind()
  }
}
