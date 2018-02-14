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
 * Provides classes for performing local (intra-procedural) and
 * global (inter-procedural) data flow analyses.
 */

import java

module DataFlow4 {
  import semmle.code.java.dataflow.internal.DataFlowImpl4

  /**
   * This class exists to prevent mutual recursion between the user-overridden
   * member predicates of `Configuration` and the rest of the data-flow library.
   * Good performance cannot be guaranteed in the presence of such recursion, so
   * it should be replaced by using more than one copy of the data flow library.
   * Four copies are available: `DataFlow` through `DataFlow4`.
   */
  private abstract
  class ConfigurationRecursionPrevention extends Configuration {
    bindingset[this]
    ConfigurationRecursionPrevention() { any() }

    override predicate hasFlow(Node source, Node sink) {
      strictcount(Node n | this.isSource(n)) < 0
      or
      strictcount(Node n | this.isSink(n)) < 0
      or
      strictcount(Node n1, Node n2 | this.isAdditionalFlowStep(n1, n2)) < 0
      or
      super.hasFlow(source, sink)
    }
  }
}
