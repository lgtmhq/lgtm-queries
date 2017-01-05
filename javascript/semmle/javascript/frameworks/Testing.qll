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
 * A library for working with testing frameworks for JavaScript.
 */

import javascript
import semmle.javascript.frameworks.xUnit
import semmle.javascript.frameworks.TestingCustomizations

/**
 * A syntactic construct that represents a single test.
 */
abstract class Test extends Locatable {
}

/**
 * A QUnit test, that is, an invocation of `QUnit.test`.
 */
class QUnitTest extends Test, MethodCallExpr {
  QUnitTest() {
    getReceiver().(VarAccess).getName() = "QUnit" and
    getMethodName() = "test"
  }

  string toString() { result = MethodCallExpr.super.toString() }
}

/**
 * A BDD-style test (as used by Mocha.js, Unit.js, Jasmine and others),
 * that is, an invocation of a function named `it` where the first argument
 * is a string and the second argument is a function.
 */
class BDDTest extends Test, CallExpr {
  BDDTest() {
    getCallee().(VarAccess).getName() = "it" and
    exists(getArgument(0).getStringValue()) and
    getArgument(1).(DataFlowNode).getASource() instanceof Function
  }

  string toString() { result = CallExpr.super.toString() }
}

/**
 * A xUnit.js fact, that is, a function annotated with an xUnit.js
 * `Fact` annotation.
 */
class XUnitTest extends Test, XUnitFact {
}
