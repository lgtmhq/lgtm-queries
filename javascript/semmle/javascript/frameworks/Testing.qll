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
 * Provides classes for working with JavaScript testing frameworks.
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
class QUnitTest extends Test, @callexpr {
  QUnitTest() {
    exists (MethodCallExpr mce | mce = this |
      mce.getReceiver().(VarAccess).getName() = "QUnit" and
      mce.getMethodName() = "test"
    )
  }
}

/**
 * A BDD-style test (as used by Mocha.js, Unit.js, Jasmine and others),
 * that is, an invocation of a function named `it` where the first argument
 * is a string and the second argument is a function.
 */
class BDDTest extends Test, @callexpr {
  BDDTest() {
    exists (CallExpr call | call = this |
      call.getCallee().(VarAccess).getName() = "it" and
      exists(call.getArgument(0).getStringValue()) and
      call.getArgument(1).(DataFlowNode).getALocalSource() instanceof Function
    )
  }
}

/**
 * A xUnit.js fact, that is, a function annotated with an xUnit.js
 * `Fact` annotation.
 */
class XUnitTest extends Test, XUnitFact {
}

private CallExpr getModuleMethodCall(string path, string methodName) {
  exists(ModuleInstance m |
    m.getPath() = path and
    result = m.getAMethodCall(methodName)
  )
}

/**
 * A tape test, that is, an invocation of `require('tape').test`.
 */
class TapeTest extends Test, @callexpr {
  TapeTest() {
    this = getModuleMethodCall("tape", "test")
  }
}

/**
 * An AVA test, that is, an invocation of `require('ava').test`.
 */
class AvaTest extends Test, @callexpr {
  AvaTest() {
    this = getModuleMethodCall("ava", "test")
  }
}

/**
 * A Cucumber test, that is, an invocation of `require('cucumber')`.
 */
class CucumberTest extends Test, @callexpr {
  CucumberTest() {
    exists(ModuleInstance m, CallExpr call |
      m.getPath() = "cucumber" and
      call.getCallee().(DataFlowNode).getALocalSource() = m and
      call.getArgument(0).(DataFlowNode).getALocalSource() instanceof Function and
      this = call
    )
  }
}
