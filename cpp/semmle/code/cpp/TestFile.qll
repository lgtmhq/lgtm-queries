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

import semmle.code.cpp.File

/**
 * The `gtest/gtest.h` file.
 */
private class GoogleTestHeader extends File {
  GoogleTestHeader() {
    getFileName() = "gtest.h" and
    getParent().getShortName() = "gtest"
  }
}

/**
 * A test using the Google Test library.
 */
private class GoogleTest extends MacroInvocation {
  GoogleTest() {
    // invocation of a macro from Google Test.
    this.getMacro().getFile() instanceof GoogleTestHeader
  }
} 

/**
 * The `boost/test` directory.
 */
private class BoostTestFolder extends Folder {
  BoostTestFolder() {
    getShortName() = "test" and
    getParent().getShortName() = "boost"
  }
}

/**
 * A test using the Boost Test library.
 */
private class BoostTest extends MacroInvocation {
  BoostTest() {
    // invocation of a macro from Boost Test.
    this.getMacro().getFile().getParent().getParent*() instanceof BoostTestFolder
  }
}

/**
 * The `cppunit` directory.
 */
private class CppUnitFolder extends Folder {
  CppUnitFolder() {
    getShortName() = "cppunit"
  }
}

/**
 * A class from the `cppunit` directory.
 */
private class CppUnitClass extends Class {
  CppUnitClass() {
    getFile().getParent().getParent*() instanceof CppUnitFolder and
    getNamespace().getParentNamespace*().getName() = "CppUnit"
  }
}

/**
 * A test using the CppUnit library.
 */
private class CppUnitTest extends Element {
  CppUnitTest() {
    (
      // class with a base class from cppunit. 
      this.(Class).getABaseClass*() instanceof CppUnitClass and

      // class itself is not a part of cppunit.
      not this instanceof CppUnitClass
    ) or (
      // any member function of a test is also test code
      this.(Function).getDeclaringType() instanceof CppUnitTest
    )
  }
}

/**
 * A file that contains one or more test cases.
 */
class TestFile extends File {
  TestFile() {
    exists(GoogleTest test | test.getFile() = this) or
    exists(BoostTest test | test.getFile() = this) or
    exists(CppUnitTest test | test.getFile() = this)
  }
}
