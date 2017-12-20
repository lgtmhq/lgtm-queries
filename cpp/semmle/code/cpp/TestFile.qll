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

import semmle.code.cpp.File

/**
 * A `gtest/gtest.h` file.
 */
private class GoogleTestHeader extends File {
  GoogleTestHeader() {
    getFileName() = "gtest.h" and
    getParent().getShortName() = "gtest"
  }
}

/**
 * A test from the Google Test library.
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
 * A test from the Boost Test library.
 */
private class BoostTest extends MacroInvocation {
  BoostTest() {
    // invocation of a macro from Boost Test.
    this.getMacro().getFile().getParent().getParent*() instanceof BoostTestFolder
  }
}

/**
 * A file that contains one or more test cases.
 */
class TestFile extends File {
  TestFile() {
    exists(GoogleTest test | test.getFile() = this) or
    exists(BoostTest test | test.getFile() = this)
  }
}
