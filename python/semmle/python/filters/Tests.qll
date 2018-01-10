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

import python

abstract class TestScope extends Scope {}

// don't extend Class directly to avoid ambiguous method pain
class UnitTestClass extends TestScope {
    UnitTestClass() {
        exists(ClassObject c | 
            this = c.getPyClass() and 
            c.getASuperType() = theUnitTestPackage().getAttribute(_)
        )
    }
}

PackageObject theUnitTestPackage() {
    result.getName() = "unittest"
}

abstract class Test extends TestScope {}

class UnitTestFunction extends Test {

    UnitTestFunction() {
        this.getScope+() instanceof UnitTestClass
        and
        this.(Function).getName().matches("test%")
    }
}

class PyTestFunction extends Test {

    PyTestFunction() {
        exists(Module pytest | pytest.getName() = "pytest") and
        this.(Function).getName().matches("test%")
    }

}

class NoseTestFunction extends Test {

    NoseTestFunction() {
        exists(Module nose | nose.getName() = "nose") and
        this.(Function).getName().matches("test%")
    }

}
