// Copyright 2016 Semmle Ltd.
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
 * @name Test case has no tests
 * @description A test case class whose test methods are not recognized by JUnit 3.8 as valid
 *              declarations is not used.
 * @kind problem
 * @problem.severity recommendation
 */
import default

// `suite()` methods in `TestCase`s also count as test methods.
class SuiteMethod extends Method {
	SuiteMethod() {
		this.getDeclaringType() instanceof JUnit38TestClass and
		this.isPublic() and
		this.isStatic() and 
		this.hasNoParameters()
	}
}

from JUnit38TestClass j
where j.fromSource() and
			not j.getAnAnnotation().getType().hasQualifiedName("org.junit", "Ignore") and
			not j.isAbstract() and
			not exists(TestMethod t | t.getDeclaringType() = j) and
			not exists(SuiteMethod s | s.getDeclaringType() = j)
select j, "TestCase has no tests."
