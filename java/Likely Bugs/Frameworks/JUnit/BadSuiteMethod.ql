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
 * @name Bad suite method
 * @description A 'suite' method in a JUnit 3.8 test that does not match the expected signature is not
 *              detected by JUnit.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/wrong-junit-suite-signature
 * @tags testability
 *       maintainability
 *       frameworks/junit
 */
import java

from TypeJUnitTestCase junitTestCase, TypeJUnitTest junitTest, Method m
where m.hasName("suite") and
      m.hasNoParameters() and
      m.getDeclaringType().hasSupertype+(junitTestCase) and
      (   not m.isPublic()
       or not m.isStatic()
       or (not m.getReturnType().(RefType).getASupertype*() = junitTest))
select m, "Bad declaration for suite method."
