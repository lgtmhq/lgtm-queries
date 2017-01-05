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
 * @name TestCase implements tearDown but doesn't call super.tearDown()
 * @description A JUnit 3.8 test method that overrides 'tearDown' but does not call 'super.tearDown'
 *              may result in subsequent tests failing, or allow the current state to persist and
 *              affect subsequent tests.
 * @kind problem
 * @problem.severity warning
 * @tags testability
 *       maintainability
 *       frameworks/junit
 */
import java

from TearDownMethod m1
where m1.fromSource() and
      not m1.getDeclaringType().isAbstract() and
      not exists(TearDownMethod m2 | m1.overrides(m2) and m1.callsSuper(m2))
select m1, "TestCase implements tearDown but doesn't call super.tearDown()."
