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
 * @name Wrong NaN comparison
 * @description A comparison with 'NaN' using '==' or '!=' will always yield the same result
 *              and is unlikely to be intended.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @id java/comparison-with-nan
 * @tags correctness
 */
import java

predicate nanField(Field f) {
  f.getDeclaringType() instanceof FloatingPointType and
  f.hasName("NaN")
}

from EqualityTest eq, Field f, string classname
where eq.getAnOperand() = f.getAnAccess() and nanField(f) and f.getDeclaringType().hasName(classname)
select eq, "This comparison will always yield the same result since 'NaN != NaN'. Consider using " + classname + ".isNaN instead"
