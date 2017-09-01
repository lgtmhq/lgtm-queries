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
 * @name Print an array
 * @description Directly printing an array, without first converting the array to a string,
 *              produces unreadable results.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id java/print-array
 * @tags maintainability
 */
import java

from Method println, int i, Expr arr
where arr.getType() instanceof Array and
      arr = println.getAReference().getArgument(i) and
      println.hasName("println") and
      not println.getParameter(i).getType() instanceof Array
select arr, "Implicit conversion from Array to String."
