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
 * @name Array in String append
 * @description Appending an array to a string, without first converting the array to a string, 
 *              produces unreadable results.
 * @kind problem
 * @problem.severity warning
 */
import default

from AddExpr ae, Expr arr
where ae.getType() instanceof TypeString and
      arr = ae.getAnOperand() and
      arr.getType() instanceof Array
select arr, "Implicit conversion of array to String in append."
