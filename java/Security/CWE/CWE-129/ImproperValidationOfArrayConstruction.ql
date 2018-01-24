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
 * @name Improper validation of user-provided size used for array construction
 * @description Using unvalidated external input as the argument to a construction of an array can lead to index out of bound exceptions.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/improper-validation-of-array-construction
 * @tags security
 *       external/cwe/cwe-129
 */

import java
import ArraySizing

from RemoteUserInput source, ArrayCreationExpr arrayCreation, CheckableArrayAccess arrayAccess
where arrayAccess.canThrowOutOfBoundsDueToEmptyArray(source, arrayCreation)
select arrayAccess.getIndexExpr(),
  "The $@ is accessed here, but the array is initialized using $@ which may be zero.",
  arrayCreation, "array",
  source, "User-provided value"
