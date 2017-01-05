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
 * @name Illegal raise
 * @description Raising a non-exception object or type will result in a TypeError being raised instead.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 *       types
 */

import python
import Raising

from Raise r, ClassObject t
where type_or_typeof(r, t, _) and not t.isLegalExceptionType() and not t.failedInference()
select r, "Illegal class '" + t.getName() + "' raised; will result in a TypeError being raised instead."

