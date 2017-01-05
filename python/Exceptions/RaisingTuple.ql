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
 * @name Raising a tuple
 * @description Raising a tuple will result in all but the first element being discarded
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 */

import python
import Raising

from Raise r, ControlFlowNode origin
where type_or_typeof(r, theTupleType(), origin) and
major_version() = 2 /* Raising a tuple is a type error in Python 3, so is handled by the IllegalRaise query. */

select r, "Raising $@ will result in the first element (recursively) being raised and all other elements being discarded.", origin, "a tuple"