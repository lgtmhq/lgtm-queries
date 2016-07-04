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
 * @name Class should be a context manager
 * @description Making a class a context manager allows instances to be used in a 'with' statement.
 *              This improves resource handling and code readability.
 * @kind problem
 * @problem.severity recommendation
 */

import python

from ClassObject c
where not c.isC() and not c.isContextManager() and exists(c.declaredAttribute("__del__"))
select c, "Class " + c.getName() + " implements __del__ (presumably to release some resource). Consider making it a context manager."
