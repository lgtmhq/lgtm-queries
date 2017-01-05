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
 * @name Confusing non-overriding of package-private method
 * @description A method that appears to override another method but does not, because the
 *              declaring classes are in different packages, is potentially confusing.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       readability
 */

import java

from Method superMethod, Method method
where overridesIgnoringAccess(method, _, superMethod, _)
  and not method.overrides(superMethod)
  and not superMethod.isPublic()
  and not superMethod.isProtected()
  and not superMethod.isPrivate()
select method, "This method does not override $@ because it is private to another package.",
  superMethod,
  superMethod.getDeclaringType().getName() + "." + superMethod.getName()
