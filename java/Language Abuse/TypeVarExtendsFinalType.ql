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
 * @name Type bound extends a final class
 * @description If 'C' is a final class, a type bound such as '? extends C'
 *              is confusing because it implies that 'C' has subclasses, but
 *              a final class has no subclasses.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/type-bound-extends-final
 * @tags maintainability
 *       readability
 *       types
 */

import java

from TypeVariable v, RefType bound
where v.getATypeBound().getType() = bound
  and bound.isFinal()
select v, "Type '" + bound + "' is final, so <" + v.getName() + " extends " + bound + "> is confusing."
