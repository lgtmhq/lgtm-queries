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
 * @name Bad param tag
 * @description A 'param' tag that does not include a name is confusing since it is unclear which
 *              parameter it is meant to document. A 'param' tag that does not include a
 *              description is useless and should be removed.
 * @kind problem
 * @problem.severity recommendation
 * @id js/jsdoc/malformed-param-tag
 * @tags maintainability
 *       readability
 *       documentation
 * @precision very-high
 */

import javascript

from JSDocParamTag parm, string missing
where // JSDoc comments in externs files are not necessarily meant for human readers, so don't complain
      not parm.getFile().getATopLevel().isExterns() and
      (not exists(parm.getName()) and missing = "name" or
       (not exists(parm.getDescription()) or parm.getDescription().regexpMatch("\\s*")) and missing = "description")
select parm, "@param tag is missing " + missing + "."