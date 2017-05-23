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
 * @name JSDoc tag for non-existent parameter
 * @description A JSDoc 'param' tag that refers to a non-existent parameter is confusing
 *              and may indicate badly maintained code.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       readability
 *       documentation
 * @precision high
 */

import javascript

from Function f, JSDoc doc, JSDocParamTag tag, string parmName
where doc = f.getDocumentation() and
      tag = doc.getATag() and
      parmName = tag.getName() and
      tag.documentsSimpleName() and
      not exists (f.getParameterByName(parmName)) and
      // don't report functions without declared parameters that use `arguments`
      not (f.getNumParameter() = 0 and f.usesArgumentsObject()) and
      // don't report a violation in ambiguous cases
      strictcount(JSDoc d | d = f.getDocumentation() and d.getATag() instanceof JSDocParamTag) = 1
select tag, "@param tag refers to non-existent parameter " + parmName + "."