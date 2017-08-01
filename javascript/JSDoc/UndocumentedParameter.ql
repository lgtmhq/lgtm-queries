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
 * @name Undocumented parameter
 * @description If some parameters of a function are documented by JSDoc 'param' tags while others
 *              are not, this may indicate badly maintained code.
 * @kind problem
 * @problem.severity recommendation
 * @id js/jsdoc/missing-parameter
 * @tags maintainability
 *       readability
 *       documentation
 * @precision very-high
 */

import javascript

from Function f, Parameter parm, Variable v, JSDoc doc
where parm = f.getAParameter() and
      doc = f.getDocumentation() and
      v = parm.getAVariable() and
      // at least one parameter is documented
      exists(doc.getATag().(JSDocParamTag).getDocumentedParameter()) and
      // but v is not
      not doc.getATag().(JSDocParamTag).getDocumentedParameter() = v and
      // don't report a violation in ambiguous cases
      strictcount(JSDoc d | d = f.getDocumentation() and d.getATag() instanceof JSDocParamTag) = 1
select parm, "Parameter " + v.getName() + " is not documented."