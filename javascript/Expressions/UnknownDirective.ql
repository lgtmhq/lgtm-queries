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
 * @name Unknown directive
 * @description An unknown directive has no effect and may indicate a misspelling.
 * @kind problem
 * @problem.severity warning
 * @id js/unknown-directive
 * @tags correctness
 * @precision high
 */

import javascript

from Directive d
where not d instanceof KnownDirective and
      // but exclude attribute top-levels: `<a href="javascript:'some-attribute-string'">`
      not (d.getParent() instanceof CodeInAttribute)
select d, "Unknown directive: '" + d.getDirectiveText() + "'."
