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
 * @name Unused named argument in formatting call
 * @description Including surplus keyword arguments in a formatting call makes code more difficult to read and may indicate an error.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       useless-code
 */

import python
import AdvancedFormatting

from AdvancedFormattingCall call, AdvancedFormatString fmt, string name, string fmt_repr
where call.getAFormat() = fmt and 
name = call.getAKeyword().getArg() and
forall(AdvancedFormatString format | format = call.getAFormat() | not format.getFieldName(_, _) = name)
and not exists(call.getKwargs()) and
(strictcount(call.getAFormat()) = 1 and fmt_repr = "format \"" + fmt.getText() + "\""
 or
 strictcount(call.getAFormat()) != 1  and fmt_repr = "any format used."
)

select call, "Surplus named argument for string format. An argument named '" + name + 
             "' is provided, but it is not required by $@.", fmt, fmt_repr
