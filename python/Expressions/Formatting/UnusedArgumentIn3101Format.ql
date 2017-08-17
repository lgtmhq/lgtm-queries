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
 * @name Unused argument in a formatting call
 * @description Including surplus arguments in a formatting call makes code more difficult to read and may indicate an error.
 * @kind problem
 * @tags maintainability
 *       useless-code
 * @problem.severity warning
 * @sub-severity high
 * @precision high
 * @id py/str-format/surplus-argument
 */

import python


import python
import AdvancedFormatting

from AdvancedFormattingCall call, AdvancedFormatString fmt, int arg_count, int max_field
where arg_count = call.providedArgCount() and max_field = max(fmt.getFieldNumber(_, _)) and
call.getAFormat() = fmt and not exists(call.getStarargs()) and max_field+1 < arg_count
select call, "Too many arguments for string format. Format $@ requires at only " + (max_field+1) + ", but " + 
arg_count.toString() + " are provided.", fmt, "\"" + fmt.getText() + "\""
