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
 * @name Too few arguments in formatting call
 * @description A string formatting operation, such as '"{0}: {1}, {2}".format(a,b)',
 *              where the number of values to be formatted is too few for the format string will raise an IndexError.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 */

import python
import AdvancedFormatting

from AdvancedFormattingCall call, AdvancedFormatString fmt, 
int arg_count, int max_field, string provided
where arg_count = call.providedArgCount() and max_field = max(fmt.getFieldNumber(_, _)) and
call.getAFormat() = fmt and not exists(call.getStarargs()) and arg_count <= max_field and
(if arg_count = 1 then provided = " is provided." else provided = " are provided.")
select call, "Too few arguments for string format. Format $@ requires at least " + (max_field+1) + ", but " + 
arg_count.toString() + provided, fmt, "\"" + fmt.getText() + "\""