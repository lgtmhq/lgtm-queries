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
 * @name Missing named arguments in formatting call
 * @description A string formatting operation, such as '"{name}".format(key=b)',
 *              where the names of format items in the format string differs from the names of the values to be formatted will raise a KeyError.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 * @sub-severity low
 * @precision high
 */

import python
import AdvancedFormatting

from AdvancedFormattingCall call, AdvancedFormatString fmt, string name
where call.getAFormat() = fmt and 
not name = call.getAKeyword().getArg() and
fmt.getFieldName(_, _) = name
and not exists(call.getKwargs())
select call, "Missing named argument for string format. Format $@ requires '" + name + "', but it is omitted.",
fmt, "\"" + fmt.getText() + "\""