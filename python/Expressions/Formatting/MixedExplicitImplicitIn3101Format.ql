// Copyright 2016 Semmle Ltd.
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
 * @name Formatting string mixes implicitly and explicitly numbered fields
 * @description Using implicit and explicit numbering in string formatting operations, such as '"{}: {1}".format(a,b)', will raise a ValueError.
 * @kind problem
 * @problem.severity error
 */

import python
import AdvancedFormatting

from AdvancedFormattingCall call, AdvancedFormatString fmt
where call.getAFormat() = fmt and fmt.isImplicitlyNumbered() and fmt.isExplicitlyNumbered()
select fmt, "Formatting string mixes implicitly and explicitly numbered fields."
