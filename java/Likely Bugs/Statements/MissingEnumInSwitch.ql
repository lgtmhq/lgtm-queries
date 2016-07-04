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
 * @name Missing enum case in switch
 * @description A 'switch' statement that is based on an 'enum' type and does not have cases for all 
 *              the 'enum' constants is usually a coding mistake.
 * @kind problem
 * @problem.severity warning
 * @cwe 478
 */

import default

from SwitchStmt switch, EnumType enum, EnumConstant missing
where switch.getExpr().getType() = enum
  and missing.getDeclaringType() = enum
  and not exists(switch.getDefaultCase())
  and not switch.getAConstCase().getValue() = missing.getAnAccess()
select switch, "Switch statement does not have a case for $@.", missing, missing.getName()
