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
 * @name Missing enum case in switch
 * @description A switch statement over an enum type is missing a case for some enum constant
 *              and does not have a default case. This may cause logic errors.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/missing-case-in-switch
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-478
 */
import default

from EnumSwitch es, float missing, float total
where not es.hasDefaultCase()
     and missing = count(es.getAMissingCase())
     and total = missing + count(es.getASwitchCase())
     and missing/total < 0.30
select es, "Switch statement is missing case for "+es.getAMissingCase().getName()
