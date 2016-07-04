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
 * @name Useless type test
 * @description Testing whether a derived type is an instance of its base type is unnecessary.
 * @kind problem
 * @problem.severity warning
 * @cwe 561
 */

import default

from InstanceOfExpr ioe, RefType t, RefType ct
where t = ioe.getExpr().getType()
	and ct = ioe.getTypeName().getType()
	and ct = t.getASupertype+()
select ioe, "There is no need to test whether an instance of $@ is also an instance of $@ - it always is.",
	t, t.getName(),
	ct, ct.getName()
