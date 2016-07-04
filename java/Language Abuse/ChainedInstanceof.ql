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
 * @name Chain of 'instanceof' tests
 * @description Long sequences of type tests on a variable are are difficult to maintain.
 * @kind problem
 * @problem.severity recommendation
 */

import default

int instanceofCountForIfChain(IfStmt is) {
	exists(int rest |
		(
			if is.getElse() instanceof IfStmt then
				rest = instanceofCountForIfChain(is.getElse())
			else
				rest = 0
		)
		and
		(
			if is.getCondition() instanceof InstanceOfExpr then
			  result = 1 + rest
			else
			  result = rest
		)
	)
}

from IfStmt is, int n
where
	n = instanceofCountForIfChain(is)
	and n > 5
	and not exists(IfStmt other | is = other.getElse())
select is,
	"This if block performs a chain of " + n +
	" type tests - consider alternatives, e.g. polymorphism or the visitor pattern."
