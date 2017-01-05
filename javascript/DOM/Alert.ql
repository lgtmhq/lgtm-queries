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
 * @name Invocation of alert
 * @description 'alert' should not be used in production code.
 * @kind problem
 * @problem.severity warning
 * @tags usability
 *       maintainability
 */

import javascript

class AlertCall extends CallExpr {
	AlertCall() {
		exists (GlobalVarAccess va |
			va = this.getCallee() and
			va.getName() = "alert"
		) or
		exists (DotExpr dot, GlobalVarAccess va |
			dot = this.getCallee() and
			va = dot.getBase() and
			va.getName() = "window" and
			dot.getPropertyName() = "alert"
		)
	}
}

from AlertCall alert
select alert, "Avoid calling alert."