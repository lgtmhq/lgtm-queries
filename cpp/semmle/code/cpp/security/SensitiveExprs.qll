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

import cpp

private string suspicious() {
  result = "%password%" or
  result = "%passwd%" or
  result = "%account%" or
  result = "%accnt%" or
  result = "%trusted%"
}

private string nonSuspicious() {
  result = "%hashed%" or
  result = "%encrypted%" or
  result = "%crypt%"
}

abstract class SensitiveExpr extends Expr {}

class SensitiveVarAccess extends SensitiveExpr {
  SensitiveVarAccess() {
    this instanceof VariableAccess and
    exists(string s | this.toString().toLowerCase() = s |
      s.matches(suspicious())and
      not s.matches(nonSuspicious())
    )
  }
}

class SensitiveCall extends SensitiveExpr {
  SensitiveCall() {
    this instanceof FunctionCall and
    exists(string s | this.toString().toLowerCase() = s |
      s.matches(suspicious())and
      not s.matches(nonSuspicious())
    )
  } 
}

class SensitivePropAccess extends SensitiveExpr {
  SensitivePropAccess() {
    exists (PropertyAccess acc, string name |
      acc = this and
      name = acc.getProperty().getName().toLowerCase() and
      name.matches(suspicious()) and
      not name.matches(nonSuspicious()))
  }
}

/**
 * A read from the value of a text widget.
 */
class SensitiveTextRead extends SensitiveExpr {
  SensitiveTextRead() {
    exists (PropertyAccess facc |
      facc = this and
      facc.getReceiver() instanceof SensitiveExpr and
      facc.getProperty().getName() = "text")
  }
}
