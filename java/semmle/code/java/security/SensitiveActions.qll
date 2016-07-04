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
 * Sensitive data and methods for security.
 *
 * 'Sensitive' data in general is anything that should not be
 * sent around in unencrypted form. This library tries to guess
 * where sensitive data may either be stored in a variable or
 * produced by a method.
 *
 * In addition, there are methods that ought not to be executed or not
 * in a fashion that the user can control. This includes authorization
 * methods such as logins, and sending of data, etc.
 */
import default

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

/** An expression that might contain sensitive data. */
abstract class SensitiveExpr extends Expr {
}

/** A method access that might produce sensitive data. */
class SensitiveMethodAccess extends SensitiveExpr, MethodAccess {
  SensitiveMethodAccess() {
    this.getMethod() instanceof SensitiveDataMethod or
    // This is particularly to pick up methods with an argument like "password", which
    // may indicate a lookup.
    exists(string s | ((Literal)this.getAnArgument()).getLiteral().toLowerCase() = s |
      s.matches(suspicious()) and
      not s.matches(nonSuspicious())
    )
  }

  Callable getEnclosingCallable() { result = MethodAccess.super.getEnclosingCallable() }
  
  string toString() {
    result = MethodAccess.super.toString()
  }
}

/** Access to a variable that might contain sensitive data. */
class SensitiveVarAccess extends SensitiveExpr, VarAccess {
  SensitiveVarAccess() {
    exists(string s | this.getVariable().getName().toLowerCase() = s |
      s.matches(suspicious()) and
      not s.matches(nonSuspicious())
    )
  }
  
  string toString() {
    result = VarAccess.super.toString()
  }
}

/** A method that may produce sensitive data. */
abstract class SensitiveDataMethod extends Method {}

class CredentialsMethod extends SensitiveDataMethod {
  CredentialsMethod() {
    exists(string s | s = this.getName().toLowerCase() |
      s.matches(suspicious())
    )
  }
}

/** A method whose execution may be sensitive. */
abstract class SensitiveExecutionMethod extends Method {}

/** A method that may perform authorization. */
class AuthMethod extends SensitiveExecutionMethod {
  AuthMethod() {
    exists(string s | s = this.getName().toLowerCase() |
      (
        s.matches("%login%") or
        s.matches("%auth%")
      )
      and not 
      (
        s.matches("get%") or
        s.matches("set%") or
        s.matches("%loginfo%")
      )
    )
  }
}

/** A method that sends data, and so should not be run conditionally on user input. */
class SendingMethod extends SensitiveExecutionMethod {
  SendingMethod() {
	  exists(string s | s.matches("%Socket") |
	    this.getDeclaringType().hasQualifiedName("java.net", s) and
	    this.hasName("send")
	  )
  }
}
