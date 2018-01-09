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
 * Provides classes and predicates for identifying sensitive data and methods for security.
 *
 * 'Sensitive' data in general is anything that should not be sent around in unencrypted form. This
 * library tries to guess where sensitive data may either be stored in a variable or produced by a
 * method.
 *
 * In addition, there are methods that ought not to be executed or not in a fashion that the user
 * can control. This includes authorization methods such as logins, and sending of data, etc.
 */

import javascript

/** A regular expression that identifies strings that look like they represent secret data that are not passwords. */
private string suspiciousNonPassword() {
  result = "(?is).*(account|accnt|(?<!un)trusted).*"
}
/** A regular expression that identifies strings that look like they represent secret data that are passwords. */
private string suspiciousPassword() {
  result = "(?is).*(password|passwd).*"
}

/** A regular expression that identifies strings that look like they represent secret data. */
private string suspicious() {
  result = suspiciousPassword() or result = suspiciousNonPassword()
}

/**
 * A string for `match` that identifies strings that look like they represent secret data that is
 * hashed or encrypted.
 */
private string nonSuspicious() {
  result = "(?is).*(hash|(?<!un)encrypted|\\bcrypt\\b).*"
}

/** An expression that might contain sensitive data. */
abstract class SensitiveExpr extends Expr { }

/** A method access that might produce sensitive data. */
class SensitiveCall extends SensitiveExpr, InvokeExpr {
  SensitiveCall() {
    this.getCalleeName() instanceof SensitiveDataFunctionName or
    // This is particularly to pick up methods with an argument like "password", which
    // may indicate a lookup.
    exists(string s | this.getAnArgument().getStringValue() = s |
      s.regexpMatch(suspicious()) and
      not s.regexpMatch(nonSuspicious())
    )
  }
}

/** An access to a variable or property that might contain sensitive data. */
abstract class SensitiveVariableAccess extends SensitiveExpr {

  string name;

  SensitiveVariableAccess() {
    this.(VarAccess).getName() = name or
    this.(PropAccess).getPropertyName() = name
  }

}

/** An access to a variable or property that might contain sensitive data. */
private class BasicSensitiveVariableAccess extends SensitiveVariableAccess {

  BasicSensitiveVariableAccess() {
    name.regexpMatch(suspicious()) and not name.regexpMatch(nonSuspicious())
  }

}

/** A function name that suggests it may be sensitive. */
abstract class SensitiveFunctionName extends string {
  SensitiveFunctionName() {
    this = any(Function f).getName() or
    this = any(Property p).getName() or
    this = any(PropAccess pacc).getPropertyName()
  }
}

/** A function name that suggests it may produce sensitive data. */
abstract class SensitiveDataFunctionName extends SensitiveFunctionName {}

/** A method that might return sensitive data, based on the name. */
class CredentialsFunctionName extends SensitiveDataFunctionName {
  CredentialsFunctionName() {
    this.regexpMatch(suspicious())
  }
}

/**
 * Classes for expressions containing cleartext passwords.
 */
private module CleartextPasswords {

  bindingset[name]
  private predicate isCleartextPasswordIndicator(string name) {
    name.regexpMatch(suspiciousPassword()) and
    not name.regexpMatch(nonSuspicious())
  }

  /** An expression that might contain a cleartext password. */
  abstract class CleartextPasswordExpr extends SensitiveExpr { }

  /** A function name that suggests it may produce a cleartext password. */
  private class CleartextPasswordDataFunctionName extends SensitiveDataFunctionName {
    CleartextPasswordDataFunctionName() {
      isCleartextPasswordIndicator(this)
    }
  }

  /** A call that might return a cleartext password. */
  private class CleartextPasswordCallExpr extends CleartextPasswordExpr, SensitiveCall {
    CleartextPasswordCallExpr() {
      this.getCalleeName() instanceof CleartextPasswordDataFunctionName or
      // This is particularly to pick up methods with an argument like "password", which
      // may indicate a lookup.
      isCleartextPasswordIndicator(this.getAnArgument().(DataFlowNode).getALocalSource().(ConstantString).getStringValue())

    }
  }

  /** An access to a variable or property that might contain a cleartext password. */
  private class CleartextPasswordLookupExpr extends CleartextPasswordExpr, SensitiveVariableAccess {
    CleartextPasswordLookupExpr() {
      isCleartextPasswordIndicator(name)
    }
  }

}
import CleartextPasswords
