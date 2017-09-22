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

import semmle.code.cpp.Location

/** A compiler-generated error, warning or remark. */
class Diagnostic extends Locatable, @diagnostic {

  /**
   * Gets the severity of the message, on a range from 1 to 5: 1=remark,
   * 2=warning, 3=discretionary error, 4=error, 5=catastrophic error.
   */
  int getSeverity() { diagnostics(this, result, _, _, _, _) }

  /** Gets the error code for this compiler message. */
  string getTag() { diagnostics(this, _, result, _, _, _) }
  predicate hasTag(string s) { this.getTag() = s }

  /**
   * Gets the error message text associated with this compiler
   * diagnostic.
   */
  string getMessage() { diagnostics(this, _, _, result, _, _) }

  /**
   * Gets the full error message text associated with this compiler
   * diagnostic.
   */
  string getFullMessage() { diagnostics(this, _, _, _, result, _) }

  /** Gets the source location corresponding to the compiler message. */
  override Location getLocation() { diagnostics(this, _, _, _, _, result) }

  override string toString() { result = this.getMessage() }

}

/** A compiler-generated remark (milder than a warning). */
class CompilerRemark extends Diagnostic {

  CompilerRemark() { this.getSeverity() = 1 }
}

/** A compiler-generated warning. */
class CompilerWarning extends Diagnostic {

  CompilerWarning() { this.getSeverity() = 2 }
}

/**
 * A compiler-generated discretionary error (a compile-time error that may
 * be suppressed).
 */
class CompilerDiscretionaryError extends Diagnostic {

  CompilerDiscretionaryError() { this.getSeverity() = 3 }
}

/** A compiler error message. */
class CompilerError extends Diagnostic {

  CompilerError() { this.getSeverity() = 4 }
}

/** A compiler error that prevents compilation from continuing. */
class CompilerCatastrophe extends Diagnostic {

  CompilerCatastrophe() { this.getSeverity() = 5 }
}
