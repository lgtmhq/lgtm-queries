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

/*
 * Security pack options.
 *
 * see https://semmle.com/wiki/display/SD/_Configuring+SecurityOptions+for+your+code+base
 *
 * Please note that functions for MySql and SQLite are included by default and do not
 * require any customization here.
 */

import semmle.code.cpp.security.Security

class CustomSecurityOptions extends SecurityOptions {
  predicate sqlArgument(string function, int arg) {
    SecurityOptions.super.sqlArgument(function, arg) or
    // --- custom functions that access SQL code via one of their arguments:
    // 'arg' is the 0-based index of the argument that contains an SQL string
    // for example: (function = "MySpecialSqlFunction" and arg = 0)
    none() // rules to match custom functions replace this line
  }

  predicate userInputArgument(FunctionCall functionCall, int arg)
  {
    SecurityOptions.super.userInputArgument(functionCall, arg) or
    exists(string fname |
      functionCall.getTarget().hasGlobalName(fname) and
      exists(functionCall.getArgument(arg)) and (
        // --- custom functions that return user input via one of their arguments:
        // 'arg' is the 0-based index of the argument that is used to return user input
        // for example: (fname = "readXmlInto" and arg = 1)
        none() // rules to match custom functions replace this line
      )
    )
  }

  predicate userInputReturned(FunctionCall functionCall)
  {
    SecurityOptions.super.userInputReturned(functionCall) or 
    exists(string fname |
      functionCall.getTarget().hasGlobalName(fname) and
      (
        // --- custom functions that return user input via their return value:
        // for example: fname = "xmlReadAttribute"
        none() // rules to match custom functions replace this line
      )
    )
  }
}
