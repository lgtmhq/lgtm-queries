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

import semmle.code.java.Expr

/** The method `method` validates its `arg`-th argument in some way. */ 
predicate validationMethod(Method method, int arg) {
  // The method examines the contents of the string argument.
  exists(Parameter param, VarAccess paramRef, MethodAccess call |
    method.getParameter(arg) = param and
    param.getType() instanceof TypeString and
    paramRef.getVariable() = param and
    call.getQualifier() = paramRef and
    (
      call.getMethod().getName() = "contains" or
      call.getMethod().getName() = "charAt"
    )
  )
  // The method calls another one that verifies the argument.
  or exists (Parameter param, MethodAccess call, int recursiveArg |
    method.getParameter(arg) = param and
    call.getArgument(recursiveArg) = param.getAnAccess() and
    validationMethod(call.getMethod(), recursiveArg)
  )
}

/** A variable that is ever passed to a string verification method. */
class ValidatedVariable extends Variable {
  ValidatedVariable() {
    exists(MethodAccess call, int arg, VarAccess access |
      validationMethod(call.getMethod(), arg) and
      call.getArgument(arg) = access and
      access.getVariable() = this
    )
  }
}
