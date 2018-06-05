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

import semmle.code.cpp.models.interfaces.ArrayFunction
import semmle.code.cpp.models.interfaces.Taint

class PureFunction extends ArrayFunction, TaintFunction {
  PureFunction() {
    exists(string name |
      hasName(name) and
      (
        name = "abs"
        or name = "atof"
        or name = "atoi"
        or name = "atol"
        or name = "atoll"
        or name = "labs"
        or name = "strcasestr"
        or name = "strchnul"
        or name = "strchr"
        or name = "strchrnul"
        or name = "strcmp"
        or name = "strcspn"
        or name = "strlen"
        or name = "strncmp"
        or name = "strnlen"
        or name = "strrchr"
        or name = "strspn"
        or name = "strstr"
        or name = "strtod"
        or name = "strtof"
        or name = "strtol"
        or name = "strtoll"
        or name = "strtoq"
        or name = "strtoul"
      )
    )
  }
  
  override predicate hasArrayInput(int bufParam) {
    getParameter(bufParam).getType().getUnspecifiedType() instanceof PointerType
  }
  
  predicate hasTaintFlow(FunctionInput input, FunctionOutput output) {
    exists (ParameterIndex i |
      input.isInParameter(i) or
      (
        input.isInParameterPointer(i) and
        getParameter(i).getType().getUnspecifiedType() instanceof PointerType
      )
    ) and
    (
      (
        output.isOutReturnPointer() and
        getType().getUnspecifiedType() instanceof PointerType
      ) or
      output.isOutReturnValue()
    )
  }
}