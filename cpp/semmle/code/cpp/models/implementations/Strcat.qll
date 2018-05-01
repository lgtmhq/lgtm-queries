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
import semmle.code.cpp.models.interfaces.DataFlow
import semmle.code.cpp.models.interfaces.Taint


/**
 * The standard function `strcat` and its wide, sized, and Microsoft variants.
 */
class StrcatFunction extends TaintFunction, DataFlowFunction, ArrayFunction {
  StrcatFunction() {
    exists(string name | name = getName()|
      name = "strcat" // strcat(dst, src)
      or name = "strncat" // strncat(dst, src, max_amount)
      or name = "wcscat" // wcscat(dst, src)
      or name = "_mbscat" // _mbscat(dst, src)
      or name = "wcsncat" // wcsncat(dst, src, max_amount)
      or name = "_mbsncat" // _mbsncat(dst, src, max_amount)
      or name = "_mbsncat_l" // _mbsncat_l(dst, src, max_amount, locale)
    )
  }
  
  override predicate hasDataFlow(FunctionInput input, FunctionOutput output) {
    input.isInParameter(0) and
    output.isOutReturnValue()
  }
  
  override predicate hasTaintFlow(FunctionInput input, FunctionOutput output) {
    exists(string name | name = getName()
    | (
        (
          name = "strncat" or
          name = "wcsncat" or
          name = "_mbsncat" or
          name = "_mbsncat_l"
        ) and
        input.isInParameter(2) and
        output.isOutParameterPointer(0)
      ) or (
        name = "_mbsncat_l" and
        input.isInParameter(3) and
        output.isOutParameterPointer(0)
      )
    ) or (
      input.isInParameterPointer(0) and
      output.isOutParameterPointer(0)
    ) or (
      input.isInParameter(1) and
      output.isOutParameterPointer(0)
    )
  }
  
  override predicate hasArrayInput(int param) {
    param = 0 or
    param = 1
  }
  
  override predicate hasArrayOutput(int param) {
    param = 0
  }
  
  override predicate hasArrayWithNullTerminator(int param) {
    param = 1
  }
  
  override predicate hasArrayWithUnknownSize(int param) {
    param = 0
  }
}