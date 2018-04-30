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
 * The standard function `stract` and its wide, sized, and Microsoft variants.
 */
class StrcpyFunction extends ArrayFunction, DataFlowFunction, TaintFunction {
  StrcpyFunction() {
    this.hasName("strcpy") or
    this.hasName("_mbscpy") or
    this.hasName("wcscpy") or
    this.hasName("strncpy") or
    this.hasName("_mbsncpy") or
    this.hasName("wcsncpy")
  }
  
  override predicate hasArrayInput(int bufParam) {
    bufParam = 1
  }
  
  override predicate hasArrayOutput(int bufParam) {
    bufParam = 0
  }
  
  override predicate hasArrayWithNullTerminator(int bufParam) {
    bufParam = 1
  }
  
  override predicate hasArrayWithVariableSize(int bufParam, int countParam) {
    (
      this.hasName("strncpy") or
      this.hasName("_mbsncpy") or
      this.hasName("wcsncpy")
    ) and
    bufParam = 0 and
    countParam = 2
  }
  
  override predicate hasArrayWithUnknownSize(int bufParam) {
    (
      this.hasName("strcpy") or
      this.hasName("_mbscpy") or
      this.hasName("wcscpy")
    ) and
    bufParam = 0
  }
  

  override predicate hasDataFlow(FunctionInput input, FunctionOutput output) {
    (
      (
        // These always copy the full value of the input buffer to the output
        // buffer
        this.hasName("strcpy") or
        this.hasName("_mbscpy") or
        this.hasName("wcscpy")
      ) and (
        (
          input.isInParameterPointer(1) and
          output.isOutParameterPointer(0)
        ) or (
          input.isInParameterPointer(1) and
          output.isOutReturnPointer()
        )
      )
    ) or (
      input.isInParameter(0) and
      output.isOutReturnValue()
    )
  }
  
  override predicate hasTaintFlow(FunctionInput input, FunctionOutput output) {
    (
      // these may do only a partial copy of the input buffer to the output
      // buffer
      this.hasName("strncpy") or
      this.hasName("_mbsncpy") or
      this.hasName("wcsncpy")
    ) and (
      input.isInParameter(2) or
      input.isInParameterPointer(1)
    ) and (
      output.isOutParameterPointer(0) or
      output.isOutReturnPointer()
    )
  }
}