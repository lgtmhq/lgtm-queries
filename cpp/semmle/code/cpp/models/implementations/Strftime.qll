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

import semmle.code.cpp.models.interfaces.Taint
import semmle.code.cpp.models.interfaces.ArrayFunction

class Strftime extends TaintFunction, ArrayFunction {
  Strftime() {
    hasQualifiedName("strftime")
  }
  
  override predicate hasTaintFlow(FunctionInput input, FunctionOutput output) {
    (
      input.isInParameter(1) or
      input.isInParameterPointer(2) or
      input.isInParameterPointer(3)
    )
    and
    (
      output.isOutParameterPointer(0) or
      output.isOutReturnValue()
    )
  }
  
  override predicate hasArrayWithNullTerminator(int bufParam) {
    bufParam = 2
  }
  
  override predicate hasArrayWithFixedSize(int bufParam, int elemCount) {
    bufParam = 3 and
    elemCount = 1
  }
  
  override predicate hasArrayWithVariableSize(int bufParam, int countParam) {
    bufParam = 0 and
    countParam = 1
  }
  
  override predicate hasArrayInput(int bufParam) {
    bufParam = 2 or
    bufParam = 3
  }
  
  override predicate hasArrayOutput(int bufParam) {
    bufParam = 0
  }
}
