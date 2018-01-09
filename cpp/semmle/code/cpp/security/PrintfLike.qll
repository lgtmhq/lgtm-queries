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

import semmle.code.cpp.commons.Printf
import external.ExternalArtifact

predicate printfLikeFunction(Function func, int formatArg) {
  (formatArg = func.(FormattingFunction).getFormatParameterIndex() and not func instanceof UserDefinedFormattingFunction)
  or
  primitiveVariadicFormatter(func, formatArg, _)
  or
  exists(ExternalData data |
    // TODO Do this \ to / conversion in the toolchain?
    data.getDataPath().replaceAll("\\", "/") = "cert/formatingFunction.csv"
    and func.getName() = data.getField(0)
    and formatArg = data.getFieldAsInt(1)
  )
}
