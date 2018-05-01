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
 * Provides an abstract class for accurate taint modeling of library
 * functions when source code is not available.  To use this QL library,
 * create a QL class extending `TaintFunction` with a characteristic predicate
 * that selects the function or set of functions you are modeling. Within that
 * class, override the predicates provided by `TaintFunction` to match the flow
 * within that function.
 */

import semmle.code.cpp.Function
import FunctionInputsAndOutputs
import semmle.code.cpp.models.Models

/**
 * A library function for which a taint-tracking library should propagate taint
 * from a parameter or qualifier to an output buffer, return value, or qualifier.
 * 
 * Note that this does not include direct copying of values; that is covered by
 * DataFlowModel.qll
 */
abstract class TaintFunction extends Function {
  abstract predicate hasTaintFlow(FunctionInput input, FunctionOutput output);
}