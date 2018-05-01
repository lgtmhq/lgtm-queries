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
 * Provides an abstract class for accurate dataflow modeling of library
 * functions when source code is not available.  To use this QL library,
 * create a QL class extending `DataFlowFunction` with a characteristic
 * predicate that selects the function or set of functions you are modeling.
 * Within that class, override the predicates provided by `DataFlowFunction`
 * to match the flow within that function.
 */

import semmle.code.cpp.Function
import FunctionInputsAndOutputs
import semmle.code.cpp.models.Models
 

/**
 * A library function for which a value is copied from a parameter or qualifier
 * to an output buffer, return value, or qualifier.
 * 
 * Note that this does not include partial copying of values or partial writes
 * to destinations; that is covered by `TaintModel.qll`.
 */
abstract class DataFlowFunction extends Function {
  abstract predicate hasDataFlow(FunctionInput input, FunctionOutput output);
}