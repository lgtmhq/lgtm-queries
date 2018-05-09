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
 * Provides a class for modeling `printf`-style formatting functions. To use
 * this QL library, create a QL class extending `DataFlowFunction` with a
 * characteristic predicate that selects the function or set of functions you
 * are modeling. Within that class, override the predicates provided by
 * `FormattingFunction` to match the flow within that function.
 */

import semmle.code.cpp.Function
/**
 * A standard library function that uses a `printf`-like formatting string.
 */
abstract class FormattingFunction extends Function {
  /** Gets the position at which the format parameter occurs. */
  abstract int getFormatParameterIndex();

  /**
   * Holds if the default meaning of `%s` is a `wchar_t *`, rather than
   * a `char *` (either way, `%S` will have the opposite meaning).
   */
  predicate isWideCharDefault() { none() }

  /**
   * Gets the position at which the output parameter, if any, occurs.
   */
  int getOutputParameterIndex() { none() }

  /**
   * Gets the position of the first format argument, corresponding with
   * the first format specifier in the format string.
   */
  int getFirstFormatArgumentIndex() { result = getNumberOfParameters() }

  /**
   * Gets the position of the buffer size argument, if any.
   */
  int getSizeParameterIndex() { none() }
}