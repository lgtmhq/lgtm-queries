// Copyright 2017 Semmle Ltd.
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
 * @name Use of arguments.caller or arguments.callee
 * @description The properties 'arguments.caller' and 'argument.callee' have subtle semantics and
 *              make code non-modular and hard to maintain. Consequently, they should not be used.
 * @kind problem
 * @problem.severity recommendation
 * @id js/call-stack-introspection
 * @tags maintainability
 *       language-features
 * @precision very-high
 */

import javascript

from PropAccess acc, ArgumentsVariable args
where acc.getBase() = args.getAnAccess() and
      acc.getPropertyName().regexpMatch("caller|callee") and
      // don't flag cases where the variable can never contain an arguments object
      not exists (Function fn | args = fn.getVariable()) and
      not exists (Parameter p | args = p.getAVariable()) and
      // arguments.caller/callee in strict mode causes runtime errors,
      // this is covered by the query 'Use of call stack introspection in strict mode'
      not acc.getContainer().isStrict()
select acc, "Avoid using arguments.caller and arguments.callee."