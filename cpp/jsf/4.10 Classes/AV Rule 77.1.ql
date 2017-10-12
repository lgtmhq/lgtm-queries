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
 * @name Constructor with default arguments will be used as a copy constructor
 * @description Constructors with default arguments should not be signature-compatible with a copy constructor when their default arguments are taken into account.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/constructor-used-as-copy-constructor
 * @tags reliability
 *       readability
 *       language-features
 */
import default

from CopyConstructor f
where f.getNumberOfParameters() > 1
  and not f.mayNotBeCopyConstructorInInstantiation()
select f, f.getName() + " is signature-compatible with a copy constructor when its default arguments are taken into account."
