// Copyright 2016 Semmle Ltd.
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
 * @name Magic numbers
 * @description A magic number makes code less readable and maintainable.
 * @kind problem
 * @problem.severity recommendation
 */
import default
import MagicConstants

from Literal e, string msg
where magicConstant(e, msg)
  and isNumber(e)
select e, msg
