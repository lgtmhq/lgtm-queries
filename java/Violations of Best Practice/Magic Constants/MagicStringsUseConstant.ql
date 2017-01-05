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
 * @name Magic strings: use defined constant
 * @description A magic string, which is used instead of an existing named constant, makes code less
 *              readable and maintainable.
 * @kind problem
 * @problem.severity recommendation
 * @tags changeability
 *       readability
 */
import java
import MagicConstants

from StringLiteral magicLiteral, string message, Field field, string linkText
where literalInsteadOfConstant(magicLiteral, message, field, linkText)
select magicLiteral, message, field, linkText
