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
 * @name Implicit downcast from bitfield
 * @description A bitfield is implicitly downcast to a smaller integer type.
 *              This could lead to loss of upper bits of the bitfield.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/implicit-bitfield-downcast
 * @tags reliability
 *       correctness
 *       types
 */

import cpp

from BitField fi, VariableAccess va

where fi.getNumBits() > va.getFullyConverted().getType().getSize() * 8
  and va.getExplicitlyConverted().getType().getSize() > va.getFullyConverted().getType().getSize()
  and va.getTarget() = fi
  and not va.getActualType() instanceof BoolType

select va, "Implicit downcast of bitfield $@", fi, fi.toString()
