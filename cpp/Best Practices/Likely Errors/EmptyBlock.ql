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
 * @name Empty branch of conditional or empty loop body
 * @description Finds empty branches of conditionals and empty loop bodies. This may indicate badly maintained code.
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id cpp/empty-block
 * @tags reliability
 *       readability
 */
import default

predicate macroUse(Locatable l) {
  l instanceof PreprocessorDirective or l instanceof MacroInvocation
}

predicate macroUseLocation(File f, int start, int end) {
  exists(Locatable l, Location loc |
    macroUse(l) and
    loc = l.getLocation() and
    f = loc.getFile() and
    start = loc.getStartLine() and
    end = loc.getEndLine()
  )
}

pragma[noopt]
predicate emptyBlock(ControlStructure s, Block b, File f, int start, int end) {
  s instanceof ControlStructure and
  b = s.getAChild() and
  b instanceof Block and
  not exists(b.getAChild()) and
  f = b.getFile() and
  exists (Location l |
    l = b.getLocation() and
    start = l.getStartLine() and
    end = l.getEndLine()
  )
}

pragma[noopt]
predicate query(ControlStructure s, Block b) {
  exists(File f, int blockStart, int blockEnd |
    emptyBlock(s, b, f, blockStart, blockEnd) and
    not exists(int macroStart, int macroEnd |
      macroUseLocation(f, macroStart, macroEnd) and
      macroStart > blockStart and
      macroEnd < blockEnd
    )
  )
}

predicate sameLine(ControlStructure cs, Block b) {
  cs instanceof Loop and
  b = cs.getAChild() and
  b.getLocation().getStartLine() = b.getLocation().getEndLine()
}

from ControlStructure s, Block eb
where query(s, eb) and
      not eb.isInMacroExpansion() and
      not sameLine(s, eb)
select eb, "Empty block"
