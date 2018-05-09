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
 * @name Inappropriate Intimacy
 * @description Two files share too much information about each other (accessing many operations or variables in both directions). It would be better to invert some of the dependencies to reduce the coupling between the two files.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/file-intimacy
 * @tags maintainability
 *       modularity
 *       statistical
 *       non-attributable
 */
import cpp

predicate remoteVarAccess(File source, File target, VariableAccess va) {
  va.getFile() = source and
  va.getTarget().getFile() = target and
  // Ignore variables with locations in multiple files
  strictcount(File f | f = va.getTarget().getFile()) = 1 and
  source != target
}

predicate remoteFunAccess(File source, File target, FunctionCall fc) {
  fc.getFile() = source and
  fc.getTarget().getFile() = target and
  // Ignore functions with locations in multiple files
  strictcount(File f | f = fc.getTarget().getFile()) = 1 and
  source != target
}

predicate remoteMessagePass(File source, File target, MessageExpr me) {
  me.getFile() = source and
  me.getStaticTarget().getFile() = target and
  // Ignore targets with locations in multiple files
  strictcount(File f | f = me.getTarget().getFile()) = 1 and
  source != target
}

predicate candidateFilePair(File source, File target) {
  remoteVarAccess(source, target, _) or
  remoteFunAccess(source, target, _) or
  remoteMessagePass(source, target, _)
}

predicate variableDependencyCount(File source, File target, int res) {
  candidateFilePair(source, target) and
  res = count(VariableAccess va | remoteVarAccess(source, target, va))
}

predicate functionDependencyCount(File source, File target, int res) {
  candidateFilePair(source, target) and
  res = count(FunctionCall fc | remoteFunAccess(source, target, fc))
}

predicate messageDependencyCount(File source, File target, int res) {
  candidateFilePair(source, target) and
  res = count(MessageExpr me | remoteMessagePass(source, target, me))
}

predicate highDependencyCount(File source, File target, int res) {
  exists(int varCount, int funCount, int mesCount |
    variableDependencyCount(source, target, varCount) and
    functionDependencyCount(source, target, funCount) and
    messageDependencyCount(source, target, mesCount) and
    res = varCount + funCount + mesCount and
    res > 20)
}

from File a, File b, int ca, int cb
where highDependencyCount(a, b, ca) and
      highDependencyCount(b, a, cb) and
      ca >= cb and
      a != b and
      not a instanceof HeaderFile and
      not b instanceof HeaderFile and
      b.getShortName().trim().length() > 0
select a, "File is too closely tied to $@ (" + ca.toString() + " dependencies one way and " + cb.toString() + " the other).",
       b, b.getBaseName()
