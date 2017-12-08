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
 * @name Feature envy
 * @description A function that uses more functions and variables from another file than functions and variables from its own file. This function might be better placed in the other file, to avoid exposing internals of the file it depends on.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/feature-envy
 * @tags changeability
 *       maintainability
 *       modularity
 *       statistical
 */
import default

predicate functionUsesVariable(Function source, Variable v, File target) {
  v.getAnAccess().getEnclosingFunction() = source and
  not (v.(LocalScopeVariable).getFunction() = source) and
  v.getFile() = target
}

predicate functionUsesFunction(Function source, Function f, File target) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = source and fc.getTarget() = f) and
  f.getFile() = target
}

predicate functionSendsMessage(Function source, MemberFunction f, File target) {
  exists(MessageExpr me | me.getEnclosingFunction() = source and me.getStaticTarget() = f) and
  f.getFile() = target
}

predicate dependencyCount(Function source, File target, int res) {
  res = strictcount(Declaration d |
    functionUsesVariable(source, d, target) or
    functionUsesFunction(source, d, target) or
    functionSendsMessage(source, d, target)
  )
}

predicate selfDependencyCountOrZero(Function source, int res) {
  exists(File target
       | target = source.getFile() and onlyInFile(source, target)
       | res = max(int i | dependencyCount(source, target, i) or i = 0))
}

predicate dependsHighlyOn(Function source, File target, int res) {
  dependencyCount(source, target, res) and
  target.fromSource() and
  exists(int selfCount |
    selfDependencyCountOrZero(source, selfCount) and
    res > 2*selfCount and
    res > 4
  )
}

predicate onlyInFile(Function f, File file) {
  file = f.getFile() and
  not exists(File file2 | file2 = f.getFile() and file2 != file)
}

from Function f, File other, int selfCount, int depCount, string selfDeps
where dependsHighlyOn(f, other, depCount) and
      selfDependencyCountOrZero(f, selfCount) and
      not exists(File yetAnother | dependsHighlyOn(f, yetAnother, _) and yetAnother != other) and
      not other instanceof HeaderFile and
      not f instanceof MemberFunction
      and if      selfCount = 0 then selfDeps = "0 dependencies"
          else if selfCount = 1 then selfDeps = "only 1 dependency"
          else                       selfDeps = "only " + selfCount.toString() + " dependencies"
select f, "Function " + f.getName() + " could be moved to file $@" +
       " since it has " + depCount.toString() + " dependencies to that file, but " +
       selfDeps + " to its own file.", other, other.getFileName()
