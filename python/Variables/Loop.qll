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

import python


private predicate empty_sequence(Expr e) {
    exists(SsaVariable var | var.getAUse().getNode() = e | empty_sequence(var.getDefinition().getNode())) or
    e instanceof List and not exists(e.(List).getAnElt()) or
    e instanceof Tuple and not exists(e.(Tuple).getAnElt()) or
    e.(StrConst).getText().length() = 0
}

/* This has the potential for refinement, but we err on the side of fewer false positives for now. */
private predicate probably_non_empty_sequence(Expr e) {
    not empty_sequence(e)
}

/** A loop which probably defines v */
private Stmt loop_probably_defines(Variable v) {
    exists(Name defn | defn.defines(v) and result.contains(defn) |
        probably_non_empty_sequence(result.(For).getIter())
        or
        probably_non_empty_sequence(result.(While).getTest())
    )
}

/** Whether the variable used by `use` is probably defined in a loop */
predicate probably_defined_in_loop(Name use) {
    exists(Stmt loop |
        loop = loop_probably_defines(use.getVariable()) |
        loop.getAFlowNode().strictlyReaches(use.getAFlowNode())
    )
}
