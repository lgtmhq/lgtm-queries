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
 * Provides classes and predicates for computing statement-level intra-procedural control flow graphs.
 *
 * DEPRECATED: Use `ControlFlowGraph.qll` instead.
 */

import java

private predicate cfgMap(ControlFlowNode n, StmtParent s) {
  (n.getEnclosingStmt() = s or n = s) and not n instanceof DoStmt or
  cfgMap(n.(DoStmt).getStmt(), s)
}

/**
 * The control-flow graph restricted to statements.
 * 
 * DEPRECATED: Use `ControlFlowNode.getASuccessor()` instead.
 */
cached
deprecated StmtParent stmtSucc(Stmt s) {
  result != s and
  exists (ControlFlowNode n1, ControlFlowNode n2 |
    cfgMap(n1, s) and cfgMap(n2, result) and
    n2 = n1.getASuccessor()
  )
}
