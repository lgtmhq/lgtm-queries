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
 * QL classes for working with intra-procedural control flow graphs (CFGs).
 */

import javascript

/**
 * A node in the control flow graph, which is an expression, a statement,
 * or a synthetic node.
 */
class CFGNode extends @cfg_node, Locatable {
  /** Get a node succeeding this node in the CFG. */
  CFGNode getASuccessor() {
    successor(this, result)
  }

  /** Get a node preceding this node in the CFG. */
  CFGNode getAPredecessor() {
    this = result.getASuccessor()
  }

  /** Is this a branching node with more than one successor? */
  predicate isBranch() {
    strictcount(getASuccessor()) > 1
  }

  /** Is this a join node with more than one predecessor? */
  predicate isJoin() {
    strictcount(getAPredecessor()) > 1
  }
}

/** A synthetic CFG node marking the entry or exit point of a function or script. */
class SyntheticCFGNode extends @synthetic_cfg_node, CFGNode {
}

/** A synthetic CFG node marking the entry point of a function or toplevel script. */
class EntryCFGNode extends SyntheticCFGNode, @entry_node {
  /** Get the function or toplevel of which this node is the entry. */
  StmtContainer getContainer() {
    entry_cfg_node(this, result)
  }

  string toString() {
    result = "entry node of " + getContainer().toString()
  }
}

/** A synthetic CFG node marking the exit of a function or toplevel script. */
class ExitCFGNode extends SyntheticCFGNode, @exit_node {
  /** Get the function or toplevel of which this node is the exit. */
  StmtContainer getContainer() {
    exit_cfg_node(this, result)
  }

  string toString() {
    result = "exit node of " + getContainer().toString()
  }
}