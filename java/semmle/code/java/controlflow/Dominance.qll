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
 * Library for control-flow graph dominance.
 */
import java
private import semmle.code.java.Successor
private import semmle.code.java.ControlFlowGraph


/*
 * Predicates for basic-block-level dominance.
 */

/** Entry points for control-flow. */
private predicate flowEntry(Stmt entry) {
  exists (Callable c | entry = c.getBody())
}

/** The successor relation for basic blocks. */
private predicate bbSucc(BasicBlock pre, BasicBlock post) {
  post = pre.getABBSuccessor()
}

/** The immediate dominance relation for basic blocks. */
predicate bbIDominates(BasicBlock dom, BasicBlock node) = idominance(flowEntry/1, bbSucc/2)(_, dom, node)

/** Exit points for control-flow. */
private predicate flowExit(Callable exit) {
  exists(ControlFlowNode s | s.getASuccessor() = exit)
}

/** Exit points for basic-block control-flow. */
private predicate bbSink(BasicBlock exit) {
  flowExit(exit.getLastNode())
}

/** Reversed `bbSucc`. */
private predicate bbPred(BasicBlock post, BasicBlock pre) {
  post = pre.getABBSuccessor()
}

/** The immediate post-dominance relation on basic blocks. */
predicate bbIPostDominates(BasicBlock dominator, BasicBlock node) = idominance(bbSink/1,bbPred/2)(_, dominator, node)

/** Whether `dom` strictly dominates `node`. */
predicate bbStrictlyDominates(BasicBlock dom, BasicBlock node) { bbIDominates+(dom, node) }

/** Whether `dom` dominates `node`. (This is reflexive.) */
predicate bbDominates(BasicBlock dom, BasicBlock node) { bbStrictlyDominates(dom, node) or dom = node }

/** Whether `dom` strictly post-dominates `node`. */
predicate bbStrictlyPostDominates(BasicBlock dom, BasicBlock node) { bbIPostDominates+(dom, node) }

/** Whether `dom` post-dominates `node`. (This is reflexive.) */
predicate bbPostDominates(BasicBlock dom, BasicBlock node) { bbStrictlyPostDominates(dom, node) or dom = node }

/** The dominance frontier relation for basic blocks. */
predicate dominanceFrontier(BasicBlock x, BasicBlock w) {
  bbDominates(x, w.getABBPredecessor()) and not bbStrictlyDominates(x, w)
}

/*
 * Predicates for expression-level dominance.
 */

/** Immediate dominance relation on control-flow graph nodes. */
predicate iDominates(ControlFlowNode dominator, ControlFlowNode node) {
  exists(BasicBlock bb, int i | dominator = bb.getNode(i) and node = bb.getNode(i+1)) or
  exists(BasicBlock dom, BasicBlock bb |
    bbIDominates(dom, bb) and
    dominator = dom.getLastNode() and
    node = bb.getFirstNode()
  )
}

/** Whether `dom` strictly dominates `node`. */
pragma[inline]
predicate strictlyDominates(ControlFlowNode dom, ControlFlowNode node) {
  // This predicate is gigantic, so it must be inlined.
  bbStrictlyDominates(dom.getBasicBlock(), node.getBasicBlock())
  or
  exists(BasicBlock b, int i, int j |
    dom = b.getNode(i) and node = b.getNode(j) and i < j
  )
}

/** Whether `dom` dominates `node`. (This is reflexive.) */
pragma[inline]
predicate dominates(ControlFlowNode dom, ControlFlowNode node) {
  // This predicate is gigantic, so it must be inlined.
  bbStrictlyDominates(dom.getBasicBlock(), node.getBasicBlock())
  or
  exists(BasicBlock b, int i, int j |
    dom = b.getNode(i) and node = b.getNode(j) and i <= j
  )
}

/** Whether `dom` strictly post-dominates `node`. */
pragma[inline]
predicate strictlyPostDominates(ControlFlowNode dom, ControlFlowNode node) {
  // This predicate is gigantic, so it must be inlined.
  bbStrictlyPostDominates(dom.getBasicBlock(), node.getBasicBlock())
  or
  exists(BasicBlock b, int i, int j |
    dom = b.getNode(i) and node = b.getNode(j) and i > j
  )
}

/** Whether `dom` post-dominates `node`. (This is reflexive.) */
pragma[inline]
predicate postDominates(ControlFlowNode dom, ControlFlowNode node) {
  // This predicate is gigantic, so it must be inlined.
  bbStrictlyPostDominates(dom.getBasicBlock(), node.getBasicBlock())
  or
  exists(BasicBlock b, int i, int j |
    dom = b.getNode(i) and node = b.getNode(j) and i >= j
  )
}
