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
 * Library for control-flow graph dominance.
 */
import default
private import semmle.code.java.Successor
private import semmle.code.java.ControlFlowGraph

 /*
  * Predicates for statement-level dominance.
  */
  
/** Entry points for control-flow. */
private predicate flowEntry(Stmt entry) {
  exists (Callable c | entry = c.getBody())
}

predicate succs(ControlFlowNode s, ControlFlowNode succ) { succ = s.getASuccessor() }

/** Immediate dominance relation on control-flow graph nodes. */
predicate iDominates(ControlFlowNode dominator, ControlFlowNode node)
  = idominance(flowEntry/1,succs/2)(dominator, node)

/** Exit points for control-flow. */
private predicate flowExit(Callable exit) {
  exists(ControlFlowNode s | s.getASuccessor() = exit)
}

/** Reversed `succs`. */
private predicate preds(ControlFlowNode post, ControlFlowNode pre) { succs(pre, post) }

/** Immediate post-dominance relation on control-flow graph nodes. */
predicate iPostDominates(ControlFlowNode dominator, ControlFlowNode node)
  = idominance(flowExit/1,preds/2)(dominator, node)

/** Whether `dom` strictly dominates `node`. */
predicate strictlyDominates(ControlFlowNode dom, ControlFlowNode node) { iDominates+(dom, node) }

/** Whether `dom` dominates `node`. (This is reflexive.) */
predicate dominates(ControlFlowNode dom, ControlFlowNode node) { strictlyDominates(dom, node) or dom = node }

/** Whether `dom` strictly post-dominates `node`. */
predicate strictlyPostDominates(ControlFlowNode dom, ControlFlowNode node) { iPostDominates+(dom, node) }

/** Whether `dom` post-dominates `node`. (This is reflexive.) */
predicate postDominates(ControlFlowNode dom, ControlFlowNode node) { strictlyPostDominates(dom, node) or dom = node }

 /*
  * Predicates for basic-block-level dominance.
  */

/** The successor relation for basic blocks. */
private predicate bbSucc(BasicBlock pre, BasicBlock post) {
  post = pre.getABBSuccessor()
}

/** The immediate dominance relation for basic blocks. */
predicate bbIDominates(BasicBlock dom, BasicBlock node)
  = idominance(flowEntry/1, bbSucc/2)(dom, node)

/** Exit points for basic-block control-flow. */
private predicate bbSink(BasicBlock exit) {
  flowExit(exit.getLastNode())
}

/** Reversed `bbSucc`. */
private predicate bbPred(BasicBlock post, BasicBlock pre) {
  post = pre.getABBSuccessor()
}

/** The immediate post-dominance relation on basic blocks. */
predicate bbIPostDominates(BasicBlock dominator, BasicBlock node)
  = idominance(bbSink/1,bbPred/2)(dominator, node)

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
