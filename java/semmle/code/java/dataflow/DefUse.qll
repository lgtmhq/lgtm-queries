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
 * Statement-level def-use pairs. This may be inaccurate for multiple definitions
 * of variables in the same statement or multiple uses.
 *
 * DEPRECATED: use SSA library instead.
 */

import default
private import SSA

/**
 * An assignment to a variable or an initialization of the variable.
 *
 * DEPRECATED: use `VariableUpdate` instead.
 */
deprecated class VariableAssign extends Expr {
  VariableAssign() {
    ((AssignExpr)this).getDest() instanceof VarAccess or
    this instanceof LocalVariableDeclExpr
  }
  
  Expr getSource() {
    result = ((AssignExpr)this).getSource() or
    result = ((LocalVariableDeclExpr)this).getInit()
  }
  
  Variable getDestVar() {
    result.getAnAccess() = ((AssignExpr)this).getDest() or
    result = ((LocalVariableDeclExpr)this).getVariable()
  }
}

/** An update of a variable or an initialization of the variable. */
class VariableUpdate extends Expr {
	VariableUpdate() {
		this.(Assignment).getDest() instanceof VarAccess or
		this instanceof LocalVariableDeclExpr or
		this.(UnaryAssignExpr).getExpr() instanceof VarAccess
	}

	Variable getDestVar() {
		result.getAnAccess() = this.(Assignment).getDest() or
		result = this.(LocalVariableDeclExpr).getVariable() or
		result.getAnAccess() = this.(UnaryAssignExpr).getExpr()
	}
}

/**
 * Utility class for defs or uses.
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated abstract class DefOrUseStmt extends Stmt {}

/** A statement containing one or more definitions of variables.
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated
class DefStmt extends DefOrUseStmt {
  DefStmt() {
    definition(_, this)
  }
  
  /** A definition of `v` in this statement. */
  VariableAssign getADef(Variable v) {
    result.getDestVar() = v and result.getEnclosingStmt() = this
  }
  
  /** A variable that is defined in this statement. */
  Variable getADefinedVar() {
    exists(VariableAssign e | e.getEnclosingStmt() = this | result = e.getDestVar())
  }
}

/**
 * A statement containing one or more uses of variables.
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated
class UseStmt extends DefOrUseStmt {
  UseStmt() {
    useOfVar(_, this)
  }
  
  /** A use of `v` in this statement. */
  deprecated VarAccess getAUse(Variable v) {
    result.getVariable() = v and result.getEnclosingStmt() = this
  }
  
  /** A variable that is used in this statement. */
  deprecated Variable getAUsedVar() {
    exists(RValue e | e.getEnclosingStmt() = this | result = e.getVariable())
  }
}

deprecated
cached
predicate useOfVar(Variable v, Stmt s) {
  not v instanceof Field and
  exists(RValue r | r.getEnclosingStmt() = s | r.getVariable() = v)
}

deprecated
cached
predicate definition(Variable v, Stmt s) {
  not v instanceof Field and
  exists(VariableAssign a | a.getEnclosingStmt() = s | a.getDestVar() = v)
}

/**
 * Does the definition of `v` in `def` reach `use` along some control flow path
 * without crossing another definition of `v`?
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated
cached
predicate definitionReaches(Variable v, DefStmt def, Stmt use) {
  definition(v, def) and 
  (
	  use = def.getASuccessor()
	  or
	  exists(Stmt mid | 
	    // def reaches here
	    definitionReaches(v, def, mid) and
	    // not a redefinition of v
	    not definition(v, mid) and
	    // use is the successor
	    use = mid.getASuccessor()
	  )
  )
}

/**
 * Is this `use` statement a possible use of the value for `v` defined
 * in `def`?
 *
 * DEPRECATED: use `defUsePair(VariableUpdate def, RValue use)` instead.
 */
deprecated
predicate defUsePair(Variable v, DefStmt def, UseStmt use) {
  defUsePair(def.getADef(v), use.getAUse(v))
}

/**
 * Does the use of `v` in `use2` follow `use1` along some control flow path
 * without crossing a definition of `v`?
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated
cached
predicate useReaches(Variable v, UseStmt use1, Stmt use2) {
  useOfVar(v, use1) and 
  (
	  use2 = use1.getASuccessor()
	  or
	  exists(Stmt mid |
	    // use reaches here
	    useReaches(v, use1, mid) and
	    // not a redefinition of v
	    not definition(v, mid) and
	    // use2 is the successor
	    use2 = mid.getASuccessor()
	  )
  )
}

/**
 * Is `use2` a possible use of the variable `v` that could observe
 * the same value as `use1`?
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated
cached
predicate useUsePair(Variable v, UseStmt use1, UseStmt use2) {
  useReaches(v, use1, use2) and
  useOfVar(v, use2)
}

/**
 * Does a parameter value reach a use of the parameter variable along some control-flow path
 * without passing through a definition of that variable?
 *
 * DEPRECATED: use SSA library instead.
 */
deprecated
cached
predicate parameterReaches(Parameter p, Stmt use) {
  // base case - all parameters reach the body
  use = p.getCallable().getBody()
  or
  exists(Stmt mid | 
    // parameter reaches here
    parameterReaches(p, mid) and
    // not a redefinition of v
    not definition(p, mid) and
    // use is the successor
    use = mid.getASuccessor()
  )
}

/**
 * Is this `use` statement a use of the parameter `p` that could observe the
 * passed-in value?
 *
 * DEPRECATED: use `parameterDefUsePair(Parameter p, RValue use)` instead.
 */
deprecated
predicate parameterUse(Parameter p, UseStmt use) {
  parameterDefUsePair(p, use.getAUse(p))
}
