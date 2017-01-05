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
 * Modelling of Asynchronous Module Definitions (https://github.com/amdjs/amdjs-api/wiki/AMD).
 */

import Modules

/**
 * An AMD `define` call of the form
 *
 * ```
 * define(['a', 'b'], function(a, b) {
 *   ...
 * });
 * ```
 *
 * The first argument is an (optional) array of dependencies,
 * the second a factory method or object.
 *
 * We also recognize the three-argument form `define('m', ['a', 'b'], ...)`
 * where the first argument is the module name, the second argument an
 * array of dependencies, and the third argument a factory method or object.
 */
class AMDModuleDefinition extends CallExpr {
  AMDModuleDefinition() {
    getParent() instanceof ExprStmt and
    getCallee().(GlobalVarAccess).getName() = "define" and
    exists (int n | n = getNumArgument() |
      n = 1 or
      n = 2 and getArgument(0) instanceof ArrayExpr or
      n = 3 and getArgument(0) instanceof StringLiteral and getArgument(1) instanceof ArrayExpr
    )
  }

  /** Get the array of module dependencies, if any. */
  ArrayExpr getDependencies() {
    result = getArgument(0) or
    result = getArgument(1)
  }

  /** Get the i-th dependency of this module definition. */
  PathExpr getDependency(int i) {
    result = getDependencies().getElement(i)
  }

  /** Get some dependency of this module definition. */
  PathExpr getADependency() {
    result = getDependency(_) or
    result = getARequireCall().getAnArgument()
  }

  /** Get the factory expression of this module definition, which may be a function or a literal. */
  Expr getFactoryExpr() {
    result = getArgument(getNumArgument()-1).(DataFlowNode).getASource() and
    (result instanceof Function or
     result instanceof Literal or
     result instanceof ArrayExpr or
     result instanceof ObjectExpr)
  }

  /** Get the expression defining this module. */
  Expr getModuleExpr() {
    exists (Expr f | f = getFactoryExpr() |
      if f instanceof Function then
        exists (ReturnStmt ret | ret.getContainer() = f |
          result = ret.getExpr()
        )
      else
        result = f
    )
  }

  /**
   * Get the parameter corresponding to dependency `name`.
   *
   * For instance, in the module definition
   *
   * ```
   * define(['dep1', 'dep2'], function(pdep1, pdep2) { ... })
   * ```
   *
   * parameters `pdep1` and `pdep2` correspond to dependencies
   * `dep1` and `dep2`.
   */
  private SimpleParameter getDependencyParameter(string name) {
    exists (int i, Function f |
      f = getFactoryExpr() and
      getDependency(i).getValue() = name and
      result = f.getParameter(i)
    )
  }

  /**
   * Get the parameter corresponding to the pseudo-dependency `require`.
   */
  private SimpleParameter getRequireParameter() {
    result = getDependencyParameter("require") or
    // if no dependencies are listed, the first parameter is assumed to be `require`
    not exists(getDependencies()) and result = getFactoryExpr().(Function).getParameter(0)
  }

  /**
   * Get the parameter corresponding to the pseudo-dependency `exports`.
   */
  private SimpleParameter getExportsParameter() {
    result = getDependencyParameter("exports") or
    // if no dependencies are listed, the second parameter is assumed to be `exports`
    not exists(getDependencies()) and result = getFactoryExpr().(Function).getParameter(1)
  }

  /**
   * Get the parameter corresponding to the pseudo-dependency `module`.
   */
  private SimpleParameter getModuleParameter() {
    result = getDependencyParameter("module") or
    // if no dependencies are listed, the third parameter is assumed to be `module`
    not exists(getDependencies()) and result = getFactoryExpr().(Function).getParameter(2)
  }

  /**
   * Get an access to this module's `module` parameter, if any.
   */
  private VarAccess getAModuleAccess() {
    result = getModuleParameter().getVariable().getAnAccess()
  }

  /**
   * Get an access to this module's `exports`, either through the corresponding
   * parameter or through `module.exports`.
   */
  private Expr getAnExportsAccess() {
    result = getExportsParameter().getVariable().getAnAccess() or
    exists (PropAccess pacc | result = pacc |
      pacc.getBase().(DataFlowNode).getASource() = getAModuleAccess() and
      pacc.getPropertyName() = "exports"
    )
  }

  /**
   * Get an expression that may be exported by this module, either by virtue
   * of being returned from the factory function, or by being assigned to
   * `module.exports`. The `exports` parameter itself also always counts as being
   * exported.
   */
  DataFlowNode getAnExportedExpr() {
    result = getModuleExpr() or
    result = getAnExportsAccess() or
    exists (Assignment assgn |
      assgn.getTarget() instanceof PropAccess and
      assgn.getTarget() = getAnExportsAccess() and
      result = assgn.getRhs().(DataFlowNode).getASource()
    )
  }

  /**
   * Get a call to `require` inside this module.
   */
  CallExpr getARequireCall() {
    result.getCallee().stripParens() = getRequireParameter().getVariable().getAnAccess()
  }
}

/** A path expression appearing in the list of dependencies of an AMD module. */
library class AMDDependencyPath extends PathExpr {
  AMDDependencyPath() {
    this instanceof StringLiteral and
    exists (AMDModuleDefinition amd | this.getParentExpr*() = amd.getDependencies().getAnElement())
  }

  string getValue() { result = this.(StringLiteral).getValue() }
}

/** A path expression appearing in a `require` call in an AMD module. */
library class AMDRequirePath extends PathExpr {
  AMDRequirePath() {
    this instanceof StringLiteral and
    exists (AMDModuleDefinition amd | this.getParentExpr*() = amd.getARequireCall().getAnArgument())
  }

  string getValue() { result = this.(StringLiteral).getValue() }
}

/**
 * Helper predicate: `def` is an AMD module definition in `tl`, and it is
 * not nested inside another module definition.
 */
private predicate amdModuleTopLevel(AMDModuleDefinition def, TopLevel tl) {
  def.getTopLevel() = tl and
  not def.getParent+() instanceof AMDModuleDefinition
}

/**
 * An AMD-style module.
 */
class AMDModule extends Module {
  AMDModule() {
    strictcount (AMDModuleDefinition def | amdModuleTopLevel(def, this)) = 1
  }

  /** Get the definition of this module. */
  AMDModuleDefinition getDefine() {
    amdModuleTopLevel(result, this)
  }

  Module getAnImportedModule() {
    result.getFile() = resolve(getDefine().getADependency())
  }

  predicate exports(string name, ASTNode export) {
    exists (PropWriteNode pwn | pwn = export |
      pwn.getBase() = getDefine().getAnExportedExpr() and
      name = pwn.getPropertyName()
    )
  }
}