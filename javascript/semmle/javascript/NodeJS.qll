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

import Modules
import DataFlow

/**
 * A Node.js module.
 */
class NodeModule extends Module {
  NodeModule() {
    isModule(this) and
    isNodejs(this)
  }

  /** Get the scope induced by this module. */
  ModuleScope getScope() {
    result.getScopeElement() = this
  }

  /** Get a `require` import in this module. */
  Require getAnImport() {
    result.getTopLevel() = this
  }

  /** Get a module imported by this module. */
  NodeModule getAnImportedModule() {
    result = getAnImport().getImportedModule()
  }

  /** Get an expression whose value flows into module.exports. */
  DataFlowNode getAnExportedExpr() {
    result = getAnExportsAccess() or
    exists (Assignment assgn, PropAccess lhs |
      // the left hand side of the assignment is a reference to module.exports
      lhs = assgn.getTarget() and
      lhs = getAnExportsAccess() and
      // the result is an expression that may flow into the right hand side
      result = assgn.getRhs().(DataFlowNode).getASource()
    )
  }

  /** Get a symbol exported by this module. */
  string getAnExportedSymbol() {
    result = super.getAnExportedSymbol() or
    result = getAnImplicitlyExportedSymbol()
  }

  predicate exports(string name, ASTNode export) {
    // a property write whose base is `exports` or `module.exports`
    exists (PropWriteNode pwn | export = pwn |
      pwn.getBase().getASource() = getAnExportedExpr() and
      name = pwn.getPropertyName()
    ) or
    // an externs definition (where appropriate)
    exists (PropAccess pacc | export = pacc |
      pacc.getBase().(DataFlowNode).getASource() = getAnExportedExpr() and
      name = pacc.getPropertyName() and
      isExterns() and exists(pacc.getDocumentation())
    )
  }

  /** Get a symbol that the module object inherits from its prototypes. */
  private string getAnImplicitlyExportedSymbol() {
    exists (ExternalConstructor ec | ec = getPrototypeOfExportedExpr() |
      result = ec.getAMember().getName() or
      ec instanceof FunctionExternal and result = "prototype" or
      ec instanceof ArrayExternal and exists (NumberLiteral nl | result = nl.getValue() and exists(result.toInt()))
    )
  }

  private ExternalConstructor getPrototypeOfExportedExpr() {
    exists (DataFlowNode exported | exported = getAnExportedExpr() |
      result instanceof ObjectExternal or
      exported instanceof Function and result instanceof FunctionExternal or
      exported instanceof ArrayExpr and result instanceof ArrayExternal
    )
  }

  /** Get a reference to `module.exports` in this module. */
  ExportsAccess getAnExportsAccess() {
    result.getTopLevel() = this
  }

  predicate searchRoot(PathExpr path, Folder searchRoot, int priority) {
    path.getTopLevel() = this and
    exists (string pathval | pathval = path.getValue() |
      // paths starting with `./` or `../` are resolved relative to the importing
      // module's folder
      if pathval.regexpMatch("\\.\\.?(/.*)?") then
        (searchRoot = getFile().getParent() and priority = 0)
      // paths starting with `/` are resolved relative to the file system root
      else if pathval.prefix(1) = "/" then
        (searchRoot.getName() = "" and priority = 0)
      // other paths are resolved relative to `node_modules` folders
      else
        findNodeModulesFolder(getFile().getParent(), searchRoot, priority)
    )
  }
}

/**
 * This predicate implements the `NODE_MODULES_PATHS` procedure from the
 * [specification of `require.resolve`](https://nodejs.org/api/modules.html#modules_all_together):
 * for a folder `f`, it finds all folders `nodeModules` whose path is of
 * the form `<prefix>/node_modules`, such that `<prefix>` is a (not necessarily
 * proper) prefix of the path of `f` and does not end in `/node_modules`;
 * `distance` is the number of path elements of `f` that are missing from `<prefix>`.
 *
 * For example, if `f` is `/a/node_modules/b`, we get the following results:
 *
 * <table border="1">
 * <tr><th><code>nodeModules</code></th><th><code>distance</code></th></tr>
 * <tr><td><code>/a/node_modules/b/node_modules</code></td><td>0</td></tr>
 * <tr><td><code>/a/node_modules</code></td><td>2</td></tr>
 * <tr><td><code>/node_modules</code></td><td>3</td></tr>
 * </table>
 */
private predicate findNodeModulesFolder(Folder f, Folder nodeModules, int distance) {
  nodeModules = f.getChild("node_modules") and not f.getName() = "node_modules" and distance = 0 or
  findNodeModulesFolder(f.getParent(), nodeModules, distance-1)
}

/**
 * A Node.js `require` variable.
 */
library class RequireVariable extends Variable {
  RequireVariable() {
    exists (ModuleScope m | this = m.getVariable("require"))
  }
}

/**
 * Helper predicate relating node modules and the files in which they occur.
 */
private predicate nodeModuleFile(NodeModule nm, File f) {
  nm.getFile() = f
}

/**
 * A `require` import.
 */
class Require extends CallExpr, Import {
  Require() {
    exists (RequireVariable req |
      this.getCallee() = req.getAnAccess()
    )
  }

  PathExpr getImportedPath() {
    result = getArgument(0)
  }

  NodeModule getEnclosingModule() {
    this = result.getAnImport()
  }

  NodeModule resolveImportedPath() {
    nodeModuleFile(result, load(min(int prio | nodeModuleFile(_, load(prio)))))
  }

  /**
   * Get the file that is imported by this `require`.
   *
   * The result can be a JavaScript file, a JSON file or a `.node` file.
   * Externs files are not treated differently from other files by this predicate.
   */
  File getImportedFile() {
    result = load(min(int prio | exists(load(prio))))
  }

  /**
   * Resolve this `require` to a file (which may not be a JavaScript file),
   * following the [specification of `require.resolve`](https://nodejs.org/api/modules.html#modules_all_together).
   *
   * Module resolution order is modelled using the `priority` parameter as follows.
   *
   * Each candidate folder in which the path may be resolved is assigned
   * a priority (this is actually done by `Module.searchRoot`, but we repeat it
   * here for completeness):
   *
   *   - if the path starts with `'./'`, `'../'`, or `/`, it has a single candidate
   *     folder (the enclosing folder of the module for the former two, the file
   *     system root for the latter) of priority 0
   *   - otherwise, candidate folders are folders of the form `<prefix>/node_modules`
   *     such that `<prefix>` is a (not necessarily proper) ancestor of the enclosing
   *     folder of the module which is not itself named `node_modules`; the priority
   *     of a candidate folder is the number of steps from the enclosing folder of
   *     the module to `<prefix>`.
   *
   * To resolve an import of a path `p`, we consider each candidate folder `c` with
   * priority `r` and resolve the import to the following files if they exist
   * (the scaling factor of 11 prevents results from different candidate folders
   * from overlapping):
   *
   * <ul>
   * <li> the file `c/p`, with priority `11*r`;
   * <li> the file `c/p.js`, with priority `11*r+1`;
   * <li> the file `c/p.json`, with priority `11*r+2`;
   * <li> the file `c/p.node`, with priority `11*r+3`;
   * <li> if `c/p` is a folder:
   *      <ul>
   *      <li> if `c/p/package.json` exists and specifies a `main` module `m`:
   *        <ul>
   *        <li> the file `c/p/m`, with priority `11*r+4`;
   *        <li> the file `c/p/m.js`, with priority `11*r+5`;
   *        <li> the file `c/p/m.json`, with priority `11*r+6`;
   *        <li> the file `c/p/m.node`, with priority `11*r+7`;
   *        </ul>
   *      <li> the file `c/p/index.js`, with priority `11*r+8`;
   *      <li> the file `c/p/index.json`, with priority `11*r+9`;
   *      <li> the file `c/p/index.node`, with priority `11*r+10`.
   *      </ul>
   * </ul>
   *
   * The first four steps are factored out into predicate `loadAsFile`,
   * the remainder into `loadAsDirectory`; both make use of an auxiliary
   * predicate `tryExtensions` that handles the repeated distinction between
   * `.js`, `.json` and `.node`.
   */
  private File load(int priority) {
    exists (int r | getEnclosingModule().searchRoot(getImportedPath(), _, r) |
      result = loadAsFile(this, r, priority-11*r) or
      result = loadAsDirectory(this, r, priority-(11*r+4))
    )
  }

  string toString() { result = CallExpr.super.toString() }
  CFGNode getFirstCFGNode() { result = CallExpr.super.getFirstCFGNode() }
}

private File loadAsFile(Require req, int rootPriority, int priority) {
  exists (PathExpr path | path = req.getImportedPath() |
    result = path.resolve(rootPriority) and priority = 0 or
    exists (Folder encl | encl = path.resolveUpTo(path.getNumComponent()-1, rootPriority) |
      result = tryExtensions(encl, path.getBaseName(), priority-1)
    )
  )
}

private File loadAsDirectory(Require req, int rootPriority, int priority) {
  exists (Folder dir | dir = req.getImportedPath().resolve(rootPriority) |
    exists (PackageJSON pkgjson | pkgjson.getFile() = dir.getAFile() |
      result = resolveMainModule(pkgjson, priority)
    ) or
    result = tryExtensions(dir, "index", priority-4)
  )
}

private File resolveMainModule(PackageJSON pkgjson, int priority) {
  exists (Folder dir, string main |
    dir = pkgjson.getFile().getParent() and main = pkgjson.getMain() |
    result = dir.getFile(main) and priority = 0 or
    result = tryExtensions(dir, main, priority-1)
  )
}

pragma[inline]
private File tryExtensions(Folder dir, string basename, int priority) {
  result = dir.getFile(basename + ".js") and priority = 0 or
  result = dir.getFile(basename + ".json") and priority = 1 or
  result = dir.getFile(basename + ".node") and priority = 2
}

/** A literal path expression appearing in a `require` import. */
library class LiteralRequiredPath extends PathExpr {
  LiteralRequiredPath() {
    this instanceof StringLiteral and
    exists (Require req | this.getParentExpr*() = req.getArgument(0))
  }

  string getValue() { result = this.(StringLiteral).getValue() }
}

/** A literal path expression appearing in a call to `require.resolve`. */
library class LiteralRequireResolvePath extends PathExpr {
  LiteralRequireResolvePath() {
    this instanceof StringLiteral and
    exists (RequireVariable req, MethodCallExpr reqres |
      reqres.getReceiver() = req.getAnAccess() and
      reqres.getMethodName() = "resolve" and
      this.getParentExpr*() = reqres.getArgument(0)
    )
  }

  string getValue() { result = this.(StringLiteral).getValue() }
}

/** A __dirname path expression. */
library class DirNamePath extends PathExpr, VarAccess {
  DirNamePath() {
    getName() = "__dirname" and
    getVariable().getScope() instanceof ModuleScope
  }

  string getValue() {
    result = getFile().getParent().getPath()
  }

  predicate isImpure() { VarAccess.super.isImpure() }
}

/** A __filename path expression. */
library class FileNamePath extends PathExpr, VarAccess {
  FileNamePath() {
    getName() = "__filename" and
    getVariable().getScope() instanceof ModuleScope
  }

  string getValue() {
    result = getFile().getPath()
  }

  predicate isImpure() { VarAccess.super.isImpure() }
}

/**
 * A path expression of the form `path.join(p, "...")` where
 * `p` is also a path expression.
 */
library class JoinedPath extends PathExpr {
  JoinedPath() {
    exists (MethodCallExpr call | call = this |
      call.getReceiver().(VarAccess).getName() = "path" and
      call.getMethodName() = "join" and
      call.getNumArgument() = 2 and
      call.getArgument(0) instanceof PathExpr and
      call.getArgument(1) instanceof StringLiteral
    )
  }

  string getValue() {
    exists (CallExpr call, PathExpr left, StringLiteral right |
      call = this and
      left = call.getArgument(0) and right = call.getArgument(1) |
      result = left.getValue() + "/" + right.getValue()
    )
  }
}

/** A reference to the special `module` variable. */
class ModuleAccess extends VarAccess {
  ModuleAccess() {
    exists (ModuleScope ms | this = ms.getVariable("module").getAnAccess())
  }
}

/**
 * A reference to the `exports` property, either through `module` or through its
 * variable alias.
 */
class ExportsAccess extends Expr {
  ExportsAccess() {
    exists (ModuleScope ms |
      this = ms.getVariable("exports").getAnAccess()
    ) or
    exists (PropAccess pacc | pacc = this |
      pacc.getBase().(DataFlowNode).getASource() instanceof ModuleAccess and
      pacc.getPropertyName() = "exports"
    )
  }
}