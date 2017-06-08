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
 * Provides classes for working with JavaScript modules, both
 * ECMAScript 2015-style modules, and the older CommonJS and AMD-style
 * modules.
 */

import Variables
import Paths

/**
 * A module, which may either be an ECMAScript 2015-style module,
 * a CommonJS module, or an AMD module.
 */
abstract class Module extends TopLevel {
  /** Gets the full path of the file containing this module. */
  string getPath() {
    result = getFile().getAbsolutePath()
  }

  /** Gets the short name of this module without file extension. */
  string getName() {
    result = getFile().getStem()
  }

  /** Gets a module from which this module imports. */
  abstract Module getAnImportedModule();

  /** Gets a symbol exported by this module. */
  string getAnExportedSymbol() {
    exports(result, _)
  }

  /**
   * Holds if this module explicitly exports symbol `name` at the
   * program element `export`.
   *
   * Note that in some module systems (notably CommonJS and AMD)
   * modules are arbitrary objects that export all their
   * properties. This predicate only considers properties
   * that are explicitly defined on the module object.
   *
   * Symbols defined in another module that are re-exported by
   * this module are not considered either.
   */
  abstract predicate exports(string name, ASTNode export);

  /**
   * Gets the root folder relative to which the given import path (which must
   * appear in this module) is resolved.
   *
   * Each root has an associated priority, and roots with numerically smaller
   * priority are preferred during import resolution.
   *
   * This predicate is not part of the public API, it is only exposed to allow
   * overriding by subclasses.
   */
  predicate searchRoot(PathExpr path, Folder searchRoot, int priority) {
    path.getTopLevel() = this and
    priority = 0 and
    exists (string v | v = path.getValue() |
      // paths starting with a dot are resolved relative to the module's directory
      if v.matches(".%") then
        searchRoot = getFile().getParentContainer()
      // all other paths are resolved relative to the file system root
      else
        searchRoot.getBaseName() = ""
    )
  }

  /**
   * Gets the file to which the import path `path`, which must appear in this
   * module, resolves.
   *
   * If the path resolves to a file directly, this is the result. If the path
   * resolves to a folder containing a main module (such as `index.js`), then
   * that file is the result.
   */
  File resolve(PathExpr path) {
    path.getTopLevel() = this and
    (
     // handle the case where the import path is complete
     exists (Container c | c = path.resolve() |
       // import may refer to a file...
       result = c or
       // ...or to a directory, in which case we import index.js in that directory
       result = c.(Folder).getFile("index.js")
     ) or

     // handle the case where the import path is missing an extension
     exists (Folder f | f = path.resolveUpTo(path.getNumComponent()-1) |
       result = f.getFile(path.getBaseName() + ".js")
     )
    )
  }
}

/**
 * An import in a module, which may either be an ECMAScript 2015-style
 * `import` statement or a CommonJS-style `require` import.
 */
abstract class Import extends ASTNode {
  /** Gets the module in which this import appears. */
  abstract Module getEnclosingModule();

  /** Gets the (unresolved) path that this import refers to. */
  abstract PathExpr getImportedPath();

  /**
   * Gets an externs module the path of this import resolves to.
   *
   * Any externs module whose name exactly matches the imported
   * path is assumed to be a possible target of the import.
   */
  Module resolveExternsImport() {
    result.isExterns() and result.getName() = getImportedPath().getValue()
  }

  /**
   * Gets the module the path of this import resolves to.
   */
  Module resolveImportedPath() {
    result.getFile() = getEnclosingModule().resolve(getImportedPath())
  }

  /**
   * Gets a module with a `@providesModule` JSDoc tag that matches
   * the imported path.
   */
  private Module resolveAsProvidedModule() {
    exists (JSDocTag tag |
      tag.getTitle() = "providesModule" and
      tag.getParent().getComment().getTopLevel() = result and
      tag.getDescription().trim() = getImportedPath().getValue()
    )
  }

  /**
   * Gets the module this import refers to.
   *
   * The result is either an externs module, or an actual source module;
   * in cases of ambiguity, the former are preferred. This models the runtime
   * behavior of Node.js imports, which prefer core modules such as `fs` over any
   * source module of the same name.
   */
  Module getImportedModule() {
    if exists(resolveExternsImport()) then
      result = resolveExternsImport()
    else
      (result = resolveAsProvidedModule() or
       result = resolveImportedPath())
  }
}

/**
 * A path expression that appears in a module and is resolved relative to it.
 */
abstract class PathExprInModule extends PathExpr {
  PathExprInModule() {
    getTopLevel() instanceof Module
  }

  override Folder getSearchRoot(int priority) {
    getTopLevel().(Module).searchRoot(this, result, priority)
  }
}

/**
 * An import of a module with the given `path`, either using `require` or using `import`.
 */
private predicate isImport(DataFlowNode nd, string moduleName) {
  exists (Import i | i.getImportedPath().getValue() = moduleName |
    // `require("http")`
    nd = (Require)i or
    // `import * as http from 'http'`
    nd = i.(ImportDeclaration).getASpecifier().(ImportNamespaceSpecifier).getLocal()
  )
}

/**
 * A data flow node that holds a module instance, that is, the result of
 * an import of the module.
 */
class ModuleInstance extends DataFlowNode {
  ModuleInstance() {
    isImport(this, _)
  }

  /** Gets the path from which the module is imported. */
  string getPath() {
    isImport(this, result)
  }

  /**
   * Gets a function call that invokes method `methodName` on this module instance.
   */
  CallExpr getAMethodCall(string methodName) {
    exists (PropReadNode prn |
      prn.getBase().getALocalSource() = this and
      prn.getPropertyName() = methodName and
      result.getCallee().(DataFlowNode).getALocalSource() = prn
    )
  }
}