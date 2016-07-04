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

import Variables
import Paths

/**
 * A module.
 */
abstract class Module extends TopLevel, @script {
  /** Get the full path of the file containing this module. */
  string getPath() {
    result = getFile().getPath()
  }

  /** Get the short name of this module without file extension. */
  string getName() {
    result = getFile().getShortName()
  }

  /** Get a module from which this module imports. */
  abstract Module getAnImportedModule();

  /** Get a symbol exported by this module. */
  string getAnExportedSymbol() {
    exports(result, _)
  }

  /**
   * This module explicitly exports symbol `name` at the AST
   * node `export`.
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
   * Determine the root folder relative to which the given import path (which must
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
    // paths starting with a dot are resolved relative to the module's directory
    if path.getValue().matches(".%") then
      searchRoot = getFile().getParent()
    // all other paths are resolved relative to the file system root
    else
      searchRoot.getName() = ""
  }

  /**
   * Resolve an import path appearing somewhere in the module.
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

  string toString() {
    result = getName()
  }
}

/**
 * An import in a module.
 */
abstract class Import extends ASTNode {
  /** Get the module in which this import appears. */
  abstract Module getEnclosingModule();

  /** Get the (unresolved) path that this import refers to. */
  abstract PathExpr getImportedPath();

  /** Get the module this import refers to. */
  abstract Module getImportedModule();
}
