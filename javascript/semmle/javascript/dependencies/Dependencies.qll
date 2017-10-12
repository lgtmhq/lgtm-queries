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
 * Provides classes for modeling dependencies such as NPM packages
 * and framework libraries.
 */

import javascript
private import FrameworkLibraries
private import semmle.javascript.dependencies.DependencyCustomizations
private import semmle.javascript.frameworks.Emscripten

/**
 * An abstract representation of a dependency.
 */
abstract class Dependency extends Locatable {
  /**
   * Gets the unique identifier of this dependency.
   *
   * This should be treated as an opaque value.
   */
  abstract string getId();

  /**
   * Gets the version of the dependency, or `unknown` if the version
   * could not be determined.
   */
  abstract string getVersion();

  /**
   * A use of this dependency, which is of the given `kind`.
   *
   * Currently, the only supported kind is `"import"`.
   */
  abstract Locatable getAUse(string kind);
}

/**
 * A module in an NPM package, viewed as a dependency.
 *
 * This may either be a bundled NPM package that is included in
 * the source tree, or a package that is referenced as a dependency
 * in a `package.json` file.
 */
abstract class NPMDependency extends Dependency {
  /** Gets the name of the NPM package this module belongs to. */
  abstract string getNPMPackageName();

  /** Gets an import that imports to this module. */
  abstract Import getAnImport();

  override string getId() {
    result = getNPMPackageName()
  }

  override Locatable getAUse(string kind) {
    exists (Import i | i = getAnImport() |
      kind = "import" and result = i or
      kind = "use" and result = getATargetVariable(i).getAnAccess()
    )
  }
}

/**
 * Gets a variable into which something is imported by `i`.
 */
private Variable getATargetVariable(Import i) {
  // `var v = require('m')` or `var w = require('n').p`
  result.getAnAssignedValue().(DataFlowNode).getALocalSource() = propAccessOn*(i)
  or
  // `import { x as y }, * as z from 'm'`
  result = i.(ImportDeclaration).getASpecifier().getLocal().getVariable()
}

/**
 * Gets a property access of which `e` is the base.
 */
private Expr propAccessOn(Expr e) {
  result.(PropAccess).getBase() = e
}

/**
 * A bundled NPM module, that is, a module in a package whose source is
 * included in the database (as opposed to an `ExternalNPMDependency`
 * which is only referenced in a `package.json` file).
 */
class BundledNPMDependency extends NPMDependency {
  BundledNPMDependency() {
    exists (NPMPackage pkg | this = pkg.getAModule() |
      // exclude packages marked "private": they have no globally unique ID
      not pkg.getPackageJSON().isPrivate()
    )
  }

  /** Gets the package to which this module belongs. */
  private NPMPackage getPackage() {
    this = result.getAModule()
  }

  /** Gets the `package.json` of the package to which this module belongs. */
  private PackageJSON getPackageJSON() {
    result = getPackage().getPackageJSON()
  }

  override string getNPMPackageName() {
    result = getPackageJSON().getPackageName()
  }

  override string getVersion() {
    result = getPackageJSON().getVersion()
  }

  override Import getAnImport() {
    this = result.getImportedModule() and
    // ignore intra-package imports; they do not induce dependencies
    not result.getEnclosingModule() = getPackage().getAModule()
  }
}

/**
 * An NPM package referenced in a `package.json` file.
 */
class ExternalNPMDependency extends NPMDependency {
  ExternalNPMDependency() {
    exists (PackageJSON pkgjson |
      (JSONString)this = pkgjson.getADependenciesObject(_).getPropValue(_)
    )
  }

  /** Gets the NPM package declaring this dependency. */
  private NPMPackage getDeclaringPackage() {
    this = result.getPackageJSON().getADependenciesObject(_).getPropValue(_)
  }

  override string getNPMPackageName() {
    exists (PackageDependencies pkgdeps |
      this = pkgdeps.getPropValue(result)
    )
  }

  override string getVersion() {
    exists (string versionRange | versionRange = this.(JSONString).getValue() |
      // extract a concrete version from the version range; currently,
      // we handle exact versions as well as `<=`, `>=`, `~` and `^` ranges
      result = versionRange.regexpCapture("(?:[><]=|[=~^])?v?(\\d+(\\.\\d+){1,2})", 1) or
      // if no version is specified, report version `unknown`
      result = "unknown" and (versionRange = "" or versionRange = "*")
    )
  }

  override Import getAnImport() {
    exists (int depth | depth = importsDependency(result, getDeclaringPackage(), this) |
      // restrict to those results for which this is the closest matching dependency
      depth = min (importsDependency(result, _, _))
    )
  }
}

/**
 * Holds if import `i` may refer to the declared dependency `dep` of package `pkg`,
 * where the result value is the nesting depth of the file containing `i` within `pkg`.
 */
private int importsDependency(Import i, NPMPackage pkg, NPMDependency dep) {
  exists (string name |
    dep = pkg.getPackageJSON().getADependenciesObject(_).getPropValue(name) and
    not exists(i.getImportedModule()) and
    i.getImportedPath().getComponent(0) = name and
    i.getEnclosingModule() = pkg.getAModule() and
    result = distance(pkg, i.getFile())
  )
}

/**
 * Gets the nesting depth of `descendant` within `ancestor`.
 */
private int distance(Folder ancestor, Container descendant) {
  ancestor = descendant and result = 0 or
  result = 1 + distance(ancestor, descendant.getParentContainer())
}

/**
 * Holds if `e` is  of the form `g.x.y.z`, where `g` is an
 * access to a global variable and `.x.y.z` is a (possibly empty)
 * sequence of property accesses. The parameter `n` is bound
 * to the string `g.x.y.z`.
 */
private predicate propAccessOnGlobal(Expr e, string n) {
  e.accessesGlobal(n)
  or
  exists (PropAccess pacc, string q |
    pacc = e and propAccessOnGlobal(pacc.getBase(), q) |
    n = q + "." + pacc.getPropertyName()
  )
}

/**
 * A plain JavaScript library imported via a `<script>` tag.
 */
abstract class ScriptDependency extends Dependency {
  /**
   * Gets a use of a variable defined by the imported script.
   */
  abstract Expr getAnApiUse();

  override Locatable getAUse(string kind) {
    kind = "import" and (HTMLFile)result = this.getFile()
    or
    kind = "use" and result = getAnApiUse()
  }
}

/**
 * An embedded JavaScript library included inside a `<script>` tag.
 */
class InlineScriptDependency extends ScriptDependency, @toplevel {
  FrameworkLibrary fl;

  InlineScriptDependency() {
    fl = this.(FrameworkLibraryInstance).getFramework()
  }

  override string getId() {
    result = fl.getId()
  }

  override string getVersion() {
    result = this.(FrameworkLibraryInstance).getVersion()
  }

  override Expr getAnApiUse() {
    propAccessOnGlobal(result, fl.getAnEntryPoint()) and
    result.getFile() = this.getFile() and
    result.getTopLevel() != this
  }
}

/**
 * An external JavaScript library referenced via the `src` attribute
 * of a `<script>` tag.
 */
class ExternalScriptDependency extends ScriptDependency, @xmlattribute {
  FrameworkLibrary fl;

  ExternalScriptDependency() {
    fl = this.(FrameworkLibraryReference).getFramework()
  }

  override string getId() {
    result = fl.getId()
  }

  override string getVersion() {
    result = this.(FrameworkLibraryReference).getVersion()
  }

  override Expr getAnApiUse() {
    propAccessOnGlobal(result, fl.getAnEntryPoint()) and
    result.getFile() = this.getFile()
  }
}

/**
 * A dependency on GWT indicated by a GWT header script.
 */
private class GWTDependency extends ScriptDependency {
  GWTDependency() {
    this instanceof GWTHeader
  }

  override string getId() {
    result = "gwt"
  }

  override string getVersion() {
    exists (GWTHeader h | h = this |
      result = h.getGWTVersion() or
      not exists(h.getGWTVersion()) and result = "unknown"
    )
  }

  override Expr getAnApiUse() { none() }
}

/**
 * A dependency on the Google Closure library indicated by
 * a call to `goog.require` or `goog.provide`.
 */
private class GoogleClosureDep extends Dependency, @callexpr {
  GoogleClosureDep() {
    exists (MethodCallExpr mce |
      mce = this and mce.getReceiver().(GlobalVarAccess).getName() = "goog" |
      mce.getMethodName() = "require" or
      mce.getMethodName() = "provide"
    )
  }

  override string getId() {
    result = "closure"
  }

  override string getVersion() {
    result = "unknown"
  }

  override Locatable getAUse(string kind) {
    kind = "import" and
    result = this.(Expr).getTopLevel()
  }
}

/**
 * A dependency indicated by marker comment left by a code generator.
 */
private class GeneratorComment extends Dependency, @comment {
  GeneratorComment() {
    generatedBy(this, _)
  }

  override string getId() {
    generatedBy(this, result)
  }

  override string getVersion() {
    result = "unknown"
  }

  override Locatable getAUse(string kind) {
    kind = "generated" and
    result = this.(Comment).getTopLevel()
  }
}

/**
 * Holds if `c` is a marker comment left by the given `generator`.
 */
private predicate generatedBy(Comment c, string generator) {
  c instanceof EmscriptenMarkerComment and generator = "emscripten" or
  exists (string gn | gn = c.(CodeGeneratorMarkerComment).getGeneratorName() |
    // map generator names to their npm package names
    gn = "CoffeeScript" and generator = "coffee-script" or
    gn = "PEG.js" and generator = "pegjs" or
    gn != "CoffeeScript" and gn != "PEG.js" and generator = gn
  )
}

/**
 * A dependency indicated by an expression left by a module bundler.
 */
private class BundledTopLevel extends Dependency, @expr {
  BundledTopLevel() {
    isBrowserifyBundle(this) or
    isWebpackBundle(this)
  }

  override string getId() {
    isBrowserifyBundle(this) and result = "browserify" or
    isWebpackBundle(this) and result = "webpack"
  }

  override string getVersion() {
    result = "unknown"
  }

  override Locatable getAUse(string kind) {
    kind = "generated" and
    result = this.(Expr).getTopLevel()
  }
}
