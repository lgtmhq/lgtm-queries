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
 * @name Unused npm dependency
 * @description If unnecessary package dependencies are included in package.json, the
 *              package will become harder to install.
 * @kind problem
 * @problem.severity warning
 * @id js/node/unused-npm-dependency
 * @tags maintainability
 *       frameworks/node.js
 * @precision very-high
 */

import javascript

/**
 * Holds if the NPM package `pkg` declares a dependency on package `name`,
 * and `dep` is the corresponding declaration in the `package.json` file.
 */
predicate declaresDependency(NPMPackage pkg, string name, JSONValue dep) {
  dep = pkg.getPackageJSON().getDependencies().getPropValue(name)
}

/**
 * Gets a path expression in a module belonging to `pkg`.
 */
PathExpr getAPathExpr(NPMPackage pkg) {
  result.getTopLevel() = pkg.getAModule()
}

/**
 * Gets a URL-valued attribute in a module or HTML file belonging to `pkg`.
 */
URLValuedAttribute getAURLAttribute(NPMPackage pkg) {
  result.getFile() = pkg.getAFile()
}

/**
 * Gets the name of a script in the 'scripts' object of `pkg`.
 * The script makes use of a declared `dependency` of `pkg`.
 */
string getPackageScriptNameWithDependency(NPMPackage pkg, string dependency){
    exists (JSONObject scriptsObject, string scriptName, string script |
        declaresDependency(pkg, dependency, _) and
        scriptsObject = pkg.getPackageJSON().getPropValue("scripts") and
        script = scriptsObject.getPropStringValue(scriptName) and
        script.regexpMatch(".*\\b\\Q" + dependency + "\\E\\b.*") and
        result = scriptName
    )
}

/**
 * Holds if the NPM package `pkg` declares a dependency on package `name`,
 * and uses it at least once.
 */
predicate usesDependency(NPMPackage pkg, string name) {
  declaresDependency(pkg, name, _) and
  (
    // there is a path expression (e.g., in a `require` or `import`) that
    // references `pkg`
    exists (PathExpr path | path = getAPathExpr(pkg) |
      // check whether the path is `name` or starts with `name/`
      path.getValue().regexpMatch("\\Q" + name + "\\E(/.*)?")
    )
    or
    // there is an HTML URL attribute that may reference `pkg`
    exists (URLValuedAttribute attr | attr = getAURLAttribute(pkg) |
      // check whether the URL contains `node_modules/name`
      attr.getURL().regexpMatch(".*\\bnode_modules/\\Q" + name + "\\E(/.*)?")
    )
    or
    // there is a reference in a package.json white-listed script
    exists (string packageScriptName |
      packageScriptName = getPackageScriptNameWithDependency(pkg, name) |
      packageScriptName = "preinstall" or
      packageScriptName = "install" or
      packageScriptName = "postinstall"
    )
  )
}

/**
 * Holds if `pkg` implicitly requires module `name`.
 *
 * Currently, the only implicit requires that are recognized are Express
 * view engine definitions, which (may) implicitly require the specified
 * engine as a module.
 */
predicate implicitRequire(NPMPackage pkg, string name) {
  // look for Express `set('view engine', ...)` calls
  exists (MethodCallExpr setViewEngine, string engine |
    Express::isApp(setViewEngine.getReceiver()) and
    setViewEngine.getMethodName() = "set" and
    setViewEngine.getArgument(0).getStringValue() = "view engine" and
    setViewEngine.getArgument(1).getStringValue() = engine and
    setViewEngine.getTopLevel() = pkg.getAModule() |
    // chop off leading dot, if any
    if engine.matches(".%") then
      name = engine.suffix(1)
    else
      name = engine
  )
}

from NPMPackage pkg, string name, JSONValue dep
where exists (pkg.getAModule()) and
      declaresDependency(pkg, name, dep) and
      not usesDependency(pkg, name) and
      not implicitRequire(pkg, name)
select dep, "Unused dependency '" + name + "'."
