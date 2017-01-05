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
 * @name Unresolvable import
 * @description An import that cannot be resolved to a module will
 *              cause an exception at runtime.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       frameworks/node.js
 */

import javascript

PackageJSON getClosestPackageJSON(Folder f) {
  result = f.(NPMPackage).getPackageJSON() or
  not f instanceof NPMPackage and result = getClosestPackageJSON(f.getParent())
}

from Require r, string path, string mod
where path = r.getImportedPath().getValue() and

      // the imported module is the initial segment of the path, up to
      // `/` or the end of the string, whichever comes first; we exclude
      // local paths starting with `.` or `/`, since they might refer to files
      // downloaded or generated during the build
      mod = path.regexpCapture("([^./][^/]*)(/.*|$)", 1) and

      // exclude WebPack/Require.js loaders
      not mod.matches("%!%") and

      // import cannot be resolved statically
      not exists (r.getImportedModule()) and

      // no enclosing NPM package declares a dependency on `mod`
      forex (NPMPackage pkg, PackageJSON pkgJSON |
        pkg.getAModule() = r.getTopLevel() and pkgJSON = pkg.getPackageJSON() |
        not pkgJSON.declaresDependency(mod, _) and
        not pkgJSON.getPeerDependencies().getADependency(mod, _) and
        // exclude packages depending on `fbjs`, which automatically pulls in many otherwise
        // undeclared dependencies
        not pkgJSON.declaresDependency("fbjs", _)
      )
select r, "Module " + mod + " cannot be resolved, and is not declared as a dependency in $@.",
       getClosestPackageJSON(r.getFile().getParent()), "package.json"