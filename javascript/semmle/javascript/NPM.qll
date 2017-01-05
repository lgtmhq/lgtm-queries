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
 * Classes for working with NPM module definitions and dependencies.
 */

import JSON
import NodeJS

/** A package.json object. */
class PackageJSON extends JSONObject {
  PackageJSON() {
    getFile().getName() = "package.json" and
    isTopLevel()
  }

  /** Get the name of this package. */
  string getPackageName() {
    result = getPropStringValue("name")
  }

  /** Get the version of this package. */
  string getVersion() {
    result = getPropStringValue("version")
  }

  /** Get the description of this package. */
  string getDescription() {
    result = getPropStringValue("description")
  }

  /** Get the array of keywords for this package. */
  JSONArray getKeywords() {
    result = getPropValue("keywords")
  }

  /** Get a keyword for this package. */
  string getAKeyword() {
    result = getKeywords().getElementStringValue(_)
  }

  /** Get the homepage URL of this package. */
  string getHomepage() {
    result = getPropStringValue("homepage")
  }

  /** Get the bug tracker information of this package. */
  BugTrackerInfo getBugs() {
    result = getPropValue("bugs")
  }

  /** Get the license information of this package. */
  string getLicense() {
    result = getPropStringValue("license")
  }
  
  /** Get the author information of this package. */
  ContributorInfo getAuthor() {
    result = getPropValue("author")
  }

  /** Get information for a contributor to this package. */
  ContributorInfo getAContributor() {
    result = ((JSONArray)getPropValue("contributors")).getElementValue(_)
  }

  /** Get the array of files for this package. */
  JSONArray getFiles() {
    result = getPropValue("files")
  }

  /** Get a file for this package. */
  string getAFile() {
    result = getFiles().getElementStringValue(_)
  }

  /** Get the main module of this package. */
  string getMain() {
    result = getPropStringValue("main")
  }

  /** Get the path of a command defined for this package. */
  string getBin(string cmd) {
    (cmd = getPackageName() and result = getPropStringValue("bin")) or
    result = ((JSONObject)getPropValue("bin")).getPropStringValue(cmd)
  }

  /** Get a man page for this package. */
  string getAManFile() {
    result = getPropStringValue("man") or
    result = ((JSONArray)getPropValue("man")).getElementStringValue(_)
  }

  /** Get information about the directories of this package. */
  JSONObject getDirectories() {
    result = getPropValue("directories")
  }

  /** Get repository information for this package. */
  RepositoryInfo getRepository() {
    result = getPropValue("repository")
  }

  /** Get information about the scripts of this package. */
  JSONObject getScripts() {
    result = getPropValue("scripts")
  }

  /** Get configuration information for this package. */
  JSONObject getConfig() {
    result = getPropValue("config")
  }

  /** Get the dependencies of this package. */
  PackageDependencies getDependencies() {
    result = getPropValue("dependencies")
  }

  /** Get the devDependencies of this package. */
  PackageDependencies getDevDependencies() {
    result = getPropValue("devDependencies")
  }

  /** Get the peerDependencies of this package. */
  PackageDependencies getPeerDependencies() {
    result = getPropValue("peerDependencies")
  }

  /** Get the bundledDependencies of this package. */
  PackageDependencies getBundledDependencies() {
    result = getPropValue("bundledDependencies") or
    result = getPropValue("bundleDependencies")
  }

  /** Get the optionalDependencies of this package. */
  PackageDependencies getOptionalDependencies() {
    result = getPropValue("optionalDependencies")
  }

  /**
   * Get a JSON object describing a group of dependencies of
   * this package, and bind `depkind` to a string describing
   * the kind of dependencies: `""` for normal dependencies,
   * `"dev"` for `devDependencies`, `"bundled"` for
   * `bundledDependencies` and `"opt"` for `optionalDependencies`. */
  PackageDependencies getADependenciesObject(string depkind) {
    result = getDependencies() and depkind = "" or
    result = getDevDependencies() and depkind = "dev" or
    result = getBundledDependencies() and depkind = "bundled" or
    result = getOptionalDependencies() and depkind = "opt"
  }

  /**
   * Does this package.json file declare a dependency (including
   * optional, dev and bundled dependencies) on the given version
   * of the given package?
   *
   * This does _not_ consider peer dependencies, which are semantically
   * different from the other dependency types.
   */
  predicate declaresDependency(string pkg, string version) {
    getADependenciesObject(_).getADependency(pkg, version)
  }

  /** Get the engine dependencies of this package. */
  PackageDependencies getEngines() {
    result = getPropValue("engines")
  }

  /** Does this package have strict engine requirements? */
  predicate isEngineStrict() {
    ((JSONBoolean)getPropValue("engineStrict")).getValue() = "true"
  }

  /** Get information about operating systems supported by this package. */
  JSONArray getOSs() {
    result = getPropValue("os")
  }

  /** Get an operating system supported by this package. */
  string getWhitelistedOS() {
    result = getOSs().getElementStringValue(_) and
    result.charAt(0) != "!"
  }

  /** Get an operating system not supported by this package. */
  string getBlacklistedOS() {
    exists (string str | str = getOSs().getElementStringValue(_) |
      str.charAt(0) = "!" and
      result = str.suffix(1)
    )
  }

  /** Get information about platforms supported by this package. */
  JSONArray getCPUs() {
    result = getPropValue("cpu")
  }

  /** Get a platform supported by this package. */
  string getWhitelistedCPU() {
    result = getCPUs().getElementStringValue(_) and
    result.charAt(0) != "!"
  }

  /** Get a platform not supported by this package. */
  string getBlacklistedCPU() {
    exists (string str | str = getCPUs().getElementStringValue(_) |
      str.charAt(0) = "!" and
      result = str.suffix(1)
    )
  }

  /** Does this package prefer to be installed globally? */
  predicate isPreferGlobal() {
    ((JSONBoolean)getPropValue("preferGlobal")).getValue() = "true"
  }

  /** Is this a private package? */
  predicate isPrivate() {
    ((JSONBoolean)getPropValue("private")).getValue() = "true"
  }

  /** Get publishing configuration information about this package. */
  JSONValue getPublishConfig() {
    result = getPropValue("publishConfig")
  }
}

/**
 * Bug tracker information for an npm package.
 */
class BugTrackerInfo extends JSONValue {
  BugTrackerInfo() {
    exists (PackageJSON pkg | pkg.getPropValue("bugs") = this) and
    (this instanceof JSONObject or this instanceof JSONString)
  }

  /** Get the bug tracker URL. */
  string getURL() {
    result = ((JSONObject)this).getPropStringValue("url") or
    result = ((JSONString)this).getValue()
  }

  /** Get the bug reporting email address. */
  string getEmail() {
    result = ((JSONObject)this).getPropStringValue("email")
  }
}

/**
 * Contributor information for an npm package.
 */
class ContributorInfo extends JSONValue {
  ContributorInfo() {
    exists (PackageJSON pkg |
      this = pkg.getPropValue("author") or
      this = ((JSONArray)pkg.getPropValue("contributors")).getElementValue(_)
    ) and
    (this instanceof JSONObject or this instanceof JSONString)
  }

  private string parseInfo(int group) {
    result = ((JSONString)this).getValue().regexpCapture("(.*?)(?: <(.*?)>)?(?: \\((.*)?\\))", group)
  }

  /** Get the contributor's name. */
  string getName() {
    result = ((JSONObject)this).getPropStringValue("name") or
    result = parseInfo(1)
  }

  /** Get the contributor's email address. */
  string getEmail() {
    result = ((JSONObject)this).getPropStringValue("email") or
    result = parseInfo(2)
  }
  
  /** Get the contributor's homepage URL. */
  string getURL() {
    result = ((JSONObject)this).getPropStringValue("url") or
    result = parseInfo(3)
  }
}

/**
 * Repository information for an npm package.
 */
class RepositoryInfo extends JSONObject {
  RepositoryInfo() {
    exists (PackageJSON pkg | this = pkg.getPropValue("repository"))
  }

  /** Get the repository type. */
  string getType() {
    result = getPropStringValue("type")
  }

  /** Get the repository URL. */
  string getURL() {
    result = getPropStringValue("url")
  }
}

/**
 * Package dependencies for an npm package.
 */
class PackageDependencies extends JSONObject {
  PackageDependencies() {
    exists (PackageJSON pkg, string name |
      name.regexpMatch("(.+D|d)ependencies|engines") and
      this = pkg.getPropValue(name)
    )
  }

  /** Does this package depend on version 'version' of package 'pkg'? */
  predicate getADependency(string pkg, string version) {
    version = getPropStringValue(pkg)
  }
}

/**
 * An npm package.
 */
class NPMPackage extends Folder {
  NPMPackage() {
    exists (PackageJSON pkg | pkg.getFile().getParent() = this)
  }

  /** Get the package.json object of this package. */
  PackageJSON getPackageJSON() {
    result.getFile().getParent() = this
  }

  /** Get the name of this package. */
  string getPackageName() {
    result = getPackageJSON().getPackageName()
  }

  /** Get the node_modules folder of this package. */
  Folder getNodeModulesFolder() {
    result.getName() = "node_modules" and
    result.getParent() = this
  }

  /**
   * Get a node.js module belonging to this package.
   *
   * We only consider modules to belong to the nearest enclosing package,
   * and modules inside the `node_modules` folder of a package are not
   * considered to belong to that package.
   */
  Module getAModule() {
    this = packageInternalParent*(result.getFile().getParent())
  }
}

/**
 * Get the parent folder of `c`, provided that they belong to the same npm
 * package; that is, `c` must not be a `node_modules` folder.
 */
private Folder packageInternalParent(Container c) {
  result = c.getParent() and
  not c.(Folder).getName() = "node_modules"
}