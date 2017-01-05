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
 * QL classes for identifying popular framework libraries.
 *
 * Each framework is identified by a subclass of `FrameworkLibrary`,
 * which is simply a tag identifying the library, such as `"jquery"`.
 * This represents the framework as an abstract concept.
 *
 * Subclasses of `FrameworkLibraryInstance` identify concrete instances
 * (or copies) of frameworks, that is, files (or scripts embedded in
 * HTML) containing the implementation of a particular version of
 * a framework library.
 *
 * Subclasses of `FrameworkLibraryReference` identify HTML `<script>`
 * tags that refer to a particular version of a framework library.
 *
 * Typically, framework library instances are identified by looking
 * for marker comments, while framework library references are
 * identified by analyzing the URL referenced in the `src` attribute.
 *
 * Common patterns for doing this are encapsulated by classes
 * `FrameworkLibraryWithMarkerComment` and `FrameworkLibraryWithGenericURL`,
 * which identify framework libraries by matching their marker comment and
 * URL, respectively, against a regular expression. Most frameworks can
 * be represented by a single class extending both of these two classes
 * (for example `Bootstrap` and `React`), while other frameworks have
 * more complex rules for recognizing instances (for example `MooTools`).
 */

import javascript

/**
 * An abstract representation of a framework library.
 */
abstract class FrameworkLibrary extends string {
  pragma[inline] FrameworkLibrary() { any() }

  /**
   * The unique identifier of this framework library.
   *
   * By default, this is simply the name of the framework,
   * but it should be treated as an opaque value.
   */
  string getId() { result = this }
}

/**
 * An instance (or copy) of a framework library, that is,
 * a file or script containing the code for a particular
 * version of a framework.
 */
abstract class FrameworkLibraryInstance extends Script {
  /**
   * The framework of which this is an instance.
   */
  abstract FrameworkLibrary getFramework();

  /**
   * The version of the framework of which this is an instance.
   */
  abstract string getVersion();
}

/**
 * An abstract representation of a reference to a framework library
 * via the `src` attribute of a `<script>` element.
 */
abstract class FrameworkLibraryReference extends HTMLAttribute {
  FrameworkLibraryReference() {
    getName() = "src" and getElement().getName() = "script"
  }

  /**
   * The framework to which this is a reference.
   */
  abstract FrameworkLibrary getFramework();

  /**
   * The version of the framework to which this is a reference.
   */
  abstract string getVersion();
}

/**
 * A framework library whose instances can be identified by marker comments.
 */
abstract class FrameworkLibraryWithMarkerComment extends FrameworkLibrary {
  pragma[inline] FrameworkLibraryWithMarkerComment() { any() }

  /**
   * A regular expression that can be used to identify an instance of
   * this framework library.
   *
   * The first capture group of this regular expression should match
   * the version number.
   */
  abstract string getAMarkerCommentRegex();
}

/**
 * A framework library that is referenced by URLs that have a certain
 * pattern.
 */
abstract class FrameworkLibraryWithURLRegex extends FrameworkLibrary {
  pragma[inline] FrameworkLibraryWithURLRegex() { any() }

  /**
   * A regular expression that can be used to identify a URL referring
   * to this framework library.
   *
   * The first capture group of this regular expression should match
   * the version number.
   */
  abstract string getAURLRegex();
}

/**
 * A framework library that is referenced by URLs containing the name
 * of the framework (or an alias) and a version string.
 *
 * We currently recognize two kinds of URLs:
 *
 *   * URLs whose last component is `<framework id>-<version>.js`,
 *     possibly with some variant suffixes before the `.js`;
 *   * URLs of the form `.../<version>/<framework id>.js`,
 *     again possibly with suffixes before the `.js`; additionally,
 *     we allow a path component between `<version>` and `<framework id>`
 *     that repeats `<framework id>`, or is one of `dist` and `js`.
 *
 * See `variantRegex()` below for a discussion of variant suffixes.
 */
abstract class FrameworkLibraryWithGenericURL extends FrameworkLibraryWithURLRegex {
  pragma[inline] FrameworkLibraryWithGenericURL() { any() }

  string getAnAlias() { none() }

  string getAURLRegex() {
    exists (string id | id = getId() or id = getAnAlias() |
      result = ".*(?:^|/)" + id + "-(" + semverRegex() + ")" + variantRegex() + "\\.js" or
      result = ".*/(?:\\w+@)?(" + semverRegex() + ")/(?:(?:dist|js|" + id + ")/)?" + id + variantRegex() + "\\.js"
    )
  }
}

/**
 * Suffixes that are commonly appended to the name of a library
 * to distinguish minor variants. We ignore these when identifying
 * frameworks.
 */
private string variantRegex() {
  result = "([.-](slim|min|debug|dbg|umd|dev|all|testing|polyfills|" +
                 "core|compat|more|modern|sandbox|rtl|with-addons|legacy))*"
}

/**
 * Helper predicate encapsulating a regular expression for matching
 * version numbers in URLs.
 *
 * We currently accept version numbers of the form
 * `<major>.<minor>.<patch>-beta.<n>`, where `.<patch>` and/or
 * `-beta.<n>` may be missing.
 */
private string semverRegex() {
  result = "\\d+\\.\\d+(?:\\.\\d+)?(?:-beta\\.\\d+)?"
}


/**
 * An instance of a `FrameworkLibraryWithMarkerComment`.
 */
library class FrameworkLibraryInstanceWithMarkerComment extends FrameworkLibraryInstance {
  FrameworkLibraryInstanceWithMarkerComment() { matchMarkerComment(_, this, _, _) }
  FrameworkLibrary getFramework() { matchMarkerComment(_, this, result, _) }
  string getVersion() { matchMarkerComment(_, this, _, result) }
}

/**
 * Helper predicate identifying comments matching a regular expression
 * supplied by a `FrameworkLibraryWithMarkerComment`.
 */
private predicate matchMarkerComment(Comment c, TopLevel tl,
                                     FrameworkLibraryWithMarkerComment fl, string version) {
  c.getTopLevel() = tl and
  version = c.getText().regexpCapture(fl.getAMarkerCommentRegex(), 1)
}


/**
 * A reference to a `FrameworkLibraryWithURL`.
 */
library class FrameworkLibraryReferenceWithURL extends FrameworkLibraryReference {
  FrameworkLibraryReferenceWithURL() { matchURL(this, _, _) }
  FrameworkLibrary getFramework() { matchURL(this, result, _) }
  string getVersion() { matchURL(this, _, result) }
}

/**
 * Helper predicate identifying `src` attributes where the URL matches
 * a regular expression supplied by a `FrameworkLibraryWithURL`.
 */
private predicate matchURL(HTMLAttribute attr, FrameworkLibraryWithURLRegex fl, string version) {
  version = attr.getValue().regexpCapture(fl.getAURLRegex(), 1)
}


/**
 * Helper predicate encapsulating a regular expression for matching
 * versions specified in marker comments.
 */
private string versionRegex() {
  result = "\\d+\\.\\d+[A-Za-z0-9.+_-]*"
}


/**
 * jQuery
 */
class JQuery extends FrameworkLibraryWithGenericURL {
  JQuery() { this = "jquery" }
}

/**
 * Helper predicate for identifying jQuery's marker comment.
 */
private predicate jQueryMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  exists (string txt | txt = c.getText() |
    // more recent versions use this format
    version = txt.regexpCapture("(?s).*jQuery (?:JavaScript Library )?v(" + versionRegex() + ").*", 1) or
    // earlier versions used this format
    version = txt.regexpCapture("(?s).*jQuery (" + versionRegex() + ") - New Wave Javascript.*", 1) or
    // 1.0.0 and 1.0.1 have the same marker comment; we call them both "1.0"
    txt.matches("%jQuery - New Wave Javascript%") and version = "1.0"
  )
}

/**
 * A copy of jQuery.
 */
class JQueryInstance extends FrameworkLibraryInstance {
  JQueryInstance() { jQueryMarkerComment(_, this, _) }
  JQuery getFramework() { any() }
  string getVersion() { jQueryMarkerComment(_, this, result) }
}


/**
 * jQuery Mobile
 */
class JQueryMobile extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  JQueryMobile() { this = "jquery-mobile" }
  string getAnAlias() { result = "jquery.mobile" }
  string getAMarkerCommentRegex() { result = "(?s).*jQuery Mobile (" + versionRegex() + ").*" }
}


/**
 * jQuery UI
 */
class JQueryUI extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  JQueryUI() { this = "jquery-ui" }
  string getAMarkerCommentRegex() { result = "(?s).*jQuery UI - v?(" + versionRegex() + ").*" }
}

/**
 * jQuery TextExt
 */
class JQueryTextExt extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  JQueryTextExt() { this = "jquery-textext" }
  string getAnAlias() { result = "jquery.textext" }
  string getAMarkerCommentRegex() {
    result = "(?s).*jQuery TextExt Plugin.*@version (" + versionRegex() + ").*"
  }
}

/**
 * Bootstrap
 */
class Bootstrap extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Bootstrap() { this = "bootstrap" }
  string getAMarkerCommentRegex() {
    result = "(?s).*Bootstrap v(" + versionRegex() + ") \\(http://getbootstrap.com\\).*"
  }
}

/**
 * Modernizr
 */
class Modernizr extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Modernizr() { this = "modernizr" }
  string getAMarkerCommentRegex() {
    result = "(?s).*(?<!@license )Modernizr (?:JavaScript library )?v?(" + versionRegex() + ").*"
  }
}

/**
 * MooTools
 */
class MooTools extends FrameworkLibraryWithGenericURL {
  MooTools() { this = "mootools" }
}

/**
 * MooTools puts an object into `this.MooTools` that contains version information;
 * this helper predicate identifies the definition of that object, which is always of the form
 *
 * ```javascript
 * this.MooTools = { version: "<version>", ... }
 * ```
 */
private predicate mooToolsObject(ObjectExpr oe, TopLevel tl, string version) {
  exists (AssignExpr assgn, DotExpr d |
    tl = oe.getTopLevel() and assgn.getLhs() = d and assgn.getRhs() = oe |
    d.getBase() instanceof ThisExpr and
    d.getPropertyName() = "MooTools" and
    version = oe.getPropertyByName("version").getInit().(StringLiteral).getValue()
  )
}

/**
 * A copy of MooTools.
 */
class MooToolsInstance extends FrameworkLibraryInstance {
  MooToolsInstance() { mooToolsObject(_, this, _) }
  MooTools getFramework() { any() }
  string getVersion() { mooToolsObject(_, this, result) }
}


/**
 * Prototype
 */
class Prototype extends FrameworkLibraryWithGenericURL {
  Prototype() { this = "prototype" }
}
 
/**
 * Prototype declares a variable `Prototype` containing an object with version information;
 * this helper predicates identifies the definition of that object, which is always of the form
 *
 * ```javascript
 * var Prototype = { Version: '<version>', ... }
 * ```
 */
private predicate prototypeObject(ObjectExpr oe, TopLevel tl, string version) {
  exists (VariableDeclarator vd | tl = vd.getTopLevel() and oe = vd.getInit() |
    vd.getBindingPattern().(Identifier).getName() = "Prototype" and
    version = oe.getPropertyByName("Version").getInit().(StringLiteral).getValue()
  )
}

/**
 * A copy of Prototype.
 */
class PrototypeInstance extends FrameworkLibraryInstance {
  PrototypeInstance() { prototypeObject(_, this, _) }
  Prototype getFramework() { any() }
  string getVersion() { prototypeObject(_, this, result) }
}


/**
 * Scriptaculous
 */
class Scriptaculous extends FrameworkLibraryWithGenericURL {
  Scriptaculous() { this = "scriptaculous" }
}

/**
 * Scriptaculous declares a variable `Scriptaculous` containing an object with version information;
 * this helper predicates identifies the definition of that object, which is always of the form
 *
 * ```javascript
 * var Scriptaculous = { Version: '<version>', ... }
 * ```
 */
private predicate scriptaculousObject(ObjectExpr oe, TopLevel tl, string version) {
  exists (VariableDeclarator vd | tl = vd.getTopLevel() and oe = vd.getInit() |
    vd.getBindingPattern().(Identifier).getName() = "Scriptaculous" and
    version = oe.getPropertyByName("Version").getInit().(StringLiteral).getValue()
  )
}

/**
 * A copy of Scriptaculous.
 */
class ScriptaculousInstance extends FrameworkLibraryInstance {
  ScriptaculousInstance() { scriptaculousObject(_, this, _) }
  Scriptaculous getFramework() { any() }
  string getVersion() { scriptaculousObject(_, this, result) }
}


/**
 * Underscore
 */
class Underscore extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Underscore() { this = "underscore" }
  string getAMarkerCommentRegex() { result = "^\\s*Underscore.js (" + versionRegex() + ").*" }
}


/**
 * Lodash
 */
class Lodash extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Lodash() { this = "lodash" }

  string getAMarkerCommentRegex() {
    result = "(?s).* (?:lod|Lo-D)ash (" + versionRegex() + ")" +
             "(?: \\(Custom Build\\))? " +
             "<https?://lodash.com/>.*"
  }
}


//
// Dojo
//
class Dojo extends FrameworkLibraryWithGenericURL {
  Dojo() { this = "dojo" }
}

/**
 * Helper predicate for identifying Dojo's marker comment.
 */
private predicate dojoMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  c.getText().regexpMatch("(?s).*Copyright \\(c\\) 2004-20.., The Dojo Foundation.*") and
  // Dojo doesn't embed a version string
  version = "*"
}

/**
 * A copy of Dojo.
 */
class DojoInstance extends FrameworkLibraryInstance {
  DojoInstance() { dojoMarkerComment(_, this, _) }
  Dojo getFramework() { any() }
  string getVersion() { dojoMarkerComment(_, this, result) }
}


/**
 * ExtJS
 */
class ExtJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  ExtJS() { this = "extjs" }

  string getAMarkerCommentRegex() {
    result = "(?s).*This file is part of Ext JS (" + versionRegex() + ").*" or
    result = "(?s).*Ext Core Library (" + versionRegex() + ").*"
  }

  string getAnAlias() { result = "ext" }
}


/**
 * YUI
 */
class YUI extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  YUI() { this = "yui" }
  string getAMarkerCommentRegex() {
    result = "(?s).*YUI (" + versionRegex() + ") \\(build \\d+\\).*"
  }
}


/**
 * Knockout
 */
class Knockout extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Knockout() { this = "knockout" }
  string getAMarkerCommentRegex() {
    result = "(?s).*Knockout JavaScript library v(" + versionRegex() + ").*"
  }
}


/**
 * AngularJS
 */
class AngularJS extends FrameworkLibraryWithGenericURL {
  AngularJS() { this = "angularjs" }
  string getAnAlias() { result = "angular" or result = "angular2" }
}

/**
 * Helper predicate for identifying AngularJS's marker comment.
 *
 * Note that many versions of AngularJS do not include a marker comment.
 */
private predicate angularMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  (
   version = c.getText().regexpCapture("(?s).*AngularJS v(" + versionRegex() + ").*", 1)
   or
   c.getText().regexpMatch("(?s).*Copyright \\(c\\) 20.. Adam Abrons.*") and version = "*"
  )
}

/**
 * A copy of AngularJS.
 */
class AngularJSInstance extends FrameworkLibraryInstance {
  AngularJSInstance() { angularMarkerComment(_, this, _) }
  AngularJS getFramework() { any() }
  string getVersion() { angularMarkerComment(_, this, result) }
}


/**
 * Angular UI bootstrap
 */
class AngularUIBootstrap extends FrameworkLibraryWithGenericURL {
  AngularUIBootstrap() { this = "angular-ui-bootstrap" }
  string getAnAlias() { result = "ui-bootstrap" }
}
 

/**
 * Helper predicate for identifying Angular UI boostrap's marker comment.
 */
private predicate angularUIBootstrapMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  c.getText().regexpMatch("(?s).*angular-ui-bootstrap.*") and
  version = c.getText().regexpCapture("(?s).*Version: (" + versionRegex() + ").*", 1)
}

/**
 * A copy of Angular UI bootstrap.
 */
class AngularUIBootstrapInstance extends FrameworkLibraryInstance {
  AngularUIBootstrapInstance() { angularUIBootstrapMarkerComment(_, this, _) }
  AngularUIBootstrap getFramework() { any() }
  string getVersion() { angularUIBootstrapMarkerComment(_, this, result) }
}


/**
 * React
 */
class React extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  React() { this = "react" }
  string getAMarkerCommentRegex() {
    result = "(?s).*React(?:DOM(?:Server)?| \\(with addons\\))? v(" + versionRegex() + ").*"
  }
}


/**
 * Microsoft AJAX Framework
 */
class MicrosoftAJAXFramework extends FrameworkLibrary {
  MicrosoftAJAXFramework() { this = "microsoft-ajax-framework" }
}

/**
 * Helper predicate for identifying Microsoft AJAX Framework's marker comment.
 */
private predicate microsoftAJAXFrameworkMarkerComments(Comment c1, Comment c2,
                                                       TopLevel tl, string version) {
  tl = c1.getTopLevel() and
  tl = c2.getTopLevel() and
  c1.getText().regexpMatch("(?s).*Microsoft AJAX Framework.*") and
  version = c2.getText().regexpCapture("(?s).* Version:\\s*(" + versionRegex() + ").*", 1)
}

/**
 * A copy of Microsoft AJAX Framework.
 */
class MicrosoftAJAXFrameworkInstance extends FrameworkLibraryInstance {
  MicrosoftAJAXFrameworkInstance() { microsoftAJAXFrameworkMarkerComments(_, _, this, _) }
  MicrosoftAJAXFramework getFramework() { any() }
  string getVersion() { microsoftAJAXFrameworkMarkerComments(_, _, this, result) }
}
