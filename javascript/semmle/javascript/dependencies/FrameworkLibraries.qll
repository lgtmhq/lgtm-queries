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
 * Provides classes for identifying popular framework libraries.
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
  bindingset[this]
  FrameworkLibrary() { this=this }

  /**
   * Gets the unique identifier of this framework library.
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
   * Gets the framework of which this is an instance.
   */
  abstract FrameworkLibrary getFramework();

  /**
   * Gets the version of the framework of which this is an instance.
   */
  abstract string getVersion();
}

/**
 * An abstract representation of a reference to a framework library
 * via the `src` attribute of a `<script>` element.
 */
abstract class FrameworkLibraryReference extends HTMLAttribute {
  FrameworkLibraryReference() {
    getName() = "src" and getElement() instanceof HTMLScriptTag
  }

  /**
   * Gets the framework to which this is a reference.
   */
  abstract FrameworkLibrary getFramework();

  /**
   * Gets the version of the framework to which this is a reference.
   */
  abstract string getVersion();
}

/**
 * A framework library whose instances can be identified by marker comments.
 */
abstract class FrameworkLibraryWithMarkerComment extends FrameworkLibrary {
  bindingset[this]
  FrameworkLibraryWithMarkerComment() { this=this }

  /**
   * Gets a regular expression that can be used to identify an instance of
   * this framework library.
   *
   * The first capture group of this regular expression should match
   * the version number. Any occurrences of the string `<VERSION>` in
   * the regular expression are replaced by `versionRegex()` before
   * matching.
   */
  abstract string getAMarkerCommentRegex();
}

/**
 * A framework library that is referenced by URLs that have a certain
 * pattern.
 */
abstract class FrameworkLibraryWithURLRegex extends FrameworkLibrary {
  bindingset[this]
  FrameworkLibraryWithURLRegex() { this=this }

  /**
   * Gets a regular expression that can be used to identify a URL referring
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
  bindingset[this]
  FrameworkLibraryWithGenericURL() { this=this }

  /** Gets an alternative name of this library. */
  string getAnAlias() { none() }

  override string getAURLRegex() {
    exists (string id | id = getId() or id = getAnAlias() |
      result = ".*(?:^|/)" + id + "-(" + semverRegex() + ")" + variantRegex() + "\\.js" or
      result = ".*/(?:\\w+@)?(" + semverRegex() +
               ")/(?:(?:dist|js|" + id + ")/)?" + id + variantRegex() + "\\.js"
    )
  }
}

/**
 * Gets a regular expression identifying suffixes that are commonly appended
 * to the name of a library to distinguish minor variants.
 *
 * We ignore these when identifying frameworks.
 */
private string variantRegex() {
  result = "([.-](slim|min|debug|dbg|umd|dev|all|testing|polyfills|" +
                 "core|compat|more|modern|sandbox|rtl|with-addons|legacy))*"
}

/**
 * Gets a regular expression identifying version numbers in URLs.
 *
 * We currently recognize version numbers of the form
 * `<major>.<minor>.<patch>-beta.<n>`, where `.<patch>` and/or
 * `-beta.<n>` may be missing.
 */
private string semverRegex() {
  result = "\\d+\\.\\d+(?:\\.\\d+)?(?:-beta\\.\\d+)?"
}


/**
 * An instance of a `FrameworkLibraryWithMarkerComment`.
 */
class FrameworkLibraryInstanceWithMarkerComment extends FrameworkLibraryInstance {
  FrameworkLibraryInstanceWithMarkerComment() { matchMarkerComment(_, this, _, _) }
  override FrameworkLibrary getFramework() { matchMarkerComment(_, this, result, _) }
  override string getVersion() { matchMarkerComment(_, this, _, result) }
}

/**
 * Holds if comment `c` in toplevel `tl` matches the marker comment of library
 * `fl` at `version`.
 */
private predicate matchMarkerComment(Comment c, TopLevel tl,
                                     FrameworkLibraryWithMarkerComment fl, string version) {
  c.getTopLevel() = tl and
  exists (string r |
    r = fl.getAMarkerCommentRegex().replaceAll("<VERSION>", versionRegex()) |
    version = c.getText().regexpCapture(r, 1)
  )
}


/**
 * A reference to a `FrameworkLibraryWithURL`.
 */
class FrameworkLibraryReferenceWithURL extends FrameworkLibraryReference {
  FrameworkLibraryReferenceWithURL() { matchURL(this, _, _) }
  override FrameworkLibrary getFramework() { matchURL(this, result, _) }
  override string getVersion() { matchURL(this, _, result) }
}

/**
 * Holds if the value of `src` attribute `attr` matches the URL pattern of library
 * `fl` at `version`.
 */
private predicate matchURL(HTMLAttribute attr, FrameworkLibraryWithURLRegex fl, string version) {
  version = attr.getValue().regexpCapture(fl.getAURLRegex(), 1)
}


/**
 * Gets a regular expression for matching versions specified in marker comments.
 */
private string versionRegex() {
  result = "\\d+\\.\\d+[A-Za-z0-9.+_-]*"
}


/**
 * The jQuery framework.
 */
private class JQuery extends FrameworkLibraryWithGenericURL {
  JQuery() { this = "jquery" }
}

/**
 * Holds if comment `c` in toplevel `tl` is a marker comment for the given `version`
 * of jQuery.
 */
private predicate jQueryMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  exists (string txt | txt = c.getText() |
    // more recent versions use this format
    version = txt.regexpCapture("(?s).*jQuery (?:JavaScript Library )?v(" +
                                versionRegex() + ").*", 1)
    or
    // earlier versions used this format
    version = txt.regexpCapture("(?s).*jQuery (" + versionRegex() + ") - New Wave Javascript.*", 1)
    or
    // 1.0.0 and 1.0.1 have the same marker comment; we call them both "1.0"
    txt.matches("%jQuery - New Wave Javascript%") and version = "1.0"
  )
}

/**
 * A copy of jQuery.
 */
private class JQueryInstance extends FrameworkLibraryInstance {
  JQueryInstance() { jQueryMarkerComment(_, this, _) }
  override JQuery getFramework() { any() }
  override string getVersion() { jQueryMarkerComment(_, this, result) }
}


/**
 * The jQuery Mobile framework.
 */
private class JQueryMobile extends FrameworkLibraryWithGenericURL,
                                   FrameworkLibraryWithMarkerComment {
  JQueryMobile() { this = "jquery-mobile" }
  override string getAnAlias() { result = "jquery.mobile" }
  override string getAMarkerCommentRegex() { result = "(?s).*jQuery Mobile (<VERSION>).*" }
}


/**
 * The jQuery UI framework.
 */
private class JQueryUI extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  JQueryUI() { this = "jquery-ui" }
  override string getAMarkerCommentRegex() { result = "(?s).*jQuery UI - v?(<VERSION>).*" }
}

/**
 * The jQuery TextExt framework.
 */
private class JQueryTextExt extends FrameworkLibraryWithGenericURL,
                                    FrameworkLibraryWithMarkerComment {
  JQueryTextExt() { this = "jquery-textext" }
  override string getAnAlias() { result = "jquery.textext" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*jQuery TextExt Plugin.*@version (<VERSION>).*"
  }
}

/**
 * The Bootstrap framework.
 */
private class Bootstrap extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Bootstrap() { this = "bootstrap" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*Bootstrap v(<VERSION>) \\(http://getbootstrap.com\\).*"
  }
}

/**
 * The Modernizr framework.
 */
private class Modernizr extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Modernizr() { this = "modernizr" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*(?<!@license )Modernizr (?:JavaScript library )?v?(<VERSION>).*"
  }
}

/**
 * The MooTools framework.
 */
private class MooTools extends FrameworkLibraryWithGenericURL {
  MooTools() { this = "mootools" }
}

/**
 * Holds if expression `oe` in toplevel `tl` is a meta-information object for
 * MooTools at the given `version`.
 *
 * MooTools puts an object into `this.MooTools` that contains version information;
 * this helper predicate identifies the definition of that object, which is always
 * of the form
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
private class MooToolsInstance extends FrameworkLibraryInstance {
  MooToolsInstance() { mooToolsObject(_, this, _) }
  override MooTools getFramework() { any() }
  override string getVersion() { mooToolsObject(_, this, result) }
}


/**
 * The Prototype framework.
 */
private class Prototype extends FrameworkLibraryWithGenericURL {
  Prototype() { this = "prototype" }
}

/**
 * Holds if expression `oe` in toplevel `tl` is a meta-information object for
 * Prototype at the given `version`.
 *
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
private class PrototypeInstance extends FrameworkLibraryInstance {
  PrototypeInstance() { prototypeObject(_, this, _) }
  override Prototype getFramework() { any() }
  override string getVersion() { prototypeObject(_, this, result) }
}


/**
 * The Scriptaculous framework.
 */
private class Scriptaculous extends FrameworkLibraryWithGenericURL {
  Scriptaculous() { this = "scriptaculous" }
}

/**
 * Holds if expression `oe` in toplevel `tl` is a meta-information object for
 * Scriptaculous at the given `version`.
 *
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
private class ScriptaculousInstance extends FrameworkLibraryInstance {
  ScriptaculousInstance() { scriptaculousObject(_, this, _) }
  override Scriptaculous getFramework() { any() }
  override string getVersion() { scriptaculousObject(_, this, result) }
}


/**
 * The Underscore framework.
 */
private class Underscore extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Underscore() { this = "underscore" }
  override string getAMarkerCommentRegex() { result = "^\\s*Underscore.js (<VERSION>).*" }
}


/**
 * The Lodash framework.
 */
private class Lodash extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Lodash() { this = "lodash" }

  override string getAMarkerCommentRegex() {
    result = "(?s).* (?:lod|Lo-D)ash (<VERSION>)" +
             "(?: \\(Custom Build\\))? " +
             "<https?://lodash.com/>.*"
  }
}


/** The Dojo framework. */
private class Dojo extends FrameworkLibraryWithGenericURL {
  Dojo() { this = "dojo" }
}

/**
 * Holds if comment `c` in toplevel `tl` is a marker comment for the given
 * `version` of Dojo.
 */
private predicate dojoMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  c.getText().regexpMatch("(?s).*Copyright \\(c\\) 2004-20.., The Dojo Foundation.*") and
  // Dojo doesn't embed a version string
  version = "unknown"
}

/**
 * A copy of Dojo.
 */
private class DojoInstance extends FrameworkLibraryInstance {
  DojoInstance() { dojoMarkerComment(_, this, _) }
  override Dojo getFramework() { any() }
  override string getVersion() { dojoMarkerComment(_, this, result) }
}


/**
 * The ExtJS framework.
 */
private class ExtJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  ExtJS() { this = "extjs" }

  override string getAMarkerCommentRegex() {
    result = "(?s).*This file is part of Ext JS (<VERSION>).*" or
    result = "(?s).*Ext Core Library (<VERSION>).*"
  }

  override string getAnAlias() { result = "ext" }
}


/**
 * The YUI framework.
 */
private class YUI extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  YUI() { this = "yui" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*YUI (<VERSION>) \\(build \\d+\\).*"
  }
}


/**
 * The Knockout framework.
 */
private class Knockout extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  Knockout() { this = "knockout" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*Knockout JavaScript library v(<VERSION>).*"
  }
}


/**
 * The AngularJS framework.
 */
private class AngularJS extends FrameworkLibraryWithGenericURL {
  AngularJS() { this = "angularjs" }
  override string getAnAlias() { result = "angular" or result = "angular2" }
}

/**
 * Holds if comment `c` in toplevel `tl` is a marker comment for the given
 * `version` of AngularJS.
 *
 * Note that many versions of AngularJS do not include a marker comment.
 */
private predicate angularMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  (
   version = c.getText().regexpCapture("(?s).*AngularJS v(" + versionRegex() + ").*", 1)
   or
   c.getText().regexpMatch("(?s).*Copyright \\(c\\) 20.. Adam Abrons.*") and version = "unknown"
  )
}

/**
 * A copy of AngularJS.
 */
private class AngularJSInstance extends FrameworkLibraryInstance {
  AngularJSInstance() { angularMarkerComment(_, this, _) }
  override AngularJS getFramework() { any() }
  override string getVersion() { angularMarkerComment(_, this, result) }
}


/**
 * The Angular UI bootstrap framework.
 */
private class AngularUIBootstrap extends FrameworkLibraryWithGenericURL {
  AngularUIBootstrap() { this = "angular-ui-bootstrap" }
  override string getAnAlias() { result = "ui-bootstrap" }
}


/**
 * Holds if comment `c` in toplevel `tl` is a marker comment for the given
 * `version` of AngularUI bootstrap.
 */
private predicate angularUIBootstrapMarkerComment(Comment c, TopLevel tl, string version) {
  tl = c.getTopLevel() and
  c.getText().regexpMatch("(?s).*angular-ui-bootstrap.*") and
  version = c.getText().regexpCapture("(?s).*Version: (" + versionRegex() + ").*", 1)
}

/**
 * A copy of Angular UI bootstrap.
 */
private class AngularUIBootstrapInstance extends FrameworkLibraryInstance {
  AngularUIBootstrapInstance() { angularUIBootstrapMarkerComment(_, this, _) }
  override AngularUIBootstrap getFramework() { any() }
  override string getVersion() { angularUIBootstrapMarkerComment(_, this, result) }
}


/**
 * The React framework.
 */
private class React extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  React() { this = "react" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*React(?:DOM(?:Server)?| \\(with addons\\))? v(<VERSION>).*"
  }
}


/**
 * The Microsoft AJAX Framework.
 */
private class MicrosoftAJAXFramework extends FrameworkLibrary {
  MicrosoftAJAXFramework() { this = "microsoft-ajax-framework" }
}

/**
 * Holds if comments `c1` and `c2` in toplevel `tl` are marker comments for the given
 * `version` of the Microsoft AJAX Framework.
 */
private predicate microsoftAJAXFrameworkMarkerComments(Comment c1, Comment c2,
                                                       TopLevel tl, string version) {
  tl = c1.getTopLevel() and
  tl = c2.getTopLevel() and
  c1.getText().regexpMatch("(?s).*Microsoft AJAX Framework.*") and
  version = c2.getText().regexpCapture("(?s).* Version:\\s*(" + versionRegex() + ").*", 1)
}

/**
 * A copy of the Microsoft AJAX Framework.
 */
private class MicrosoftAJAXFrameworkInstance extends FrameworkLibraryInstance {
  MicrosoftAJAXFrameworkInstance() { microsoftAJAXFrameworkMarkerComments(_, _, this, _) }
  override MicrosoftAJAXFramework getFramework() { any() }
  override string getVersion() { microsoftAJAXFrameworkMarkerComments(_, _, this, result) }
}

/**
 * The Polymer framework.
 */
private class Polymer extends FrameworkLibraryWithGenericURL {
  Polymer() { this = "polymer" }
}

/**
 * Holds if toplevel `tl` looks like a copy of the given `version` of Polymer.
 */
private predicate isPolymer(TopLevel tl, string version) {
  // tl contains both a license comment...
  exists (Comment c | c.getTopLevel() = tl |
    c.getText().matches("%Copyright (c) 20__ The Polymer Project Authors. All rights reserved.%")
  ) and
  // ...and a version comment
  exists (Comment c | c.getTopLevel() = tl |
    version = c.getText().regexpCapture("(?s).*@version:? (" + versionRegex() + ").*", 1)
  )
}

/**
 * A copy of Polymer.
 */
private class PolymerInstance extends FrameworkLibraryInstance {
  PolymerInstance() { isPolymer(this, _) }
  override Polymer getFramework() { any() }
  override string getVersion() { isPolymer(this, result) }
}

/**
 * The Vue.js framework.
 */
private class VueJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  VueJS() { this = "vue" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*Vue\\.js v(<VERSION>).*"
  }
}

/**
 * The Swagger UI framework.
 */
private class SwaggerUI extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  SwaggerUI() { this = "swagger-ui" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*swagger-ui - Swagger UI.*@version v(<VERSION>).*"
  }
}

/**
 * The Backbone.js framework.
 */
private class BackboneJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  BackboneJS() { this = "backbone" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*Backbone\\.js (<VERSION>).*"
  }
}

/**
 * The Ember.js framework.
 */
private class EmberJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  EmberJS() { this = "ember" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*Ember - JavaScript Application Framework.*@version\\s*(<VERSION>).*"
  }
}

/**
 * The QUnit.js framework.
 */
private class QUnitJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  QUnitJS() { this = "qunit" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*QUnit\\s*(<VERSION>).*"
  }
}

/**
 * The Mocha framework.
 */
private class Mocha extends FrameworkLibraryWithGenericURL {
  Mocha() { this = "mocha" }
}

/**
 * The Jasmine framework.
 */
private class Jasmine extends FrameworkLibraryWithGenericURL {
  Jasmine() { this = "jasmine" }
}

/**
 * The Chai framework.
 */
private class Chai extends FrameworkLibraryWithGenericURL {
  Chai() { this = "chai" }
}

/**
 * The Sinon.JS framework.
 */
private class SinonJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  SinonJS() { this = "sinon" }
  override string getAnAlias() { result = "sinon-ie" or result = "sinon-timers" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*Sinon\\.JS\\s*(<VERSION>).*"
  }
}

/**
 * The TinyMCE framework.
 */
private class TinyMCE extends FrameworkLibraryWithGenericURL {
  TinyMCE() { this = "tinymce" }
  override string getAnAlias() { result = "jquery.tinymce" or result = "tinymce.jquery" }
}

/**
 * The Require.js framework.
 */
private class RequireJS extends FrameworkLibraryWithGenericURL, FrameworkLibraryWithMarkerComment {
  RequireJS() { this = "requirejs" }
  override string getAnAlias() { result = "require.js" }
  override string getAMarkerCommentRegex() {
    result = "(?s).*RequireJS\\s*(<VERSION>).*"
  }
}

/**
 * A `FrameworkLibraryReference` that refers to a recognised `FrameworkLibraryInstance`,
 * that is, a `<script>` tag where the `src` attribute can be resolved to a local file
 * that is recognised as an instance of a framework library.
 */
private class FrameworkLibraryReferenceToInstance extends FrameworkLibraryReference {
  FrameworkLibraryReferenceToInstance() {
    getElement().(HTMLScriptTag).resolveSource() instanceof FrameworkLibraryInstance
  }

  /** Gets the framework library instance this reference refers to. */
  private FrameworkLibraryInstance getInstance() {
    result = getElement().(HTMLScriptTag).resolveSource()
  }

  override FrameworkLibrary getFramework() {
    result = getInstance().getFramework()
  }

  override string getVersion() {
    result = getInstance().getVersion()
  }
}
