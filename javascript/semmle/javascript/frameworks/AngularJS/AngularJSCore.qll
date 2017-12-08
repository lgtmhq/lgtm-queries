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
 * Provides the core classes for working with AngularJS applications.
 *
 * As the module grows, large features might move to separate files.
 *
 * INTERNAL: Do not import this module directly, import `AngularJS` instead.
 *
 * NOTE: The API of this library is not stable yet and may change in
 *       the future.
 *
 */

import javascript
private import AngularJS

/**
 * Gets a string value that may flow into `nd`.
 */
private string getStringValue(DataFlowNode nd) {
  result = nd.getALocalSource().(Expr).getStringValue()
}

/**
 * Holds if `nd` is a reference to the `angular` variable.
 */
predicate isAngularRef(DataFlowNode nd) {
  exists (Expr src | src = nd.getALocalSource() |
    // either as a global
    src.accessesGlobal("angular") or
    // or imported from a module named `angular`
    src.(ModuleInstance).getPath() = "angular"
  )
}

/**
 * Holds if `m` is of the form `angular.module("name", ...)`.
 */
private predicate isAngularModuleCall(MethodCallExpr m, string name) {
  isAngularRef(m.getReceiver()) and
  m.getMethodName() = "module" and
  name = getStringValue(m.getArgument(0))
}

/**
 * An AngularJS module for which there is a definition or at least a lookup.
 */
private newtype TAngularModule = MkAngularModule(string name) {
  isAngularModuleCall(_, name)
}

/**
 * An AngularJS module.
 */
class AngularModule extends TAngularModule {
  string name;

  AngularModule() {
    this = MkAngularModule(name)
  }

  /**
   * Get a definition for this module, that is, a call of the form
   * `angular.module("name", deps)`.
   */
  MethodCallExpr getADefinition() {
    isAngularModuleCall(result, name) and
    result.getNumArgument() > 1
  }

  /**
   * Gets a lookup of this module, that is, a call of the form
   * `angular.module("name")`.
   */
  MethodCallExpr getALookup() {
    isAngularModuleCall(result, name) and
    result.getNumArgument() = 1
  }

  /**
   * Get the array of dependencies from this module's definition.
   */
  ArrayExpr getDependencyArray() {
    getADefinition().getArgument(1).(DataFlowNode).getALocalSource() = result
  }

  /**
   * Gets another module that this module lists as a dependency.
   */
  AngularModule getADependency() {
    result.getName() = getStringValue(getDependencyArray().getAnElement())
  }

  /**
   * Gets the name of this module.
   */
  string getName() { result = name }

  /**
   * Gets a textual representation of this module.
   */
  string toString() { result = name }
}

/**
 * Holds if `nd` is a reference to module `m`, that is, it is either
 * a definition of `m`, a lookup of `m`, or a chained method call on
 * `m`.
 */
predicate isModuleRef(DataFlowNode nd, AngularModule m) {
  exists (MethodCallExpr src | src = nd.getALocalSource() |
    src = m.getADefinition()
    or
    src = m.getALookup()
    or
    isModuleRef(src.getReceiver(), m) and
    // the one-argument variant of `info` is not chaining
    not (src.getMethodName() = "info" and src.getNumArgument() = 1)
  )
}

/**
 * A call to a method from the `angular.Module` API.
 */
class ModuleApiCall extends @callexpr {
  /** The module on which the method is called. */
  AngularModule mod;

  /** The name of the called method. */
  string methodName;

  ModuleApiCall() {
    exists (MethodCallExpr m | m = this |
      isModuleRef(m.getReceiver(), mod) and
      m.getMethodName() = methodName
    )
  }

  /**
   * Gets the `i`th argument of this method call.
   */
  Expr getArgument(int i) {
    result = this.(MethodCallExpr).getArgument(i)
  }

  /**
   * Gets a textual representation of this method call.
   */
  string toString() { result = this.(CallExpr).toString() }
}

/**
 * An AngularJS directive definition, that is, a method call of the form
 * `module.directive("name", factoryFunction)`.
 */
class DirectiveDefinition extends ModuleApiCall {
  /** The name of this directive. */
  string name;

  /** The factory function of this directive. */
  InjectableFunction factoryFunction;

  DirectiveDefinition() {
    methodName = "directive" and
    name = getStringValue(getArgument(0)) and
    factoryFunction = getArgument(1).(DataFlowNode).getALocalSource()
  }

  /** Gets the name of this directive. */
  string getName() { result = name }

  /** Gets the factory function of this directive. */
  InjectableFunction getFactoryFunction() {
    result = factoryFunction
  }

  /** Gets a textual representation of this directive. */
  string toString() { result = name }
}

/**
 * An AngularJS component definition, that is, a method call of the form
 * `module.component("name", config)`.
 */
class ComponentDefinition extends ModuleApiCall {
  /** The name of the defined component. */
  string name;

  /** The configuration object for the component. */
  ObjectExpr config;

  ComponentDefinition() {
    methodName = "component" and
    name = getStringValue(getArgument(0)) and
    config = getArgument(1).(DataFlowNode).getALocalSource()
  }

  /** Gets the name of the defined component. */
  string getName() { result = name }

  /** Gets the configuration object for the defined component. */
  ObjectExpr getConfig() {
    result = config
  }

  /** Gets a textual representation of this component definition. */
  string toString() { result = name }
}

/**
 * Holds if `name` is the name of a built-in AngularJS directive
 * (cf. https://docs.angularjs.org/api/ng/directive/).
 */
private predicate builtinDirective(string name) {
  name = "ngApp" or
  name = "ngBind" or
  name = "ngBindHtml" or
  name = "ngBindTemplate" or
  name = "ngBlur" or
  name = "ngChange" or
  name = "ngChecked" or
  name = "ngClass" or
  name = "ngClassEven" or
  name = "ngClassOdd" or
  name = "ngClick" or
  name = "ngCloak" or
  name = "ngController" or
  name = "ngCopy" or
  name = "ngCsp" or
  name = "ngCut" or
  name = "ngDblclick" or
  name = "ngDisabled" or
  name = "ngFocus" or
  name = "ngForm" or
  name = "ngHide" or
  name = "ngHref" or
  name = "ngIf" or
  name = "ngInclude" or
  name = "ngInit" or
  name = "ngJq" or
  name = "ngKeydown" or
  name = "ngKeypress" or
  name = "ngKeyup" or
  name = "ngList" or
  name = "ngMaxlength" or
  name = "ngMinlength" or
  name = "ngModel" or
  name = "ngModelOptions" or
  name = "ngMousedown" or
  name = "ngMouseenter" or
  name = "ngMouseleave" or
  name = "ngMousemove" or
  name = "ngMouseover" or
  name = "ngMouseup" or
  name = "ngNonBindable" or
  name = "ngOpen" or
  name = "ngOptions" or
  name = "ngPaste" or
  name = "ngPattern" or
  name = "ngPluralize" or
  name = "ngReadonly" or
  name = "ngRepeat" or
  name = "ngRequired" or
  name = "ngSelected" or
  name = "ngShow" or
  name = "ngSrc" or
  name = "ngSrcset" or
  name = "ngStyle" or
  name = "ngSubmit" or
  name = "ngSwitch" or
  name = "ngTransclude" or
  name = "ngValue"
}

private newtype TDirectiveInstance =
MkBuiltinDirective(string name) { builtinDirective(name) }
or
MkCustomDirective(DirectiveDefinition def)
or
MkCustomComponent(ComponentDefinition def)

/**
 * An AngularJS directive, either built-in or custom.
 */
class DirectiveInstance extends TDirectiveInstance {
  /**
   * Gets the name of this directive.
   */
  abstract string getName();

  /**
   * Gets a directive target matching this directive.
   */
  DirectiveTarget getATarget() {
    this.getName() = result.getName().(DirectiveTargetName).normalize()
  }

  /**
   * Gets a DOM element matching this directive.
   */
  DOM::ElementDefinition getAMatchingElement() {
    result = getATarget().getElement()
  }

  /** Gets a textual representation of this directive. */
  string toString() { result = getName() }
}

/**
 * A built-in AngularJS directive.
 */
class BuiltinDirective extends DirectiveInstance, MkBuiltinDirective {
  string name;

  BuiltinDirective() {
    this = MkBuiltinDirective(name)
  }

  override string getName() { result = name }
}

/**
 * A custom AngularJS directive, either a general directive defined by `angular.directive`
 * or a component defined by `angular.component`.
 */
abstract class CustomDirective extends DirectiveInstance {
  /** Gets the element defining this directive. */
  abstract DataFlowNode getDefinition();

  /** Gets the member `name` of this directive. */
  abstract DataFlowNode getMember(string name);

  /** Gets the method `name` of this directive. */
  Function getMethod(string name) {
    result = getMember(name)
  }

  /** Gets a link function of this directive. */
  abstract Function getALinkFunction();

  /** Holds if this directive's properties are bound to the controller. */
  abstract predicate bindsToController();

  /** Holds if this directive introduces an isolate scope. */
  abstract predicate hasIsolateScope();

  /** Gets the controller function of this directive, if any. */
  InjectableFunction getController() {
    result = getMember("controller")
  }

  /** Gets the template URL of this directive, if any. */
  string getTemplateUrl() {
    result = getStringValue(getMember("templateUrl"))
  }
}

/**
 * A custom AngularJS directive defined by `angular.directive`.
 */
class GeneralDirective extends CustomDirective, MkCustomDirective {
  /** The definition of this directive. */
  DirectiveDefinition definition;

  GeneralDirective() {
    this = MkCustomDirective(definition)
  }

  override string getName() {
    result = definition.getName()
  }

  override DataFlowNode getDefinition() {
    result = definition
  }

  /** Gets a node that contributes to the return value of the factory function. */
  private DataFlowNode getAnInstantiation() {
    exists (Function factory |
      factory = definition.getFactoryFunction().asFunction() and
      result = factory.getAReturnedExpr().(DataFlowNode).getALocalSource()
    )
  }

  override DataFlowNode getMember(string name) {
    exists (PropWriteNode pw |
      pw.getBase().getALocalSource() = getAnInstantiation() and
      pw.getPropertyName() = name and
      pw.getRhs().getALocalSource() = result
    )
  }

  /** Gets the compile function of this directive, if any. */
  Function getCompileFunction() {
    result = getMethod("compile")
  }

  /**
   * Gets a pre/post link function of this directive defined on its definition object.
   * If `kind` is `"pre"`, the result is a `preLink` function. If `kind` is `"post"`,
   * the result is a `postLink` function..
   *
   * See https://docs.angularjs.org/api/ng/service/$compile for documentation of
   * the directive definition API. We do not model the precedence of `compile` over
   * `link`.
   */
  private Function getLinkFunction(string kind) {
    // { link: function postLink() { ... } }
    kind = "post" and
    result = getMember("link")
    or
    // { link: { pre: function preLink() { ... }, post: function postLink() { ... } } }
    exists (PropWriteNode pwn |
      pwn.getBase() = getMember("link") and
      (kind = "pre" or kind = "post") and
      pwn.getPropertyName() = kind and
      result = pwn.getRhs().getALocalSource()
    )
    or
    // { compile: function() { ... return link; } }
    exists (DataFlowNode compileReturn, DataFlowNode compileReturnSrc |
      compileReturn = getCompileFunction().getAReturnedExpr() and
      compileReturnSrc = compileReturn.getALocalSource() |
      // link = function postLink() { ... }
      kind = "post" and
      result = compileReturnSrc
      or
      // link = { pre: function preLink() { ... }, post: function postLink() { ... } }
      exists (PropWriteNode pwn |
        pwn.getBase().getALocalSource() = compileReturnSrc and
        (kind = "pre" or kind = "post") and
        pwn.getPropertyName() = kind and
        result = pwn.getRhs().getALocalSource()
      )
    )
  }

  /** Gets the pre-link function of this directive. */
  Function getPreLinkFunction() {
    result = getLinkFunction("pre")
  }

  /** Gets the post-link function of this directive. */
  Function getPostLinkFunction() {
    result = getLinkFunction("post")
  }

  override Function getALinkFunction() {
    result = getLinkFunction(_)
  }

  override predicate bindsToController() {
    getMember("bindToController").(BooleanLiteral).getValue() = "true"
  }

  predicate hasIsolateScope() {
    getMember("scope") instanceof ObjectExpr
  }
}

/**
 * An AngularJS component defined by `angular.component`.
 */
class ComponentDirective extends CustomDirective, MkCustomComponent {
  /** The definition of this component. */
  ComponentDefinition comp;

  ComponentDirective() {
    this = MkCustomComponent(comp)
  }

  override string getName() {
    result = comp.getName()
  }

  override DataFlowNode getDefinition() {
    result = comp
  }

  override DataFlowNode getMember(string name) {
    exists (PropWriteNode pwn |
      pwn.getBase().getALocalSource() = comp.getConfig() and
      pwn.getPropertyName() = name and
      result = pwn.getRhs().getALocalSource()
    )
  }

  override Function getALinkFunction() {
    none()
  }

  override predicate bindsToController() {
    none()
  }

  override predicate hasIsolateScope() {
    any()
  }
}

/**
 * An AngularJS service definition, that is, a method call of the form
 * `module.factory("name", factoryFunction)`.
 */
class ServiceDefinition extends ModuleApiCall {
  /** The name of the defined service. */
  string name;

  /** The factory function for the service. */
  InjectableFunction factoryFunction;

  ServiceDefinition() {
    methodName = "factory" and
    name = getStringValue(getArgument(0)) and
    factoryFunction = getArgument(1).(DataFlowNode).getALocalSource()
  }

  /** Gets the name of the defined service. */
  string getName() { result = name }

  /** Gets the factory function creating the service instance. */
  InjectableFunction getFactoryFunction() {
    result = factoryFunction
  }

  /** Gets a textual representation of this service definition. */
  string toString() { result = name }
}

/**
 * An AngularJS filter definition, that is, a method call of the form
 * `module.filter("name", factoryFunction)`.
 */
class FilterDefinition extends ModuleApiCall {
  /** The name of the defined filter. */
  string name;

  /** The factory function for the filter. */
  InjectableFunction factoryFunction;

  FilterDefinition() {
    methodName = "filter" and
    name = getStringValue(getArgument(0)) and
    factoryFunction = getArgument(1).(DataFlowNode).getALocalSource()
  }

  /** Gets the name of the defined filter. */
  string getName() { result = name }

  /** Gets the factory function creating the filter instance. */
  InjectableFunction getFactoryFunction() {
    result = factoryFunction
  }

  /** Gets a textual representation of this filter definition. */
  string toString() { result = name }
}

/**
 * An AngularJS controller definition, that is, a method call of the form
 * `module.controller("name", factoryFunction)`.
 */
class ControllerDefinition extends ModuleApiCall {
  /** The name of the defined controller. */
  string name;

  /** The factory function for the controller. */
  InjectableFunction factoryFunction;

  ControllerDefinition() {
    methodName = "controller" and
    name = getStringValue(getArgument(0)) and
    factoryFunction = getArgument(1).(DataFlowNode).getALocalSource()
  }

  /** Gets the name of the defined controller. */
  string getName() { result = name }

  /** Gets the factory function for creating controller instances. */
  InjectableFunction getFactoryFunction() {
    result = factoryFunction
  }

  /** Gets a textual representation of this controller definition. */
  string toString() { result = name }
}

private newtype TDirectiveTargetType = E() or A() or C() or M()

/**
 * The type of a directive target, indicating whether it is an element ("E"),
 * an attribute ("A"), a class name ("C") or a comment ("M").
 */
class DirectiveTargetType extends TDirectiveTargetType {
  /**
   * Gets a textual representation of this target type.
   */
  string toString() {
    this = E() and result = "E" or
    this = A() and result = "A" or
    this = C() and result = "C" or
    this = M() and result = "M"
  }
}

/**
 * A syntactic element to which an AngularJS directive can be attached.
 */
abstract class DirectiveTarget extends Locatable {
  /**
   * Gets the name of this directive target, which is used to match it up
   * with any AngularJS directives that apply to it.
   *
   * This name is not normalized.
   */
  abstract string getName();

  /**
   * Gets the element which AngularJS directives attached to this target
   * match.
   */
  abstract DOM::ElementDefinition getElement();

  /**
   * Gets the type of this directive target.
   */
  abstract DirectiveTargetType getType();
}

/**
 * A DOM element, viewed as directive target.
 */
private class DomElementAsElement extends DirectiveTarget {
  DOM::ElementDefinition element;
  DomElementAsElement() { this = element }
  override string getName() { result = element.getName() }
  override DOM::ElementDefinition getElement() { result = element }
  override DirectiveTargetType getType() { result = E() }
}

/**
 * A DOM attribute, viewed as a directive target.
 */
private class DomAttributeAsElement extends DirectiveTarget {
  DOM::AttributeDefinition attr;
  DomAttributeAsElement() { this = attr }
  override string getName() { result = attr.getName() }
  override DOM::ElementDefinition getElement() { result = attr.getElement() }
  override DirectiveTargetType getType() { result = A() }
}

/**
 * The name of a directive target.
 *
 * This class implements directive name normalization as described in
 * https://docs.angularjs.org/guide/directive: leading `x-` or `data-`
 * is stripped, then the `:`, `-` or `_`-delimited name is converted to
 * camel case.
 */
private class DirectiveTargetName extends string {
  DirectiveTargetName() {
    this = any(DirectiveTarget e).getName()
  }

  /**
   * Gets the `i`th component of this name, where `-`,
   * `:` and `_` count as component delimiters.
   */
  string getRawComponent(int i) {
    result = toLowerCase().regexpFind("(?<=^|[-:_])[a-zA-Z0-9]+(?=$|[-:_])", i, _)
  }

  /**
   * Holds if the first component of this name is `x` or `data`,
   * and hence should be stripped when normalizing.
   */
  predicate stripFirstComponent() {
    getRawComponent(0) = "x" or getRawComponent(0) = "data"
  }

  /**
   * Gets the `i`th component of this name after processing:
   * the first component is stripped if it is `x` or `data`,
   * and all components except the first are capitalized.
   */
  string getProcessedComponent(int i) {
    exists (int j, string raw |
      i >= 0 and
      if stripFirstComponent() then j = i+1 else j = i |
      raw = getRawComponent(j) and
      if i = 0 then result = raw else result = capitalize(raw)
    )
  }

  /**
   * Gets the camelCase version of this name.
   */
  string normalize() {
    result = concat(string c, int i | c = getProcessedComponent(i) | c, "" order by i)
  }
}


/**
 * A call to a getter method of the `$location` service, viewed as a source of
 * user-controlled data.
 *
 * To avoid false positives, we don't consider `$location.url` and similar as
 * remote flow sources, since they are only partly user-controlled.
 *
 * See https://docs.angularjs.org/api/ng/service/$location for details.
 */
private class LocationFlowSource extends RemoteFlowSource {
  LocationFlowSource() {
    exists (ServiceReference service, MethodCallExpr mce, string m, int n |
      service.getName() = "$location" and
      this = mce and
      mce =  service.getAMethodCall(m) and
      n = mce.getNumArgument() |
      m = "search" and n < 2 or
      m = "hash" and n = 0
    )
  }

  override string getSourceType() {
    result = "$location"
  }
}

/**
 * An access to a property of the `$routeParams` service, viewed as a source
 * of user-controlled data.
 *
 * See https://docs.angularjs.org/api/ngRoute/service/$routeParams for more details.
 */
private class RouteParamSource extends RemoteFlowSource {
  RouteParamSource() {
    exists (ServiceReference service |
      service.getName() = "$routeParams" and
      this = service.getAPropertyAccess(_)
    )
  }

  override string getSourceType() {
    result = "$routeParams"
  }
}

/**
 * AngularJS expose a jQuery-like interface through `angular.html(..)`.
 * The interface may be backed by an actual jQuery implementation.
 */
private class JQLiteObject extends JQueryObject {

  JQLiteObject() {
    exists(MethodCallExpr mce |
      this = mce and
      isAngularRef(mce.getReceiver()) and
      mce.getMethodName() = "element"
    ) or
    exists(SimpleParameter param |
      // element parameters to user-functions invoked by AngularJS
      param = any(LinkFunction link).getElementParameter() or
      exists(GeneralDirective d |
        param = d.getCompileFunction().getParameter(0) or
        param = d.getCompileFunction().getAReturnedExpr().(DataFlowNode).getALocalSource().(Function).getParameter(1) or
        param = d.getMember("template").(Function).getParameter(0) or
        param = d.getMember("templateUrl").(Function).getParameter(0)
      ) |
      this = param.getVariable().getAnAccess()
    ) or
    exists(ServiceReference element |
      element.getName() = "$rootElement" or
      element.getName() = "$document" |
      this = element.getAnAccess()
    )
  }
}

/**
 * A call to an AngularJS function.
 *
 * Used for exposing behavior that is similar to the behavior of other libraries.
 */
abstract class AngularJSCall extends CallExpr {

  /**
   * Holds if `e` is an argument that this call interprets as HTML.
   */
  abstract predicate interpretsArgumentAsHtml(Expr e);

  /**
   * Holds if `e` is an argument that this call stores globally, e.g. in a cookie.
   */
  abstract predicate storesArgumentGlobally(Expr e);

  /**
   * Holds if `e` is an argument that this call interprets as code.
   */
  abstract predicate interpretsArgumentAsCode(Expr e);

}

/**
 * A call to a method on the AngularJS object itself.
 */
private class AngularMethodCall extends AngularJSCall {

  MethodCallExpr mce;

  AngularMethodCall() {
    isAngularRef(mce.getReceiver()) and
    mce = this
  }

  override predicate interpretsArgumentAsHtml(Expr e) {
    mce.getMethodName() = "element" and
    e = mce.getArgument(0)
  }

  override predicate storesArgumentGlobally(Expr e) {
    none()
  }

  override predicate interpretsArgumentAsCode(Expr e) {
    none()
  }
}

/**
 * A call to a method on a builtin service.
 */
private class ServiceMethodCall extends AngularJSCall {

  MethodCallExpr mce;

  ServiceMethodCall() {
    exists(BuiltinServiceReference service |
      service.getAMethodCall(_) = this and
      mce = this
    )
  }

  override predicate interpretsArgumentAsHtml(Expr e) {
    exists(ServiceReference service, string methodName |
      service.getName() = "$sce" and
      mce = service.getAMethodCall(methodName) |
      (
        // specialized call
        (methodName = "trustAsHtml" or methodName = "trustAsCss") and
        e = mce.getArgument(0)
      ) or (
        // generic call with enum argument
        methodName = "trustAs" and
        exists(PropReadNode prn |
          prn = mce.getArgument(0) and
          (prn = service.getAPropertyAccess("HTML") or prn = service.getAPropertyAccess("CSS")) and
          e = mce.getArgument(1)
        )
      )
    )
  }

  override predicate storesArgumentGlobally(Expr e) {
    exists(ServiceReference service, string serviceName, string methodName |
      service.getName() = serviceName and
      mce = service.getAMethodCall(methodName) |
      ( // AngularJS caches (only available during runtime, so similar to sessionStorage)
        (serviceName = "$cacheFactory" or serviceName = "$templateCache") and
        methodName = "put" and
        e = mce.getArgument(1)
      ) or
      (
        serviceName = "$cookies" and
        (methodName = "put" or methodName = "putObject") and
        e = mce.getArgument(1)
      )
    )
  }

  override predicate interpretsArgumentAsCode(Expr e) {
    exists(ScopeServiceReference scope, string methodName |
      methodName = "$apply" or
      methodName = "$applyAsync" or
      methodName = "$eval" or
      methodName = "$evalAsync" or
      methodName = "$watch" or
      methodName = "$watchCollection" or
      methodName = "$watchGroup" |
      e = scope.getAMethodCall(methodName).getArgument(0)
    ) or
    exists(ServiceReference service |
      service.getName() = "$compile" or
      service.getName() = "$parse" or
      service.getName() = "$interpolate" |
      e = service.getACall().getArgument(0)
    ) or
    exists(ServiceReference service, CallExpr filter, CallExpr filterInvocation |
      // `$filter('orderBy')(collection, expression)`
      service.getName() = "$filter" and
      filter = service.getACall() and
      filter.getArgument(0).(DataFlowNode).getALocalSource().(ConstantString).getStringValue() = "orderBy" and
      filterInvocation.getCallee() = filter and
      e = filterInvocation.getArgument(1)
    )
  }
}

/**
 * A link-function used in a custom AngularJS directive.
 */
class LinkFunction extends Function {
  LinkFunction() {
    this = any(GeneralDirective d).getALinkFunction()
  }

  /**
   * Gets the scope parameter of this function.
   */
  SimpleParameter getScopeParameter() {
    result = getParameter(0)
  }

  /**
   * Gets the element parameter of this function (contains a jqLite-wrapped DOM element).
   */
  SimpleParameter getElementParameter() {
    result = getParameter(1)
  }

  /**
   * Gets the attributes parameter of this function.
   */
  SimpleParameter getAttributesParameter() {
    result = getParameter(2)
  }

  /**
   * Gets the controller parameter of this function.
   */
  SimpleParameter getControllerParameter() {
    result = getParameter(3)
  }

  /**
   * Gets the transclude-function parameter of this function.
   */
  SimpleParameter getTranscludeFnParameter() {
    result = getParameter(4)
  }
}
