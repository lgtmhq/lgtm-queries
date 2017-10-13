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
 * Provides classes for working with AngularJS (also known as Angular 1.x)
 * applications.
 */

import javascript

module AngularJS {
  /**
   * Gets a string value that may flow into `nd`.
   */
  private string getStringValue(DataFlowNode nd) {
    result = nd.getALocalSource().(Expr).getStringValue()
  }

  /**
   * Holds if `nd` is a reference to the `angular` variable.
   */
  private predicate isAngularRef(DataFlowNode nd) {
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
  private predicate isModuleRef(DataFlowNode nd, AngularModule m) {
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
  private class ModuleApiCall extends @callexpr {
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
      // { link: { pre: function preLink() { ... }, post: function postLink() { ... } }
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

  /**
   * Gets the argument position at which the method called `methodName`
   * from the Module API expects an injectable function.
   */
  private int injectableArgPos(string methodName) {
    (methodName = "factory" or methodName = "directive" or
     methodName = "filter" or methodName = "controller") and result = 1
    or
    (methodName = "config" or methodName = "run") and result = 0
  }

  /**
   * An injectable function, that is, a function that has its dependency
   * parameters automatically provided by the AngularJS `$inject` service.
   */
  abstract class InjectableFunction extends DataFlowNode {
    InjectableFunction() {
      exists (MethodCallExpr m |
        isModuleRef(m.getReceiver(), _) and
        this = m.getArgument(injectableArgPos(m.getMethodName())).(DataFlowNode).getALocalSource()
      )
      or
      exists (ValueProperty controller |
        controller.getName() = "controller" and
        this = controller.getInit().(DataFlowNode).getALocalSource()
      )
    }

    /** Gets the parameter corresponding to dependency `name`. */
    abstract SimpleParameter getDependencyParameter(string name);

    /** Gets the function underlying this injectable function. */
    abstract Function asFunction();
  }

  /**
   * An injectable function that does not explicitly list its dependencies,
   * instead relying on implicit matching by parameter names.
   */
  private class FunctionWithImplicitDependencyAnnotation extends InjectableFunction, @function {
    FunctionWithImplicitDependencyAnnotation() {
      not this = any(FunctionWithExplicitDependencyAnnotation fwid).asFunction()
    }

    override SimpleParameter getDependencyParameter(string name) {
      result = asFunction().getParameterByName(name)
    }

    override Function asFunction() { result = this }
  }

  /**
   * An injectable function with an `$inject` property that lists its
   * dependencies.
   */
  private class FunctionWithInjectProperty extends FunctionWithImplicitDependencyAnnotation {
    ArrayExpr dependencies;

    FunctionWithInjectProperty() {
      exists (PropWriteNode pwn |
        pwn.getBase().getALocalSource() = this and
        pwn.getPropertyName() = "$inject" and
        pwn.getRhs().getALocalSource() = dependencies
      )
    }

    override SimpleParameter getDependencyParameter(string name) {
      exists (int i | getStringValue(dependencies.getElement(i)) = name |
        result = asFunction().getParameter(i)
      )
    }
  }

  /**
   * An injectable function embedded in an array of dependencies.
   */
  private class FunctionWithExplicitDependencyAnnotation extends InjectableFunction, @arrayexpr {
    Function function;

    FunctionWithExplicitDependencyAnnotation() {
      exists (ArrayExpr ae | ae = this |
        function = ae.getElement(ae.getSize()-1).(DataFlowNode).getALocalSource()
      )
    }

    override SimpleParameter getDependencyParameter(string name) {
      exists (int i | name = getStringValue(this.(ArrayExpr).getElement(i)) |
        result = asFunction().getParameter(i)
      )
    }

    override Function asFunction() { result = function }
  }

  newtype TDirectiveTargetType = E() or A() or C() or M()

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
   * A local variable that refers to an AngularJS service such as `$compile`
   * or `$scope`.
   */
  class InjectedService extends LocalVariable {
    /** The injectable function into which this service is injected. */
    InjectableFunction f;

    /** The name of the service this variable refers to. */
    string serviceName;

    InjectedService() {
      this = f.getDependencyParameter(serviceName).getVariable()
    }

    /** Gets the name of the service that this variable refers to. */
    string getServiceName() {
      result = serviceName
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
      exists (InjectedService location, MethodCallExpr mce, string m, int n |
        location.getServiceName() = "$location" and
        this = mce and
        mce.calls(location.getAnAccess(), m) and
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
      exists (InjectedService routeParams |
        routeParams.getServiceName() = "$routeParams" and
        this.(PropAccess).accesses(routeParams.getAnAccess(), _)
      )
    }

    override string getSourceType() {
      result = "$routeParams"
    }
  }
}
