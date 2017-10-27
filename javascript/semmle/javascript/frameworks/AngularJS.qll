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

  /**
   * Gets the argument position at which the method called `methodName`
   * from the Module API expects an injectable function.
   *
   * This method excludes the method names that are also present on the AngularJS '$provide' object.
   */
  private int injectableArgPos(string methodName) {
    (methodName = "directive" or
      methodName = "filter" or methodName = "controller" or
      methodName = "animation") and result = 1
    or
    (methodName = "config" or methodName = "run") and result = 0
  }

  /**
   * Holds if `nd` is an `angular.injector()` value
   */
  private predicate isAngularInjector(DataFlowNode nd) {
    exists(MethodCallExpr mce |
      nd.getALocalSource() = mce and
      isAngularRef(mce.getReceiver()) and
      mce.getMethodName() = "injector"
    )
  }

  /**
   * A call to `$angular.injector().invoke(...)`
   */
  class InjectorInvokeCall extends MethodCallExpr {
    InjectorInvokeCall() {
      isAngularInjector(this.getReceiver()) and
      this.getMethodName() = "invoke"
    }

    Expr getInjectedArgument() {
      result = getArgument(0)
    }
  }
  /**
   * Holds if `n` is an argument to a function that will dependency inject `n`.
   */
  private predicate isDependencyInjected(DataFlowNode n) {
    exists (ModuleApiCall m |
      n = m.getArgument(injectableArgPos(m.(MethodCallExpr).getMethodName())).(DataFlowNode).getALocalSource()
    ) or
    exists (InjectorInvokeCall invk |
      n = invk.getInjectedArgument().(DataFlowNode).getALocalSource()
    ) or
    exists (DependencyInjectionServiceDefinitions::RecipeDefinition d |
      d.getMethodName() != "value" and
      d.getMethodName() != "constant" and
      n = d.getAServiceConstructor()
    ) or
    exists (DependencyInjectionServiceDefinitions::ProviderRecipeDefinition d |
      n = d.getAService()
    )
  }

  /**
   * Holds if `n` may be dependency injected (an over-approximation of `isDependencyInjected`).
   */
  private predicate dependencyInjectionCandidate(DataFlowNode n) {
    isDependencyInjected(n) or
    // other cases
    exists (ValueProperty controller |
      controller.getName() = "controller" and
      n = controller.getInit().(DataFlowNode).getALocalSource()
    )
  }

  /**
   * An injectable function, that is, a function that could have its dependency
   * parameters automatically provided by the AngularJS `$inject` service.
   */
  abstract class InjectableFunction extends DataFlowNode {

    /** Gets the parameter corresponding to dependency `name`. */
    abstract SimpleParameter getDependencyParameter(string name);

    /**
     * Gets the `i`th dependency declaration, which is also named `name`.
     */
    abstract ASTNode getDependencyDeclaration(int i, string name);

    /**
     * Gets an ASTNode for the `name` dependency declaration.
     */
    ASTNode getADependencyDeclaration(string name) {
      result = getDependencyDeclaration(_, name)
    }

    /**
     * Gets the ASTNode for the `i`th dependency declaration.
     */
    ASTNode getDependencyDeclaration(int i) {
      result = getDependencyDeclaration(i, _)
    }


    /** Gets the function underlying this injectable function. */
    abstract Function asFunction();

    /** Gets a location where this function is explicitly dependency injected. */
    abstract ASTNode getAnExplicitDependencyInjection();

    /**
     * Holds if this is an argument to a function that will dependency inject it.
     */
    predicate isDependencyInjected(){
      isDependencyInjected(this)
    }

    /**
     * Gets a service corresponding to the dependency-injected `parameter`.
     */
    DependencyInjectionServiceDefinitions::ServiceIdentity getAResolvedDependency(SimpleParameter parameter) {
      exists(string name, DependencyInjectionServiceDefinitions::InjectableFunctionServiceRequest request |
        this = request.getAnInjectedFunction() and
        parameter = getDependencyParameter(name) and
        result = request.getAServiceDefinition(name)
      )
    }

    /**
     * Gets a Custom service corresponding to the dependency-injected `parameter`.
     * (this is a convenience variant of `getAResolvedDependency`)
     */
    DataFlowNode getCustomServiceDependency(SimpleParameter parameter) {
      exists(DependencyInjectionServiceDefinitions::CustomServiceDefinition custom |
        custom.getServiceIdentity() = getAResolvedDependency(parameter) and
        result = custom.getAService()
      )
    }

  }

  /**
   * An injectable function that does not explicitly list its dependencies,
   * instead relying on implicit matching by parameter names.
   */
  private class FunctionWithImplicitDependencyAnnotation extends InjectableFunction, @function {
    FunctionWithImplicitDependencyAnnotation() {
      dependencyInjectionCandidate(this) and
      not exists(getAPropertyDependencyInjection(this))
    }

    override SimpleParameter getDependencyParameter(string name) {
      result = asFunction().getParameterByName(name)
    }

    override SimpleParameter getDependencyDeclaration(int i, string name) {
      result.getName() = name and
      result = asFunction().getParameter(i)
    }

    override Function asFunction() { result = this }

    override ASTNode getAnExplicitDependencyInjection() {
      none()
    }
  }

  private PropWriteNode getAPropertyDependencyInjection(Function function){
    result.getBase().getALocalSource() = function and
    result.getPropertyName() = "$inject"
  }

  /**
   * An injectable function with an `$inject` property that lists its
   * dependencies.
   */
  private class FunctionWithInjectProperty extends InjectableFunction, @function {
    ArrayExpr dependencies;

    FunctionWithInjectProperty() {
      (dependencyInjectionCandidate(this) or
        exists(FunctionWithExplicitDependencyAnnotation f | f.asFunction() = this)
      ) and
      exists (PropWriteNode pwn |
        pwn = getAPropertyDependencyInjection(this) and
        pwn.getRhs().getALocalSource() = dependencies
      )
    }

    override SimpleParameter getDependencyParameter(string name) {
      exists (int i | getStringValue(dependencies.getElement(i)) = name |
        result = asFunction().getParameter(i)
      )
    }

    override ASTNode getDependencyDeclaration(int i, string name) {
      result = dependencies.getElement(i) and
      getStringValue(result) = name
    }

    override Function asFunction() { result = this }

    override ASTNode getAnExplicitDependencyInjection() {
      result = getAPropertyDependencyInjection(this)
    }
  }

  /**
   * An injectable function embedded in an array of dependencies.
   */
  private class FunctionWithExplicitDependencyAnnotation extends InjectableFunction, @arrayexpr {
    Function function;

    FunctionWithExplicitDependencyAnnotation() {
      dependencyInjectionCandidate(this) and
      exists (ArrayExpr ae | ae = this |
        function = ae.getElement(ae.getSize()-1).(DataFlowNode).getALocalSource()
      )
    }

    override SimpleParameter getDependencyParameter(string name) {
      exists (int i | name = getStringValue(this.(ArrayExpr).getElement(i)) |
        result = asFunction().getParameter(i)
      )
    }

    override ASTNode getDependencyDeclaration(int i, string name) {
      result = this.(ArrayExpr).getElement(i) and
      getStringValue(result) = name
    }

    override Function asFunction() { result = function }

    override ASTNode getAnExplicitDependencyInjection() {
      result = this or result = asFunction().(InjectableFunction).getAnExplicitDependencyInjection()
    }
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

  /**
   * Provides classes for working with the AngularJS `$provide` methods: `service`, `factory`, etc..
   *
   * Supports registration and lookup of dependency injection services.
   */
  module DependencyInjectionServiceDefinitions {

    /**
     * Service types.
     */
    private newtype TServiceIdentity =
    MkBuiltinService(string name) { exists (getBuiltinKind(name)) } or
    MkCustomService(CustomServiceDefinition service)

    abstract class ServiceIdentity extends TServiceIdentity {
      abstract string toString();
    }

    class BuiltinServiceIdentity extends ServiceIdentity, MkBuiltinService {
      string toString() {
        this = MkBuiltinService(result)
      }
    }

    class CustomServiceIdentity extends ServiceIdentity, MkCustomService {
      string toString() {
        exists(CustomServiceDefinition def |
          this = MkCustomService(def) and
          result = def.toString()
        )
      }
    }

    /**
     * Gets the kind of the builtin "service" named `name`.
     *
     * The possible kinds are:
     * - controller-only: services that are only available to controllers.
     * - provider: a provider for a service.
     * - service: a service.
     * - type: a special builtin service that is usable everywhere.
     */
    private string getBuiltinKind(string name) {
      // according to https://docs.angularjs.org/api
      result = "controller-only" and  name = "$scope"
      or (
        result = "service" and (
          // ng
          name = "$anchorScroll" or
          name = "$animate" or
          name = "$animateCss" or
          name = "$cacheFactory" or
          name = "$controller" or
          name = "$document" or
          name = "$exceptionHandler" or
          name = "$filter" or
          name = "$http" or
          name = "$httpBackend" or
          name = "$httpParamSerializer" or
          name = "$httpParamSerializerJQLike" or
          name = "$interpolate" or
          name = "$interval" or
          name = "$jsonpCallbacks" or
          name = "$locale" or
          name = "$location" or
          name = "$log" or
          name = "$parse" or
          name = "$q" or
          name = "$rootElement" or
          name = "$rootScope" or
          name = "$sce" or
          name = "$sceDelegate" or
          name = "$templateCache" or
          name = "$templateRequest" or
          name = "$timeout" or
          name = "$window" or
          name = "$xhrFactory" or
          // auto
          name = "$injector" or
          name = "$provide" or
          // ngAnimate
          name = "$animate" or
          name = "$animateCss" or
          // ngAria
          name = "$aria" or
          // ngComponentRouter
          name = "$rootRouter" or
          name = "$routerRootComponent" or
          // ngCookies
          name = "$cookieStore" or
          name = "$cookies" or
          //ngMock
          name = "$animate" or
          name = "$componentController" or
          name = "$controller" or
          name = "$exceptionHandler" or
          name = "$httpBackend" or
          name = "$interval" or
          name = "$log" or
          name = "$timeout" or
          //ngMockE2E
          name = "$httpBackend" or
          // ngResource
          name = "$resource" or
          // ngRoute
          name = "$route" or
          name = "$routeParams" or
          // ngSanitize
          name = "$sanitize" or
          // ngTouch
          name = "$swipe"
        )
      ) or (
        result = "provider" and (
          // ng
          name = "$anchorScrollProvider" or
          name = "$animateProvider" or
          name = "$compileProvider" or
          name = "$controllerProvider" or
          name = "$filterProvider" or
          name = "$httpProvider" or
          name = "$interpolateProvider" or
          name = "$locationProvider" or
          name = "$logProvider" or
          name = "$parseProvider" or
          name = "$provider" or
          name = "$qProvider" or
          name = "$rootScopeProvider" or
          name = "$sceDelegateProvider" or
          name = "$sceProvider" or
          name = "$templateRequestProvider" or
          // ngAria
          name = "$ariaProvider" or
          // ngCookies
          name = "$cookiesProvider" or
          // ngmock
          name = "$exceptionHandlerProvider" or
          // ngResource
          name = "$resourceProvider" or
          // ngRoute
          name = "$routeProvider" or
          // ngSanitize
          name = "$sanitizeProvider"
        )
      ) or (
        result = "type" and (
          // ng
          name = "$cacheFactory" or
          name = "$compile" or
          name = "$rootScope" or
          // ngMock
          name = "$rootScope"
        )
      )
    }

    /**
     * A definition of a custom AngularJS dependency injection service.
     */
    abstract class RecipeDefinition extends MethodCallExpr {

      string methodName;

      string name;

      RecipeDefinition() {
        (isModuleRef(getReceiver(), _) or
          exists(AngularJS::InjectableFunction f |
            f.getDependencyParameter("$provide").getAVariable().getAnAccess() = getReceiver()
          )) and
        methodName = getMethodName() and
        name = getStringValue(getArgument(0))
      }

      /** Gets the name of the defined service. */
      string getName() { result = name }

      /** Gets a value used for creating the service provided by this definition. */
      DataFlowNode getAServiceConstructor() {
        result = getArgument(1).(DataFlowNode).getALocalSource()
      }

      /** Gets a service created by `getAServiceConstructor`*/
      abstract DataFlowNode getAService();
    }

    /**
     * A custom AngularJS service, either defined through `$provide.service` or `module.service` or a similar method.
     */
    class CustomServiceDefinition extends Expr {

      RecipeDefinition def;

      CustomServiceDefinition() {
        def = this
      }

      string getName() {
        result = def.getName()
      }

      /** Gets a service defined by this definition. */
      DataFlowNode getAService() {
        result = def.getAService()
      }

      /** Gets the identity of the defined service. */
      ServiceIdentity getServiceIdentity() {
        result = MkCustomService(this)
      }
    }

    /**
     * Gets a service with the name `name`.
     */
    private ServiceIdentity getAGlobalServiceDefinition(string name) {
      result = MkBuiltinService(name) or
      exists(CustomServiceDefinition custom |
        name = custom.getName() and
        result = MkCustomService(custom))
    }

    /**
     * Gets a builtin service with a specific kind.
     */
    ServiceIdentity getBuiltinServiceOfKind(string kind) {
      exists(string name |
        kind = getBuiltinKind(name) and
        result = MkBuiltinService(name)
      )
    }

    /**
     * A request for a service, in the form of a dependency-injected function.
     */
    class InjectableFunctionServiceRequest extends Expr {

      AngularJS::InjectableFunction injectedFunction;

      InjectableFunctionServiceRequest() {
        if(exists(injectedFunction.getAnExplicitDependencyInjection())) then
        this = injectedFunction.getAnExplicitDependencyInjection()
        else
        this = injectedFunction
      }

      AngularJS::InjectableFunction getAnInjectedFunction() {
        result = injectedFunction
      }

      /**
       * Gets a name of a requested service.
       */
      string getAServiceName() {
        exists(getAnInjectedFunction().getADependencyDeclaration(result))
      }

      /**
       * Gets a service with the specified name, relative to this request.
       * (implementation detail: all services are in the global namespace)
       */
      ServiceIdentity getAServiceDefinition(string name) {
        result = getAGlobalServiceDefinition(name)
      }
    }

    private DataFlowNode getFactoryFunctionResult(RecipeDefinition def) {
      exists(Function factoryFunction |
        factoryFunction = def.getAServiceConstructor().(AngularJS::InjectableFunction).asFunction() and
        result = factoryFunction.getAReturnedExpr().(DataFlowNode).getALocalSource()
      )
    }

    /**
     * An AngularJS factory recipe definition, that is, a method call of the form
     * `module.factory("name", f)`.
     */
    class FactoryRecipeDefinition extends RecipeDefinition {
      FactoryRecipeDefinition() {
        methodName = "factory"
      }

      override DataFlowNode getAService() {

        /* The Factory recipe constructs a new service using a function
        with zero or more arguments (these are dependencies on other
          services). The return value of this function is the service
        instance created by this recipe.  */
        result = getFactoryFunctionResult(this)
      }
    }

    /**
     * An AngularJS decorator recipe definition, that is, a method call of the form
     * `module.decorator("name", f)`.
     */
    class DecoratorRecipeDefinition extends RecipeDefinition {
      DecoratorRecipeDefinition() {
        methodName = "decorator"
      }

      override DataFlowNode getAService() {

        /* The return value of the function provided to the decorator
        will take place of the service, directive, or filter being
        decorated.*/
        result = getFactoryFunctionResult(this)
      }
    }


    /**
     * An AngularJS service recipe definition, that is, a method call of the form
     * `module.service("name", f)`.
     */
    class ServiceRecipeDefinition extends RecipeDefinition {
      ServiceRecipeDefinition() {
        methodName = "service"
      }

      override DataFlowNode getAService() {

        /* The service recipe produces a service just like the Value or
        Factory recipes, but it does so by invoking a constructor with
        the new operator. The constructor can take zero or more
        arguments, which represent dependencies needed by the instance
        of this type. */

        result = getAServiceConstructor().(AngularJS::InjectableFunction).asFunction()
      }
    }

    /**
     * An AngularJS value recipe definition, that is, a method call of the form
     * `module.value("name", value)`.
     */
    class ValueRecipeDefinition extends RecipeDefinition {
      ValueRecipeDefinition() {
        methodName = "value"
      }

      override DataFlowNode getAService() {
        result = getAServiceConstructor()
      }
    }

    /**
     * An AngularJS constant recipe definition, that is, a method call of the form
     * `module.constant("name", "constant value")`.
     */
    class ConstantRecipeDefinition extends RecipeDefinition {
      ConstantRecipeDefinition() {
        methodName = "constant"
      }

      override DataFlowNode getAService() {
        result = getAServiceConstructor()
      }
    }

    /**
     * An AngularJS provider recipe definition, that is, a method call of the form
     * `module.provider("name", fun)`.
     */
    class ProviderRecipeDefinition extends RecipeDefinition {
      ProviderRecipeDefinition() {
        methodName = "provider"
      }

      override string getName(){
        result = name or result = name + "Provider"
      }

      override DataFlowNode getAService() {

        /* The Provider recipe is syntactically defined as a custom type
        that implements a $get method. This method is a factory function
        just like the one we use in the Factory recipe. In fact, if you
        define a Factory recipe, an empty Provider type with the $get
        method set to your factory function is automatically created
        under the hood.  */

        exists(Function enclosing, PropWriteNode prop |
          enclosing = getAServiceConstructor().(AngularJS::InjectableFunction).asFunction() and
          enclosing = prop.(Expr).getEnclosingFunction() and
          prop.getBase() instanceof ThisExpr and
          prop.getPropertyName() = "$get" and
          result = prop.getRhs().(DataFlowNode).getALocalSource()
        )
      }
    }

    /**
     * An AngularJS config method definition, that is, a method call of the form
     * `module.config(fun)`.
     */
    class ConfigMethodDefinition extends ModuleApiCall  {
      ConfigMethodDefinition() {
        methodName = "config"
      }

      /**
       * Gets a provided configuration method.
       */
      InjectableFunction getConfigMethod() {
        result = getArgument(0).(DataFlowNode).getALocalSource()
      }
    }

    /**
     * An AngularJS run method definition, that is, a method call of the form
     * `module.run(fun)`.
     */
    class RunMethodDefinition extends ModuleApiCall  {
      RunMethodDefinition() {
        methodName = "run"
      }

      /**
       * Gets a provided run method.
       */
      InjectableFunction getRunMethod() {
        result = getArgument(0).(DataFlowNode).getALocalSource()
      }
    }
  }

}
