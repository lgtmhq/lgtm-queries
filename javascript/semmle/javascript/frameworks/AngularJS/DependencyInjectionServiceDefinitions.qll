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
 * Provides classes for working with the AngularJS `$provide` methods: `service`, `factory`, etc..
 *
 * Supports registration and lookup of dependency injection services.
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
 * A reference to a service.
 */
private newtype TServiceReference =
MkBuiltinServiceReference(string name) { exists (getBuiltinKind(name)) } or
MkCustomServiceReference(CustomServiceDefinition service)

/**
 * A reference to a service.
 */
abstract class ServiceReference extends TServiceReference {

  /** Gets a textual representation of this element. */
  string toString() {
    result = getName()
  }

  /**
   * Gets the name of this reference.
   */
  abstract string getName();

  /**
   * Gets an access to the referenced service.
   */
  DataFlowNode getAnAccess() {
    result.(DataFlowNode).getALocalSource() = any(ServiceRequest request).getAnAccess(this)
  }

  /**
   * Gets a call that invokes the referenced service.
   */
  CallExpr getACall() {
    result.getCallee() = getAnAccess()
  }

  /**
   * Gets a method call that invokes method `methodName` on the referenced service.
   */
  MethodCallExpr getAMethodCall(string methodName) {
    result.getReceiver() = getAnAccess() and
    result.getMethodName() = methodName
  }

  /**
   * Gets an access to property `propertyName` on the referenced service.
   */
  PropRefNode getAPropertyAccess(string propertyName) {
    result.getBase() = getAnAccess() and
    result.getPropertyName() = propertyName
  }

}

/**
 * A reference to a builtin service.
 */
class BuiltinServiceReference extends ServiceReference, MkBuiltinServiceReference {
  override string getName() {
    this = MkBuiltinServiceReference(result)
  }
}

/**
 * A reference to a custom service.
 */
class CustomServiceReference extends ServiceReference, MkCustomServiceReference {
  override string getName() {
    exists(CustomServiceDefinition def |
      this = MkCustomServiceReference(def) and
      result = def.getName()
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
      exists(InjectableFunction f |
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

  /** Gets the reference to the defined service. */
  ServiceReference getServiceReference() {
    result = MkCustomServiceReference(this)
  }
}

/**
 * Gets a builtin service with a specific kind.
 */
BuiltinServiceReference getBuiltinServiceOfKind(string kind) {
  exists(string name |
    kind = getBuiltinKind(name) and
    result = MkBuiltinServiceReference(name)
  )
}

/**
 * A request for one or more AngularJS services.
 */
abstract class ServiceRequest extends Expr {

  /**
   * Gets an access to `service` from this request.
   */
  abstract DataFlowNode getAnAccess(ServiceReference service);

}

/**
 * The request for a scope service in the form of the link-function of a directive.
 */
private class LinkFunctionWithScopeInjection extends ServiceRequest {

  LinkFunctionWithScopeInjection() {
    this instanceof LinkFunction
  }

  override DataFlowNode getAnAccess(ServiceReference service) {
    service instanceof ScopeServiceReference and
    result = this.(LinkFunction).getScopeParameter().getAVariable().getAnAccess()
  }

}


/**
 * A request for a service, in the form of a dependency-injected function.
 */
class InjectableFunctionServiceRequest extends ServiceRequest {

  InjectableFunction injectedFunction;

  InjectableFunctionServiceRequest() {
    if(exists(injectedFunction.getAnExplicitDependencyInjection())) then
    this = injectedFunction.getAnExplicitDependencyInjection()
    else
    this = injectedFunction
  }

  /**
   * Gets the function of this request.
   */
  InjectableFunction getAnInjectedFunction() {
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
  ServiceReference getAServiceDefinition(string name) {
    result.getName() = name
  }

  override DataFlowNode getAnAccess(ServiceReference service) {
    exists(SimpleParameter param |
      service = injectedFunction.getAResolvedDependency(param) and
      result = param.getVariable().getAnAccess()
    )
  }

}

private DataFlowNode getFactoryFunctionResult(RecipeDefinition def) {
  exists(Function factoryFunction |
    factoryFunction = def.getAServiceConstructor().(InjectableFunction).asFunction() and
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

    result = getAServiceConstructor().(InjectableFunction).asFunction()
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
      enclosing = getAServiceConstructor().(InjectableFunction).asFunction() and
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

/**
 * The `$scope` or `$rootScope` service.
 */
class ScopeServiceReference extends BuiltinServiceReference {
  ScopeServiceReference() {
    getName() = "$scope" or getName() = "$rootScope"
  }
}
