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
 * Provides classes for working with the AngularJS `$injector` methods.
 *
 * INTERNAL: Do not import this module directly, import `AngularJS` instead.
 *
 * NOTE: The API of this library is not stable yet and may change in
 *       the future.
 *
 */

import javascript

private import AngularJS
private import DependencyInjectionServiceDefinitions

/**
 * Gets a string value that may flow into `nd`.
 */
private string getStringValue(DataFlowNode nd) {
  result = nd.getALocalSource().(Expr).getStringValue()
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
  exists (RecipeDefinition d |
    d.getMethodName() != "value" and
    d.getMethodName() != "constant" and
    n = d.getAServiceConstructor()
  ) or
  exists (ProviderRecipeDefinition d |
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
  ServiceReference getAResolvedDependency(SimpleParameter parameter) {
    exists(string name, InjectableFunctionServiceRequest request |
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
    exists(CustomServiceDefinition custom |
      custom.getServiceReference() = getAResolvedDependency(parameter) and
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

/**
 * DEPRECATED: Use `AngularJS::ServiceReference` instead.
 *
 * A local variable that refers to an AngularJS service such as `$compile`
 * or `$scope`.
 */
deprecated
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
