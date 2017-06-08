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
    exists (DataFlowNode src | src = nd.getALocalSource() |
      // either as a global
      src.(GlobalVarAccess).getName() = "angular" or
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
   * An AngularJS directive, that is, an object returned by the factory function
   * in a directive definition.
   */
  class DirectiveInstance extends @dataflownode {
    /** The definition of this directive. */
    DirectiveDefinition definition;
  
    DirectiveInstance() {
      this = definition.getFactoryFunction().asFunction().getAReturnedExpr().(DataFlowNode).getALocalSource()
    }
  
    /** Gets the definition of this directive. */
    DirectiveDefinition getDefinition() {
      result = definition
    }
  
    /** Gets the method `name` of this directive. */
    Function getMethod(string name) {
      exists (PropWriteNode pw |
        pw.getBase().getALocalSource() = this and
        pw.getPropertyName() = name and
        pw.getRhs().getALocalSource() = result
      )
    }
  
    /** Gets a textual representation of this directive. */
    string toString() { result = definition.getName() }
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
}
