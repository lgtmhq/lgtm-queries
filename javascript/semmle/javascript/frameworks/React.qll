// Copyright 2018 Semmle Ltd.
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
 * Provides classes for working with React code.
 */

import javascript

/**
 * A React component.
 */
abstract class ReactComponent extends ASTNode {
  /**
   * Gets an instance method of this component with the given name.
   */
  abstract Function getInstanceMethod(string name);

  /**
   * Gets a reference to `this` in this component.
   */
  ThisExpr getAThisAccess() {
    result.getBinder() = getInstanceMethod(_)
  }

  /**
   * Gets a reference to the `props` object of this component.
   */
  DataFlowNode getAPropsSource() {
    exists (PropRefNode prn | prn = result |
      prn.getBase().getALocalSource() = getAThisAccess() and
      prn.getPropertyName() = "props"
    )
  }

  /**
   * Gets a reference to the `state` object of this component.
   */
  DataFlowNode getAStateSource() {
    exists (PropRefNode prn | prn = result |
      prn.getBase().getALocalSource() = getAThisAccess() and
      prn.getPropertyName() = "state"
    )
  }

  /**
   * Gets an expression that reads a prop of this component.
   */
  PropReadNode getAPropRead() {
    result.getBase().getALocalSource() = getAPropsSource()
  }

  /**
   * Gets an expression that reads prop `name` of this component.
   */
  PropReadNode getAPropRead(string name) {
    result = getAPropRead() and
    result.getPropertyName() = name
  }

  /**
   * Gets an expression that accesses a (transitive) property
   * of the state object of this component.
   */
  PropRefNode getAStateAccess() {
    result = getAStateSource() or
    result.getBase().getALocalSource() = getAStateAccess()
  }

  /**
   * Holds if this component specifies default values for (some of) its props.
   */
  predicate hasDefaultProps() {
    exists (PropWriteNode pwn | pwn.getBase().getALocalSource() = this |
      pwn.getPropertyName() = "defaultProps"
    )
  }
}

/**
 * A React component implemented as a plain function.
 */
class FunctionalComponent extends ReactComponent, Function {
  FunctionalComponent() {
    // heuristic: a function with a single parameter named `props`
    // that always returns a JSX element is probably a component
    getNumParameter() = 1 and
    exists (Parameter p | p = getParameter(0) |
      p.(SimpleParameter).getName().regexpMatch("(?i).*props.*") or
      p instanceof ObjectPattern
    ) and
    forex (Expr e | e = getAReturnedExpr() | e instanceof JSXElement)
  }

  override Function getInstanceMethod(string name) {
    name = "render" and result = this
  }

  override DataFlowNode getAPropsSource() {
    result.(VarRef).getVariable().getADeclaration() = getParameter(0)
  }
}

/**
 * A React component implemented as a class extending `React.Component`
 * or `React.PureComponent`.
 */
class ES2015Component extends ReactComponent, ClassDefinition {
  ES2015Component() {
    exists (PropAccess sup | sup = this.getSuperClass() |
      sup.getQualifiedName() = "React.Component" or
      sup.getQualifiedName() = "React.PureComponent"
    )
  }

  override Function getInstanceMethod(string name) {
    exists (MemberDefinition mem | mem = this.getMember(name) |
      result = mem.getInit() and
      not mem.isStatic() and
      not mem instanceof ConstructorDefinition
    )
  }

  override ThisExpr getAThisAccess() {
    result = ReactComponent.super.getAThisAccess() or
    result.getBinder() = getConstructor().getInit()
  }

}

/**
 * A legacy React component implemented using `React.createClass`.
 */
class ES5Component extends ReactComponent, ObjectExpr {
  ES5Component() {
    exists (MethodCallExpr create |
      create.getReceiver().(VarAccess).getName() = "React" and
      create.getMethodName() = "createClass" and
      create.getArgument(0).(DataFlowNode).getALocalSource() = this
    )
  }

  override Function getInstanceMethod(string name) {
    result = getPropertyByName(name).getInit()
  }

  override predicate hasDefaultProps() {
    exists (getInstanceMethod("getDefaultProps"))
  }
}