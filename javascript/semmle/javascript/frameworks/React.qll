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
 * Gets a reference to the 'React' object.
 */
DataFlow::SourceNode react() {
  result = DataFlow::globalVarRef("React")
  or
  result = DataFlow::moduleImport("react")
}

/**
 * DEPRECATED: Use `react()` instead.
 */
deprecated predicate isReactRef(DataFlowNode nd) {
  react().flowsToExpr(nd)
}

/**
 * A React component.
 */
abstract class ReactComponent extends ASTNode {
  /**
   * Gets an instance method of this component with the given name.
   */
  abstract Function getInstanceMethod(string name);

  /**
   * Gets the abstract value that represents this component.
   */
  abstract AbstractValue getAbstractComponent();

  /**
   * Holds if `e` is a reference to this component.
   */
  predicate isRef(Expr e) {
    e.analyze().getAValue() = getAbstractComponent()
  }

  /**
   * Gets a `this` access in an instance method of this component.
   */
  DataFlow::SourceNode getAThisAccess() {
    result.asExpr().(ThisExpr).getBinder() = getInstanceMethod(_)
  }

  /**
   * Gets a reference to the `props` object of this component.
   */
  DataFlow::SourceNode getAPropsSource() {
    exists (PropRefNode prn | result = DataFlow::valueNode(prn) |
      isRef(prn.getBase()) and
      prn.getPropertyName() = "props"
    )
  }

  /**
   * Gets a reference to the `state` object of this component.
   */
  DataFlow::SourceNode getAStateSource() {
    exists (PropRefNode prn | result = DataFlow::valueNode(prn) |
      isRef(prn.getBase()) and
      prn.getPropertyName() = "state"
    )
  }

  /**
   * Gets an expression that reads a prop of this component.
   */
  PropReadNode getAPropRead() {
    getAPropsSource().flowsToExpr(result.getBase())
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
  DataFlow::SourceNode getAStateAccess() {
    result = getAStateSource()
    or
    exists (PropRefNode prn | result = DataFlow::valueNode(prn) |
      getAStateAccess().flowsToExpr(prn.getBase())
    )
  }

  /**
   * Holds if this component specifies default values for (some of) its props.
   */
  predicate hasDefaultProps() {
    exists (PropWriteNode pwn | isRef(pwn.getBase()) |
      pwn.getPropertyName() = "defaultProps"
    )
  }

  /**
   * Gets the render method of this component.
   */
  Function getRenderMethod() {
    result = getInstanceMethod("render")
  }

  /**
   * Gets a call to method `name` on this component.
   */
  MethodCallExpr getAMethodCall(string name) {
    isRef(result.getReceiver()) and
    result.getMethodName() = name
  }

}

/**
 * A React component implemented as a plain function.
 */
class FunctionalComponent extends ReactComponent, Function {
  FunctionalComponent() {
    // heuristic: a function with a single parameter named `props`
    // that always returns a JSX element or fragment is probably
    // a component
    getNumParameter() = 1 and
    exists (Parameter p | p = getParameter(0) |
      p.(SimpleParameter).getName().regexpMatch("(?i).*props.*") or
      p instanceof ObjectPattern
    ) and
    forex (Expr e | e = getAReturnedExpr() | e instanceof JSXNode)
  }

  override Function getInstanceMethod(string name) {
    name = "render" and result = this
  }

  override DataFlow::SourceNode getAPropsSource() {
    result = DataFlow::parameterNode(getParameter(0))
  }

  override AbstractValue getAbstractComponent() {
    result = TAbstractInstance(TAbstractFunction(this))
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

  override AbstractValue getAbstractComponent() {
    result = TAbstractInstance(TAbstractClass(this))
  }

}

/**
 * A legacy React component implemented using `React.createClass` or `create-react-class`.
 */
class ES5Component extends ReactComponent, ObjectExpr {
  ES5Component() {
    exists (DataFlow::CallNode create |
      // React.createClass({...})
      create = react().getAMethodCall("createClass")
      or
      // require('create-react-class')({...})
      create = DataFlow::moduleImport("create-react-class").getACall()
      |
      create.getArgument(0).getALocalSource().asExpr() = this
    )
  }

  override Function getInstanceMethod(string name) {
    result = getPropertyByName(name).getInit()
  }

  override predicate hasDefaultProps() {
    exists (getInstanceMethod("getDefaultProps"))
  }

  override AbstractValue getAbstractComponent() {
    result = TAbstractObjectLiteral(this)
  }

}

/**
 * A DOM element created by a React function.
 */
private abstract class ReactElementDefinition extends DOM::ElementDefinition {

  override DOM::ElementDefinition getParent() {
    none()
  }

}

/**
 * A DOM element created by the `React.createElement` function.
 */
private class CreateElementDefinition extends ReactElementDefinition {

  string tagName;

  CreateElementDefinition() {
    exists (MethodCallExpr mce |
      mce = this and
      mce = react().getAMethodCall("createElement").asExpr() and
      mce.getArgument(0).mayHaveStringValue(tagName)
    )
  }

  override string getName() {
    result = tagName
  }

}

/**
 * A DOM element created by the (legacy) `React.createFactory` function.
 */
private class FactoryDefinition extends ReactElementDefinition {

  string tagName;

  FactoryDefinition() {
    exists (DataFlow::CallNode mce |
      mce = react().getAMethodCall("createFactory") and
      mce.getArgument(0).asExpr().mayHaveStringValue(tagName) and
      this = mce.getACall().asExpr()
    )
  }

  override string getName() {
    result = tagName
  }

}

/**
 * Flow analysis for `this` expressions inside a function that is called with
 * `React.Children.map` or a similar library function that binds `this` of a
 * callback.
 *
 * However, since the function could be invoked in another way, we additionally
 * still infer the ordinary abstract value.
 */
private class AnalyzedThisInBoundCallback extends AnalyzedValueNode {

  AnalyzedValueNode thisSource;

  override ThisExpr astNode;

  AnalyzedThisInBoundCallback() {
    exists(DataFlow::CallNode bindingCall, string binderName |
      // React.Children.map or React.Children.forEach
      binderName = "map" or
      binderName = "forEach" |
      bindingCall = react().getAPropertyRead("Children").getAMemberCall(binderName) and
      3 = bindingCall.getNumArgument() and
      astNode.getBinder() = bindingCall.getCallback(1).getFunction() and
      thisSource = bindingCall.getArgument(2)
    )
  }

  override AbstractValue getALocalValue() {
    result = thisSource.getALocalValue() or
    result = AnalyzedValueNode.super.getALocalValue()
  }

}
