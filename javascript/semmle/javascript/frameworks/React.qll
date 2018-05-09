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
   * Gets the value that instantiates this component when invoked.
   */
  abstract DataFlow::SourceNode getComponentCreatorSource();

  /**
   * Gets a reference to this component.
   */
  DataFlow::Node ref() {
    result.analyze().getAValue() = getAbstractComponent()
  }

  /**
   * Gets a `this` access in an instance method of this component.
   */
  DataFlow::SourceNode getAThisAccess() {
    result.asExpr().(ThisExpr).getBinder() = getInstanceMethod(_)
  }

  /**
   * Gets an access to the `props` object of this component.
   *
   * DEPRECATED: Use `getADirectPropsAccess` instead.
   */
  deprecated DataFlow::SourceNode getAPropsSource() {
    result = getADirectPropsAccess()
  }

  /**
   * Gets an access to the `props` object of this component.
   */
  abstract DataFlow::SourceNode getADirectPropsAccess();

  /**
   * Gets an access to the `state` object of this component.
   *
   * DEPRECATED: Use `getADirectStateAccess` instead.
   */
  deprecated DataFlow::SourceNode getAStateSource() {
    result = getADirectStateAccess()
  }

  /**
   * Gets an access to the `state` object of this component.
   */
  DataFlow::SourceNode getADirectStateAccess() {
    result.(DataFlow::PropRef).accesses(ref(), "state")
  }

  /**
   * Gets a data flow node that reads a prop of this component.
   */
  DataFlow::PropRead getAPropRead() {
    getADirectPropsAccess().flowsTo(result.getBase())
  }

  /**
   * Gets a data flow node that reads prop `name` of this component.
   */
  DataFlow::PropRead getAPropRead(string name) {
    result = getAPropRead() and
    result.getPropertyName() = name
  }

  /**
   * Gets an expression that accesses a (transitive) property
   * of the state object of this component.
   */
  DataFlow::SourceNode getAStateAccess() {
    result = getADirectStateAccess()
    or
    exists (DataFlow::PropRef prn | result = prn |
      getAStateAccess().flowsTo(prn.getBase())
    )
  }

  /**
   * Holds if this component specifies default values for (some of) its
   * props.
   */
  predicate hasDefaultProps() {
    exists (getADefaultPropsSource())
  }

  /**
   * Gets the object that specifies default values for (some of) this
   * components' props.
   */
  abstract DataFlow::SourceNode getADefaultPropsSource();

  /**
   * Gets the render method of this component.
   */
  Function getRenderMethod() {
    result = getInstanceMethod("render")
  }

  /**
   * Gets a call to method `name` on this component.
   */
  DataFlow::MethodCallNode getAMethodCall(string name) {
    result.calls(ref(), name)
  }

  /**
   * Gets a value that will become (part of) the state
   * object of this component, for example an assignment to `this.state`.
   */
  DataFlow::SourceNode getACandidateStateSource() {
    exists (DataFlow::PropWrite pwn, DataFlow::Node rhs |
      // a direct definition: `this.state = o`
      result.flowsTo(rhs) and
      pwn.writes(ref(), "state", rhs)
    )
    or
    exists (DataFlow::MethodCallNode mce, DataFlow::SourceNode arg0 |
      mce = getAMethodCall("setState") or
      mce = getAMethodCall("forceUpdate") |
      arg0.flowsTo(mce.getArgument(0)) and
      if arg0 instanceof DataFlow::FunctionNode then
        // setState with callback: `this.setState(() => {foo: 42})`
        result.flowsToExpr(arg0.(DataFlow::FunctionNode).getFunction().getAReturnedExpr())
      else
        // setState with object: `this.setState({foo: 42})`
        result = arg0
    )
  }

  /**
   * Gets a value that used to be the state object of this
   * component, for example the `prevState` parameter of the
   * `comoponentDidUpdate` method of this component.
   */
  DataFlow::SourceNode getAPreviousStateSource() {
    exists (DataFlow::FunctionNode callback, int stateParameterIndex |
      // "prevState" object as callback argument
      callback.getParameter(stateParameterIndex).flowsTo(result) |
      // setState: (prevState, props)
      callback = getAMethodCall("setState").getCallback(0) and
      stateParameterIndex = 0
      or
      // componentDidUpdate: (prevProps, prevState)
      callback = getInstanceMethod("componentDidUpdate").flow() and
      stateParameterIndex = 1
    )
  }

  /**
   * Gets a value that will become (part of) the props
   * object of this component, for example the argument to the
   * constructor of this component.
   */
  DataFlow::SourceNode getACandidatePropsSource() {
    exists (DataFlow::InvokeNode call |
      getComponentCreatorSource().flowsTo(call.getCallee()) and
      result.flowsTo(call.getArgument(0))
    ) or
    result = getADefaultPropsSource()
  }

  /**
   * Gets an expression that will become the value of the props property
   * `name` of this component, for example the attribute value of a JSX
   * element that instantiates this component.
   */
  DataFlow::Node getACandidatePropsValue(string name) {
    getACandidatePropsSource().hasPropertyWrite(name, result) or
    exists (ReactJSXElement e, JSXAttribute attr |
      this = e.getComponent() and
      attr = e.getAttributeByName(name) and
      result.asExpr() = attr.getValue()
    )
  }

  /**
   * Gets a value that used to be the props object of this
   * component, for example the `prevProps` parameter of the
   * `comoponentDidUpdate` method of this component.
   */
  DataFlow::SourceNode getAPreviousPropsSource() {
    exists (DataFlow::FunctionNode callback, int propsParameterIndex |
      // "prevProps" object as callback argument
      callback.getParameter(propsParameterIndex).flowsTo(result) |
      // setState: (prevState, props)
      callback = getAMethodCall("setState").getCallback(0) and
      propsParameterIndex = 1
      or
      // componentDidUpdate: (prevProps, prevState)
      callback = getInstanceMethod("componentDidUpdate").flow() and
      propsParameterIndex = 0
    )
  }

}

/**
 * A React component implemented as a plain function.
 */
class FunctionalComponent extends ReactComponent, Function {
  FunctionalComponent() {
    // heuristic: a function with a single parameter named `props`
    // that always returns a JSX element or fragment, or a React
    // element is probably a component
    getNumParameter() = 1 and
    exists (Parameter p | p = getParameter(0) |
      p.(SimpleParameter).getName().regexpMatch("(?i).*props.*") or
      p instanceof ObjectPattern
    ) and
    forex (Expr e | e.flow().(DataFlow::SourceNode).flowsToExpr(getAReturnedExpr()) |
      e instanceof JSXNode or
      e instanceof ReactElementDefinition
    )
  }

  override Function getInstanceMethod(string name) {
    name = "render" and result = this
  }

  override DataFlow::SourceNode getADirectPropsAccess() {
    result = DataFlow::parameterNode(getParameter(0))
  }

  override AbstractValue getAbstractComponent() {
    result = TAbstractInstance(TAbstractFunction(this))
  }

  override DataFlow::SourceNode getComponentCreatorSource() {
    result = DataFlow::valueNode(this)
  }

  override DataFlow::SourceNode getADefaultPropsSource() {
    exists (DataFlow::Node props |
      result.flowsTo(props) and
      DataFlow::valueNode(this).(DataFlow::SourceNode).hasPropertyWrite("defaultProps", props)
    )
  }

}

/**
 * A React component implemented as a class extending `React.Component`
 * or `React.PureComponent`.
 */
class ES2015Component extends ReactComponent, ClassDefinition {
  ES2015Component() {
    exists (DataFlow::SourceNode sup | sup.flowsToExpr(getSuperClass()) |
      exists (PropAccess access | access = sup.asExpr() |
        access.getQualifiedName() = "React.Component" or
        access.getQualifiedName() = "React.PureComponent") or
      sup = DataFlow::moduleMember("react", "Component") or
      sup = DataFlow::moduleMember("react", "PureComponent") or
      sup.getAstNode() instanceof ReactComponent)
  }

  override Function getInstanceMethod(string name) {
    exists (MemberDefinition mem | mem = this.getMember(name) |
      result = mem.getInit() and
      not mem.isStatic() and
      not mem instanceof ConstructorDefinition
    )
  }

  override DataFlow::SourceNode getADirectPropsAccess() {
    result.(DataFlow::PropRef).accesses(ref(), "props") or
    result = DataFlow::parameterNode(getConstructor().getBody().getParameter(0))
  }

  override AbstractValue getAbstractComponent() {
    result = TAbstractInstance(TAbstractClass(this))
  }

  override DataFlow::SourceNode getComponentCreatorSource() {
    result = DataFlow::valueNode(this)
  }

  override DataFlow::SourceNode getACandidateStateSource() {
    result = ReactComponent.super.getACandidateStateSource() or
    result.flowsToExpr(getField("state").getInit())
  }

  override DataFlow::SourceNode getADefaultPropsSource() {
    exists (DataFlow::Node props |
      result.flowsTo(props) and
      DataFlow::valueNode(this).(DataFlow::SourceNode).hasPropertyWrite("defaultProps", props)
    )
  }

}

/**
 * A legacy React component implemented using `React.createClass` or `create-react-class`.
 */
class ES5Component extends ReactComponent, ObjectExpr {

  DataFlow::CallNode create;

  ES5Component() {
    (
      // React.createClass({...})
      create = react().getAMethodCall("createClass")
      or
      // require('create-react-class')({...})
      create = DataFlow::moduleImport("create-react-class").getACall()
    ) and
    create.getArgument(0).getALocalSource().asExpr() = this
  }

  override Function getInstanceMethod(string name) {
    result = getPropertyByName(name).getInit()
  }

  override DataFlow::SourceNode getADirectPropsAccess() {
    result.(DataFlow::PropRef).accesses(ref(), "props")
  }

  override AbstractValue getAbstractComponent() {
    result = TAbstractObjectLiteral(this)
  }

  override DataFlow::SourceNode getComponentCreatorSource() {
    result = create
  }

  override DataFlow::SourceNode getACandidateStateSource() {
    result = ReactComponent.super.getACandidateStateSource() or
    result.flowsToExpr(getInstanceMethod("getInitialState").getAReturnedExpr())
  }

  override DataFlow::SourceNode getADefaultPropsSource() {
    exists (Function f |
      f = getInstanceMethod("getDefaultProps") and
      result.flowsToExpr(f.getAReturnedExpr())
    )
  }

}

/**
 * A DOM element created by a React function.
 */
abstract class ReactElementDefinition extends DOM::ElementDefinition {

  override DOM::ElementDefinition getParent() {
    none()
  }

  /**
   * Gets the `props` argument of this definition.
   */
  abstract DataFlow::Node getProps();

}

/**
 * A DOM element created by the `React.createElement` function.
 */
private class CreateElementDefinition extends ReactElementDefinition {

  DataFlow::MethodCallNode call;

  CreateElementDefinition() {
    call.asExpr() = this and
    call = react().getAMethodCall("createElement")
  }

  override string getName() {
    call.getArgument(0).mayHaveStringValue(result)
  }

  override DataFlow::Node getProps() {
    result = call.getArgument(1)
  }

}

/**
 * A DOM element created by the (legacy) `React.createFactory` function.
 */
private class FactoryDefinition extends ReactElementDefinition {

  DataFlow::MethodCallNode factory;

  DataFlow::CallNode call;

  FactoryDefinition() {
    call.asExpr() = this and
    call = factory.getACall() and
    factory = react().getAMethodCall("createFactory")
  }

  override string getName() {
      factory.getArgument(0).mayHaveStringValue(result)
  }

  override DataFlow::Node getProps() {
    result = call.getArgument(0)
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

/**
 * A `JSXElement` that instantiates a `ReactComponent`.
 */
private class ReactJSXElement extends JSXElement {

  ReactComponent component;

  ReactJSXElement() {
    component.getComponentCreatorSource().flowsToExpr(getNameExpr())
  }

  /**
   * Gets the component this element instantiates.
   */
  ReactComponent getComponent() {
    result = component
  }
}