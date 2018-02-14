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
 * @name Unbound event handler receiver
 * @description Invoking an event handler method as a function can cause a runtime error.
 * @kind problem
 * @problem.severity error
 * @id js/unbound-event-handler-receiver
 * @tags correctness
 * @precision high
 */
import javascript

/**
 * Holds if the receiver of `method` is bound in a method of its class.
 */
private predicate isBoundInMethod(MethodDeclaration method) {
  exists (PropWriteNode reassign, MethodDeclaration bindingMethod |
    bindingMethod = method.getDeclaringType().(ClassDefinition).getAMethod() and
    not bindingMethod.isStatic() and
    reassign.(Expr).getEnclosingFunction() = bindingMethod.getBody() and
    // this.<methodName> = <expr>.bind(...)
    reassign.getBase() instanceof ThisExpr and
    reassign.getPropertyName() = method.getName() and
    reassign.getRhs().(MethodCallExpr).getMethodName() = "bind"
  )
}

/**
 * Gets an event handler attribute (onClick, onTouch, ...).
 */
private DOM::AttributeDefinition getAnEventHandlerAttribute() {
  exists (ReactComponent c, JSXNode rendered, string attributeName |
      rendered = c.getRenderMethod().getAReturnedExpr().(DataFlowNode).getALocalSource() and
      result = rendered.getABodyElement*().(JSXElement).getAttributeByName(attributeName) and
      attributeName.regexpMatch("on[A-Z][a-zA-Z]+") // camelCased with 'on'-prefix
  )
}

from MethodDeclaration callback, DOM::AttributeDefinition attribute, ThisExpr unbound
where
      attribute = getAnEventHandlerAttribute() and
      DataFlow::valueNode(attribute.getValueNode()).(AnalyzedFlowNode).getAValue().(AbstractFunction).getFunction() = callback.getBody() and
      unbound.getBinder() = callback.getBody() and
      not isBoundInMethod(callback)
select attribute, "The receiver of this event handler call is unbound, `$@` will be `undefined` in the call to $@", unbound, "this", callback, callback.getName()
