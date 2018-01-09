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
 * @name Template syntax in string literal
 * @description A string literal appears to use template syntax but is not quoted with backticks.
 * @kind problem
 * @problem.severity warning
 * @id js/template-syntax-in-string-literal
 * @precision high
 * @tags correctness
 */
 
import javascript

predicate isScope(ASTNode node) {
  exists (Scope scope | scope.getScopeElement() = node)
}

Scope getImmediatelyEnclosingScope(ASTNode node) {
  result.getScopeElement() = node
  or
  (not isScope(node) and getImmediatelyEnclosingScope(node.getParent()) = result)
}

predicate isInLocalScope(ASTNode node, Scope scope) {
  getImmediatelyEnclosingScope(node) = scope.getAnInnerScope*()
}

predicate isInScope(ASTNode node, Scope scope) {
  scope instanceof GlobalScope or isInLocalScope(node, scope)
}

 /** Extracts ${..} clauses from a string literal using an inexact regular expression.
  *
  * Breakdown of the sequence matched by the expression:
  * - any prefix and then "${"
  * - any amount of whitespace and simple unary operators
  * - name of the variable
  * - optionally: a character terminating the identifier token, followed by anything
  * - "}", followed by anything
  */
string getReferencedVariable(StringLiteral lit) {
  result = lit.getStringValue().regexpCapture(".*\\$\\{[\\s+\\-!]*([\\w\\p{L}$]+)([^\\w\\p{L}$].*)?\\}.*", 1)
}

/**
 * Holds if `obj` has a property for each template variable in `lit` and they occur as arguments to the same call.
 * This recognises a typical pattern in which template arguments are passed along with a string, for example:
 *
 *   output.emit('<a href="${url}">${name}$</a>',
 *        { url: url, name: name } );
 */
predicate providesTemplateVariablesFor(ObjectExpr obj, StringLiteral lit) {
  exists (CallExpr call | call.getAnArgument() = obj and call.getAnArgument() = lit) and
  forex (string name | getReferencedVariable(lit) = name | hasProperty(obj, name))
}

predicate hasProperty(ObjectExpr object, string name) {
  name = object.getAProperty().getName()
}

predicate usesTemplates(TopLevel topLevel) {
  exists (TemplateLiteral template | template.getTopLevel() = topLevel)
}

from StringLiteral lit, Variable v, Scope scope, string name, VarDecl decl
where variables(v, name, scope)
  and v.getADeclaration() = decl
  and decl.getTopLevel() = lit.getTopLevel()
  and getReferencedVariable(lit) = name
  and isInScope(lit, scope)
  and usesTemplates(lit.getTopLevel())
  and not exists (ObjectExpr obj | providesTemplateVariablesFor(obj, lit))
  and not lit.getStringValue() = "${" + name + "}"
select lit, "This string is not a template literal, but appears to reference the variable $@.", 
    decl, v.getName()
