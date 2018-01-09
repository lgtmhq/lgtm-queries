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

import python

/* Parents */

/** Internal implementation class */
library class FunctionParent extends FunctionParent_ {

}

/** Internal implementation class */
library class ArgumentsParent extends ArgumentsParent_ {

}

/** Internal implementation class */
library class ExprListParent extends ExprListParent_ {

}

/** Internal implementation class */
library class ExprContextParent extends ExprContextParent_ {

}

/** Internal implementation class */
library class StmtListParent extends StmtListParent_ {

}

/** Internal implementation class */
library class StrListParent extends StrListParent_ {

}

/** Internal implementation class */
library class ExprParent extends ExprParent_ {

}

library class DictItem extends DictItem_, AstNode {

    string toString() {
        result = DictItem_.super.toString()
    }

    AstNode getAChildNode() { none() }

    Scope getScope() { none() }

}

/** A comprehension part, the 'for a in seq' part of  [ a * a for a in seq ] */
class Comprehension extends Comprehension_, AstNode {

    /** Gets the scope of this comprehension */
    Scope getScope() {
        /* Comprehensions exists only in Python 2 list comprehensions, so their scope is that of the list comp. */
        exists(ListComp l |
            this = l.getAGenerator() |
            result = l.getScope() 
        )
    }

    string toString() {
        result = "Comprehension"
    }

    Location getLocation() {
        result = Comprehension_.super.getLocation()
    } 

    AstNode getAChildNode() {
        result = this.getASubExpression()
    }

    Expr getASubExpression() {
        result = this.getIter() or
        result = this.getAnIf() or
        result = this.getTarget()
    }

}

class BytesOrStr extends BytesOrStr_ { 

}

/** Part of a string literal formed by implicit concatenation.
 * For example the string literal "abc" expressed in the source as `"a" "b" "c"`
 * would be composed of three `StringPart`s.
 * 
 */
class StringPart extends StringPart_, AstNode {

    Scope getScope() {
        exists(Bytes b | this = b.getAnImplicitlyConcatenatedPart() | result = b.getScope())
        or
        exists(Unicode u | this = u.getAnImplicitlyConcatenatedPart() | result = u.getScope())
    }

    AstNode getAChildNode() {
        none()
    }

    string toString() {
        result = StringPart_.super.toString()
    }

    Location getLocation() {
        result = StringPart_.super.getLocation()
    }

}

class StringPartList extends StringPartList_ {

}

