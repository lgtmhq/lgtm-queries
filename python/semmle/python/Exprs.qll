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

import python

/** An expression */
class Expr extends Expr_, AstNode {

    /** Gets the scope of this expression */
    Scope getScope() {
        py_scopes(this, result)
    }

    string toString() {
        result = "Expression"
    }

    /** Gets the module in which this expression occurs */
    Module getEnclosingModule() {
        result = this.getScope().getEnclosingModule()
    }

    /** Whether this expression defines variable `v`
     * If doing dataflow, then consider using SsaVariable.getDefinition() for more precision. */
    predicate defines(Variable v) {
        this.getASubExpression+().defines(v)
    }

    /** Whether this expression may have a side effect (as determined purely from its syntax) */
    predicate hasSideEffects() {
        /* If an exception raised by this expression handled, count that as a side effect */
        this.getAFlowNode().getASuccessor().getNode() instanceof ExceptStmt
        or
        this.getASubExpression().hasSideEffects()
    }

    /** Whether this expression is a constant */
    predicate isConstant() {
        not this.isVariable()
    }

    private predicate isVariable() {
        this.hasSideEffects() or
        this instanceof Name or
        exists(Expr e | e = this.getASubExpression() and e.isVariable())
    }

    Location getLocation() {
        result = Expr_.super.getLocation()
    }

    /** Gets an immediate (non-nested) sub-expression of this expression */
    Expr getASubExpression() {
        none()
    }

    /** Use StrConst.getText() instead */
    deprecated string strValue() {
        none()
    }

    AstNode getAChildNode() {
        result = this.getASubExpression()
    }

    /** Gets what this expression might "refer-to". Performs a combination of localized (intra-procedural) points-to
     *  analysis and global module-level analysis. This points-to analysis favours precision over recall. It is highly
     *  precise, but may not provide information for a significant number of flow-nodes. 
     *  If the class is unimportant then use `refersTo(value)` or `refersTo(value, origin)` instead.
     * NOTE: For complex dataflow, involving multiple stages of points-to analysis, it may be more precise to use 
     * `ControlFlowNode.refersTo(...)` instead.
     */
    predicate refersTo(Object value, ClassObject cls, AstNode origin) {
        not py_special_objects(cls, "_semmle_unknown_type")
        and
        final_points_to(this.getAFlowNode(), value, cls, origin.getAFlowNode())
    }

    /** Whether this expression might "refer-to" to `value` which is from `origin` 
     * Unlike `this.refersTo(value, _, origin)`, this predicate includes results 
     * where the class cannot be inferred.
     */
    predicate refersTo(Object value, AstNode origin) {
        final_points_to(this.getAFlowNode(), value, _, origin.getAFlowNode())
    }

    /** Equivalent to `this.refersTo(value, _)` */
    predicate refersTo(Object value) {
        final_points_to(this.getAFlowNode(), value, _, _)
    }

}

/** An attribute expression, such as `value.attr` */
class Attribute extends Attribute_ {

    Expr getASubExpression() {
        result = this.getObject()
    }

    AttrNode getAFlowNode() { result = super.getAFlowNode() }

    string getName() {
        result = Attribute_.super.getAttr()
    }

    Expr getObject() {
        result = Attribute_.super.getValue()
    }

    /** Use getName() instead */
    deprecated string getAttr() {
        result = Attribute_.super.getAttr()
    }

    /** Use getObject() instead */
    deprecated Expr getValue() {
        result = Attribute_.super.getValue()
    }

}

/** A subscript expression, such as `value[slice]` */
class Subscript extends Subscript_ {

    Expr getASubExpression() {
        result = this.getIndex()
        or
        result = this.getObject()
    }

    Expr getObject() {
        result = Subscript_.super.getValue()
    }

    /** Use getObject() instead */
    deprecated Expr getValue() {
        result = Subscript_.super.getValue()
    }

    SubscriptNode getAFlowNode() { result = super.getAFlowNode() }
}

/** A call expression, such as `func(...)` */
class Call extends Call_ {

    Expr getASubExpression() {
        result = this.getAPositionalArg() or
        result = this.getAKeyword().getValue() or
        result = this.getFunc()
    }

    predicate hasSideEffects() {
        any()
    }

    string toString() {
        result = this.getFunc().toString() + "()"
    }

    CallNode getAFlowNode() { result = super.getAFlowNode() }

    /** Gets a tuple (*) argument of this class definition. */
    Expr getStarargs() {
        result = this.getAPositionalArg().(Starred).getValue()
    }

    /** Gets a dictionary (**) argument of this class definition. */
    Expr getKwargs() {
        result = this.getANamedArg().(DictUnpacking).getValue()
    }

    /* Backwards compatibility */

    /** Gets the nth keyword argument of this call expression, provided it is not preceded by a double-starred argument. 
     * This exists primarily for backwards compatibility. You are recommended to use
     * Call.getNamedArg(index) instead.
     * */
    Keyword getKeyword(int index) {
        result = this.getNamedArg(index) and not exists(DictUnpacking d, int lower | d = this.getNamedArg(lower) and lower < index)
    }

    /** Gets a keyword argument of this call expression, provided it is not preceded by a double-starred argument. 
     * This exists primarily for backwards compatibility. You are recommended to use
     * Call.getANamedArg() instead.
     * */
    Keyword getAKeyword() {
        result = this.getKeyword(_)
    }

    /** Gets the positional argument at `index`, provided it is not preceded by a starred argument.
     * This exists primarily for backwards compatibility. You are recommended to use
     * Call.getPositionalArg(index) instead.
     */
    Expr getArg(int index) {
        result = this.getPositionalArg(index) and
        not result instanceof Starred and
        not exists(Starred s, int lower | s = this.getPositionalArg(lower) and lower < index)
    }

    /** Gets a positional argument, provided it is not preceded by a starred argument.
     * This exists primarily for backwards compatibility. You are recommended to use
     * Call.getAPositionalArg() instead.
     */
    Expr getAnArg() {
        result = this.getArg(_)
    }

    AstNode getAChildNode() {
        result = this.getAPositionalArg() or
        result = this.getANamedArg() or
        result = this.getFunc()
    }

    /** Gets the name of a named argument, including those passed in dict literals. */
    string getANamedArgumentName() {
        result = this.getAKeyword().getArg()
        or
        result = this.getKwargs().(Dict).getAKey().(StrConst).getText()
    }

}

/** A conditional expression such as, `body if test else orelse` */
class IfExp extends IfExp_ {

    Expr getASubExpression() {
        result = this.getTest() or result = this.getBody() or result = this.getOrelse()
    }

    IfExprNode getAFlowNode() { result = super.getAFlowNode() }
}

/** A starred expression, such as the `*rest` in the assignment `first, *rest = seq` */
class Starred extends Starred_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

}


/** A yield expression, such as `yield value` */
class Yield extends Yield_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

    predicate hasSideEffects() {
        any()
    }

}

/** A yield expression, such as `yield from value` */
class YieldFrom extends YieldFrom_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

    predicate hasSideEffects() {
        any()
    }

}

/** A repr (backticks) expression, such as `` `value` `` */
class Repr extends Repr_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

    predicate hasSideEffects() {
        any()
    }

}

/* Constants */

/** A bytes constant, such as `b'ascii'`. Note that unadorned string constants such as
   `"hello"` are treated as Bytes for Python2, but Unicode for Python3. */
class Bytes extends StrConst {
  
    Bytes() {
        not this.isUnicode()
    }

    Object getLiteralObject() {
        py_cobjecttypes(result, theBytesType()) and
        py_cobjectnames(result, this.quotedString())
    }
    
    /** The extractor puts quotes into the name of each string (to prevent "0" clashing with 0).
     * The following predicate help us match up a string/byte literals in the source
     * which the equivalent object.
     */
    private string quotedString() {
        exists(string b_unquoted |
            b_unquoted = this.getS() |
            result = "b'" + b_unquoted + "'"
        ) 
    }

}

/** An ellipsis expression, such as `...` */
class Ellipsis extends Ellipsis_ {

    Expr getASubExpression() {
        none()
    }

}

/** Immutable literal expressions (except tuples).
 *  Consists of string (both unicode and byte) literals
 *  and numeric literals.
 */
abstract class ImmutableLiteral extends Expr {
 
    abstract Object getLiteralObject();

    abstract boolean booleanValue();

}

/** A numerical constant expression, such as `7` or `4.2` */
abstract class Num extends Num_, ImmutableLiteral {

    Expr getASubExpression() {
        none()
    }

    /* We want to declare this abstract, but currently we cannot. */
    string toString() {
        none() 
    }

}

/** An integer numeric constant, such as `7` or `0x9` */
class IntegerLiteral extends Num {

    IntegerLiteral() {
        not this instanceof FloatLiteral and not this instanceof ImaginaryLiteral
    }

    /** Gets the (integer) value of this constant. Will not return a result if the value does not fit into
        a 32 bit signed value */
    int getValue() {
        result = this.getN().toInt()
    }

    string toString() {
        result = "IntegerLiteral"
    }

    Object getLiteralObject() {
        py_cobjecttypes(result, theIntType()) and py_cobjectnames(result, this.getN())
        or
        py_cobjecttypes(result, theLongType()) and py_cobjectnames(result, this.getN())   
    }

    boolean booleanValue() {
        this.getValue() = 0 and result = false
        or
        this.getValue() != 0 and result = true
    }

}

/** A floating point numeric constant, such as `0.4` or `4e3` */
class FloatLiteral extends Num {

    FloatLiteral() {
        not this instanceof ImaginaryLiteral and
        exists(string n | n = this.getN() | n.charAt(_) = "." or n.charAt(_) = "e" or n.charAt(_) = "E")
    }

    float getValue() {
        result = this.getN().toFloat()
    }

    string toString() {
        result = "FloatLiteral"
    }

    Object getLiteralObject() {
        py_cobjecttypes(result, theFloatType()) and py_cobjectnames(result, this.getN())   
    }

    boolean booleanValue() {
        this.getValue() = 0.0 and result = false
        or
        // In QL 0.0 != -0.0
        this.getValue() = -0.0 and result = false
        or
        this.getValue() != 0.0 and this.getValue() != -0.0 and result = true
    }

}

/** An imaginary numeric constant, such as `3j` */
class ImaginaryLiteral extends Num {

    ImaginaryLiteral() {
        exists(string n | n = this.getN() | n.charAt(_) = "j")
    }

    /** Gets the value of this constant as a floating point value */
    float getValue() {
        exists(string s, int j | s = this.getN() and s.charAt(j) = "j" |
                       result = s.prefix(j).toFloat())
    }

    string toString() {
        result = "ImaginaryLiteral"
    }

    Object getLiteralObject() {
        py_cobjecttypes(result, theComplexType()) and py_cobjectnames(result, this.getN())   
    }

    boolean booleanValue() {
        this.getValue() = 0.0 and result = false
        or
        // In QL 0.0 != -0.0
        this.getValue() = -0.0 and result = false
        or
        this.getValue() != 0.0 and this.getValue() != -0.0 and result = true
    }

}

/** A unicode string expression, such as `u"\u20ac"`. Note that unadorned string constants such as
   "hello" are treated as Bytes for Python2, but Unicode for Python3. */
class Unicode extends StrConst {
  
    Unicode() {
        this.isUnicode()
    }

    Object getLiteralObject() {
        py_cobjecttypes(result, theUnicodeType()) and
        py_cobjectnames(result, this.quotedString())
    }
    
    /** The extractor puts quotes into the name of each string (to prevent "0" clashing with 0).
     * The following predicate help us match up a string/byte literals in the source
     * which the equivalent object.
     */
    string quotedString() {
        exists(string u_unquoted |
            u_unquoted = this.getS() |
            result = "u'" + u_unquoted + "'"
        ) 
    }
    
}


/* Compound Values */

/** A dictionary expression, such as `{'key':'value'}` */
class Dict extends Dict_ {

    /** Gets the value of an item of this dict display */
    Expr getAValue() {
        result = this.getAnItem().(DictDisplayItem).getValue()
    }

    /** Gets the key of an item of this dict display, for those items that have keys
     * E.g, in {'a':1, **b} this returns only 'a'
     */
     Expr getAKey() {
        result = this.getAnItem().(KeyValuePair).getKey()
    }

    Expr getASubExpression() {
        result = this.getAValue() or result = this.getAKey()
    }

}

/** A list expression, such as `[ 1, 3, 5, 7, 9 ]` */
class List extends List_ {

    Expr getASubExpression() {
        result = this.getAnElt()
    }

}

/** A set expression such as `{ 1, 3, 5, 7, 9 }` */
class Set extends Set_ {

    Expr getASubExpression() {
        result = this.getAnElt()
    }

}

class PlaceHolder extends PlaceHolder_ {

    string getId() {
        result = this.getVariable().getId()
    }

    Expr getASubExpression() {
        none()
    }

    string toString() {
        result = "$" + this.getId()
    }

    NameNode getAFlowNode() { result = super.getAFlowNode() }
}

/** A tuple expression such as `( 1, 3, 5, 7, 9 )` */
class Tuple extends Tuple_ {

    Expr getASubExpression() {
        result = this.getAnElt()
    }

}

/** A  (plain variable) name expression, such as `var`.
 * `None`, `True` and `False` are excluded.
 */
class Name extends Name_ {

    string getId() {
        result = this.getVariable().getId()
    }

    /** Whether this expression is a definition */
    predicate isDefinition() {
        py_expr_contexts(_, 5, this) or
        /* Treat Param as a definition (which it is) */
        py_expr_contexts(_, 4, this) or
        /* The target in an augmented assignment is also a definition (and a use) */
        exists(AugAssign aa | aa.getTarget() = this)
    }

    /** Whether this expression defines variable `v`
     * If doing dataflow, then consider using SsaVariable.getDefinition() for more precision. */
    predicate defines(Variable v) {
        this.isDefinition()
        and
        v = this.getVariable()
    }

    /** Whether this expression is a definition */
    predicate isDeletion() {
        py_expr_contexts(_, 2, this)
    }

    /** Whether this expression deletes variable `v`.
     * If doing dataflow, then consider using SsaVariable.getDefinition() for more precision. */
    predicate deletes(Variable v) {
        this.isDeletion()
        and
        v = this.getVariable()
    }

    /** Whether this expression is a use */
    predicate isUse() {
        py_expr_contexts(_, 3, this)
    }

    /** Whether this expression is a use of variable `v`
     * If doing dataflow, then consider using SsaVariable.getAUse() for more precision. */
    predicate uses(Variable v) {
        this.isUse()
        and
        v = this.getVariable()
    }
    
    

    predicate isConstant() {
        none()
    }

    Expr getASubExpression() {
        none()
    }

    string toString() {
        result = this.getId()
    }

    NameNode getAFlowNode() { result = super.getAFlowNode() }

    predicate isArtificial() {
        /* Artificial variable names in comprehensions all start with "." */
        this.getId().charAt(0) = "."
    }

}

class Filter extends Filter_ {

    Expr getASubExpression() {
        result = this.getFilter()
        or
        result = this.getValue()
    }

}


/** A slice. E.g `0:1` in the expression `x[0:1]` */
class Slice extends Slice_ {

    Expr getASubExpression() {
        result = this.getStart() or
        result = this.getStop() or
        result = this.getStep()
    }

}

/** A string constant. */
class StrConst extends Str_, ImmutableLiteral {

    predicate isUnicode() {
        this.getPrefix().charAt(_) = "u"
        or
        this.getPrefix().charAt(_) = "U"
        or
        not this.getPrefix().charAt(_) = "b" and major_version() = 3
        or
        not this.getPrefix().charAt(_) = "b" and this.getEnclosingModule().hasFromFuture("unicode_literals")
    }

    override
    string strValue() {
        result = this.getS()
    }

    Expr getASubExpression() {
        none()
    }

    AstNode getAChildNode() {
        result = this.getAnImplicitlyConcatenatedPart()
    }

    /** Gets the text of this str constant */
    string getText() {
        result = this.getS()
    }

    /** Whether this is a docstring */
    predicate isDocString() {
        exists(Scope s | s.getDocString() = this)
    }

    boolean booleanValue() {
        this.getText() = "" and result = false
        or
        this.getText() != "" and result = true
    }

    Object getLiteralObject() { none() }

}

private predicate name_consts(Name_ n, string id) {
     exists(Variable v |
        py_variables(v, n) and id = v.getId() |
        id = "True" or id = "False" or id = "None"
    )
}

/** A named constant, one of `None`, `True` or `False` */
abstract class NameConstant extends Name, ImmutableLiteral {

    NameConstant() {
        name_consts(this, _)
    }

    Expr getASubExpression() {
        none()
    }

    string toString() {
        name_consts(this, result)
    }

    predicate isConstant() {
        any()
    }

    deprecated predicate isDefinition() {
        Name.super.isDefinition()
    }

    deprecated predicate defines(Variable v) { none() }

    deprecated predicate deletes(Variable v) { none() }

    NameConstantNode getAFlowNode() { result = Name.super.getAFlowNode() }

    predicate isArtificial() {
        none()
    }

}

/** A boolean named constant, either `True` or `False` */
abstract class BooleanLiteral extends NameConstant {

}

/** The boolean named constant `True` */
class True extends BooleanLiteral {

    True() {
        name_consts(this, "True")
    }

    Object getLiteralObject() {
        name_consts(this, "True") and result = theTrueObject() 
    }

    boolean booleanValue() {
        result = true 
    }

}

/** The boolean named constant `False` */
class False extends BooleanLiteral {

    False() {
        name_consts(this, "False")
    }

    Object getLiteralObject() {
        name_consts(this, "False") and result = theFalseObject()
    }

    boolean booleanValue() {
        result = false
    }

}

/** `None` */
class None extends NameConstant {

    None() {
        name_consts(this, "None")
    }

    Object getLiteralObject() {
        name_consts(this, "None") and result = theNoneObject()
    }

    boolean booleanValue() {
        result = false
    }

}

/** An await expression such as `await coro`. */
class Await extends Await_ {

    Expr getASubExpression() {
        result = this.getValue()
    }

}

/** A formatted string literal expression, such as `f'hello {world!s}'` */
class Fstring extends Fstring_ {

    Expr getASubExpression() {
        result = this.getAValue()
    }

}

/** A formatted value (within a formatted string literal).
 * For example, in the string `f'hello {world!s}'` the formatted value is `world!s`.
 */
class FormattedValue extends FormattedValue_ {

    Expr getASubExpression() {
        result = this.getValue() or
        result = this.getFormatSpec()
    }


}

/* Expression Contexts */

/** A context in which an expression used */
class ExprContext extends ExprContext_ {

}

/** Load context, the context of var in len(var) */
class Load extends Load_ {

}

/** Store context, the context of var in var = 0 */
class Store extends Store_ {

}

/** Delete context, the context of var in del var */
class Del extends Del_ {

}

/** This is an artifact of the Python grammar which includes an AugLoad context, even though it is never used. */
library class AugLoad extends AugLoad_ {

}

/** Augmented store context, the context of var in var += 1 */
class AugStore extends AugStore_ {

}

/** Parameter context, the context of var in def f(var): pass */
class Param extends Param_ {

}


