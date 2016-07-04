// Copyright 2016 Semmle Ltd.
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

library class Add_ extends @py_Add, Operator {

    string toString() {
        result = "Add"
    }

}

library class And_ extends @py_And, Boolop {

    string toString() {
        result = "And"
    }

}

library class Assert_ extends @py_Assert, Stmt {


    /** Gets the value being tested of this assert statement. */
    Expr getTest() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the failure message of this assert statement. */
    Expr getMsg() {
        py_exprs(result, _, this, 2)
    }

    string toString() {
        result = "Assert"
    }

}

library class Assign_ extends @py_Assign, Stmt {


    /** Gets the value of this assignment statement. */
    Expr getValue() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the targets of this assignment statement. */
    ExprList getTargets() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth target of this assignment statement. */
    Expr getTarget(int index) {
        result = this.getTargets().getItem(index)
    }

    /** Gets a target of this assignment statement. */
    Expr getATarget() {
        result = this.getTargets().getAnItem()
    }

    string toString() {
        result = "Assign"
    }

}

library class Attribute_ extends @py_Attribute, Expr {


    /** Gets the object of this attribute expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the attribute name of this attribute expression. */
    string getAttr() {
        py_strs(result, this, 3)
    }


    /** Gets the context of this attribute expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    string toString() {
        result = "Attribute"
    }

}

library class AugAssign_ extends @py_AugAssign, Stmt {


    /** Gets the operation of this augmented assignment statement. */
    Expr getOperation() {
        py_exprs(result, _, this, 1)
    }

    string toString() {
        result = "AugAssign"
    }

}

library class AugLoad_ extends @py_AugLoad, ExprContext {

    string toString() {
        result = "AugLoad"
    }

}

library class AugStore_ extends @py_AugStore, ExprContext {

    string toString() {
        result = "AugStore"
    }

}

library class BinaryExpr_ extends @py_BinaryExpr, Expr {


    /** Gets the left sub-expression of this binary expression. */
    Expr getLeft() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the operator of this binary expression. */
    Operator getOp() {
        py_operators(result, _, this)
    }


    /** Gets the right sub-expression of this binary expression. */
    Expr getRight() {
        py_exprs(result, _, this, 4)
    }

    ExprParent getParent() {
        py_exprs(this, _, result, _)
    }

    string toString() {
        result = "BinaryExpr"
    }

}

library class BitAnd_ extends @py_BitAnd, Operator {

    string toString() {
        result = "BitAnd"
    }

}

library class BitOr_ extends @py_BitOr, Operator {

    string toString() {
        result = "BitOr"
    }

}

library class BitXor_ extends @py_BitXor, Operator {

    string toString() {
        result = "BitXor"
    }

}

library class BoolExpr_ extends @py_BoolExpr, Expr {


    /** Gets the operator of this boolean expression. */
    Boolop getOp() {
        py_boolops(result, _, this)
    }


    /** Gets the sub-expressions of this boolean expression. */
    ExprList getValues() {
        py_expr_lists(result, this, 3)
    }


    /** Gets the nth sub-expression of this boolean expression. */
    Expr getValue(int index) {
        result = this.getValues().getItem(index)
    }

    /** Gets a sub-expression of this boolean expression. */
    Expr getAValue() {
        result = this.getValues().getAnItem()
    }

    string toString() {
        result = "BoolExpr"
    }

}

library class Break_ extends @py_Break, Stmt {

    string toString() {
        result = "Break"
    }

}

library class Bytes_ extends @py_Bytes, Expr {


    /** Gets the value of this bytes expression. */
    string getS() {
        py_bytes(result, this, 2)
    }


    /** Gets the prefix of this bytes expression. */
    string getPrefix() {
        py_bytes(result, this, 3)
    }


    /** Gets the implicitly_concatenated_parts of this bytes expression. */
    StringPartList getImplicitlyConcatenatedParts() {
        py_StringPart_lists(result, this)
    }


    /** Gets the nth implicitly_concatenated_part of this bytes expression. */
    StringPart getImplicitlyConcatenatedPart(int index) {
        result = this.getImplicitlyConcatenatedParts().getItem(index)
    }

    /** Gets an implicitly_concatenated_part of this bytes expression. */
    StringPart getAnImplicitlyConcatenatedPart() {
        result = this.getImplicitlyConcatenatedParts().getAnItem()
    }

    string toString() {
        result = "Bytes"
    }

}

library class BytesOrStr_ extends @py_Bytes_or_Str {

    string toString() {
        result = "BytesOrStr"
    }

}

library class Call_ extends @py_Call, Expr {


    /** Gets the callable of this call expression. */
    Expr getFunc() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the arguments of this call expression. */
    ExprList getArgs() {
        py_expr_lists(result, this, 3)
    }


    /** Gets the nth argument of this call expression. */
    Expr getArg(int index) {
        result = this.getArgs().getItem(index)
    }

    /** Gets an argument of this call expression. */
    Expr getAnArg() {
        result = this.getArgs().getAnItem()
    }


    /** Gets the keyword arguments of this call expression. */
    KeywordList getKeywords() {
        py_keyword_lists(result, this)
    }


    /** Gets the nth keyword argument of this call expression. */
    Keyword getKeyword(int index) {
        result = this.getKeywords().getItem(index)
    }

    /** Gets a keyword argument of this call expression. */
    Keyword getAKeyword() {
        result = this.getKeywords().getAnItem()
    }


    /** Gets the tuple (*) argument of this call expression. */
    Expr getStarargs() {
        py_exprs(result, _, this, 5)
    }


    /** Gets the dictionary (**) argument of this call expression. */
    Expr getKwargs() {
        py_exprs(result, _, this, 6)
    }

    string toString() {
        result = "Call"
    }

}

library class Class_ extends @py_Class {


    /** Gets the name of this class. */
    string getName() {
        py_strs(result, this, 0)
    }


    /** Gets the body of this class. */
    StmtList getBody() {
        py_stmt_lists(result, this, 1)
    }


    /** Gets the nth statement of this class. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this class. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }

    ClassExpr getParent() {
        py_Classes(this, result)
    }

    string toString() {
        result = "Class"
    }

}

library class ClassExpr_ extends @py_ClassExpr, Expr {


    /** Gets the name of this class definition. */
    string getName() {
        py_strs(result, this, 2)
    }


    /** Gets the bases of this class definition. */
    ExprList getBases() {
        py_expr_lists(result, this, 3)
    }


    /** Gets the nth base of this class definition. */
    Expr getBase(int index) {
        result = this.getBases().getItem(index)
    }

    /** Gets a base of this class definition. */
    Expr getABase() {
        result = this.getBases().getAnItem()
    }


    /** Gets the keyword arguments of this class definition. */
    KeywordList getKeywords() {
        py_keyword_lists(result, this)
    }


    /** Gets the nth keyword argument of this class definition. */
    Keyword getKeyword(int index) {
        result = this.getKeywords().getItem(index)
    }

    /** Gets a keyword argument of this class definition. */
    Keyword getAKeyword() {
        result = this.getKeywords().getAnItem()
    }


    /** Gets the tuple (*) argument of this class definition. */
    Expr getStarargs() {
        py_exprs(result, _, this, 5)
    }


    /** Gets the dictionary (**) argument of this class definition. */
    Expr getKwargs() {
        py_exprs(result, _, this, 6)
    }


    /** Gets the class scope of this class definition. */
    Class getInnerScope() {
        py_Classes(result, this)
    }

    string toString() {
        result = "ClassExpr"
    }

}

library class Compare_ extends @py_Compare, Expr {


    /** Gets the left sub-expression of this compare expression. */
    Expr getLeft() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the comparison operators of this compare expression. */
    CmpopList getOps() {
        py_cmpop_lists(result, this)
    }


    /** Gets the nth comparison operator of this compare expression. */
    Cmpop getOp(int index) {
        result = this.getOps().getItem(index)
    }

    /** Gets a comparison operator of this compare expression. */
    Cmpop getAnOp() {
        result = this.getOps().getAnItem()
    }


    /** Gets the right sub-expressions of this compare expression. */
    ExprList getComparators() {
        py_expr_lists(result, this, 4)
    }


    /** Gets the nth right sub-expression of this compare expression. */
    Expr getComparator(int index) {
        result = this.getComparators().getItem(index)
    }

    /** Gets a right sub-expression of this compare expression. */
    Expr getAComparator() {
        result = this.getComparators().getAnItem()
    }

    string toString() {
        result = "Compare"
    }

}

library class Continue_ extends @py_Continue, Stmt {

    string toString() {
        result = "Continue"
    }

}

library class Del_ extends @py_Del, ExprContext {

    string toString() {
        result = "Del"
    }

}

library class Delete_ extends @py_Delete, Stmt {


    /** Gets the targets of this delete statement. */
    ExprList getTargets() {
        py_expr_lists(result, this, 1)
    }


    /** Gets the nth target of this delete statement. */
    Expr getTarget(int index) {
        result = this.getTargets().getItem(index)
    }

    /** Gets a target of this delete statement. */
    Expr getATarget() {
        result = this.getTargets().getAnItem()
    }

    string toString() {
        result = "Delete"
    }

}

library class Dict_ extends @py_Dict, Expr {


    /** Gets the keys of this dictionary expression. */
    ExprList getKeys() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth key of this dictionary expression. */
    Expr getKey(int index) {
        result = this.getKeys().getItem(index)
    }

    /** Gets a key of this dictionary expression. */
    Expr getAKey() {
        result = this.getKeys().getAnItem()
    }


    /** Gets the values of this dictionary expression. */
    ExprList getValues() {
        py_expr_lists(result, this, 3)
    }


    /** Gets the nth value of this dictionary expression. */
    Expr getValue(int index) {
        result = this.getValues().getItem(index)
    }

    /** Gets a value of this dictionary expression. */
    Expr getAValue() {
        result = this.getValues().getAnItem()
    }

    string toString() {
        result = "Dict"
    }

}

library class DictComp_ extends @py_DictComp, Expr {


    /** Gets the implementation of this dictionary comprehension. */
    Function getFunction() {
        py_Functions(result, this)
    }


    /** Gets the iterable of this dictionary comprehension. */
    Expr getIterable() {
        py_exprs(result, _, this, 3)
    }

    string toString() {
        result = "DictComp"
    }

}

library class Div_ extends @py_Div, Operator {

    string toString() {
        result = "Div"
    }

}

library class Ellipsis_ extends @py_Ellipsis, Expr {

    string toString() {
        result = "Ellipsis"
    }

}

library class Eq_ extends @py_Eq, Cmpop {

    string toString() {
        result = "Eq"
    }

}

library class ExceptStmt_ extends @py_ExceptStmt, Stmt {


    /** Gets the type of this except block. */
    Expr getType() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the name of this except block. */
    Expr getName() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the body of this except block. */
    StmtList getBody() {
        py_stmt_lists(result, this, 3)
    }


    /** Gets the nth statement of this except block. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this except block. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }

    string toString() {
        result = "ExceptStmt"
    }

}

library class Exec_ extends @py_Exec, Stmt {


    /** Gets the body of this exec statement. */
    Expr getBody() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the globals of this exec statement. */
    Expr getGlobals() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the locals of this exec statement. */
    Expr getLocals() {
        py_exprs(result, _, this, 3)
    }

    string toString() {
        result = "Exec"
    }

}

library class ExprStmt_ extends @py_Expr_stmt, Stmt {


    /** Gets the value of this expr statement. */
    Expr getValue() {
        py_exprs(result, _, this, 1)
    }

    string toString() {
        result = "ExprStmt"
    }

}

library class Filter_ extends @py_Filter, Expr {


    /** Gets the filtered value of this template filter expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the filter of this template filter expression. */
    Expr getFilter() {
        py_exprs(result, _, this, 3)
    }

    string toString() {
        result = "Filter"
    }

}

library class FloorDiv_ extends @py_FloorDiv, Operator {

    string toString() {
        result = "FloorDiv"
    }

}

library class For_ extends @py_For, Stmt {


    /** Gets the target of this for statement. */
    Expr getTarget() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the iterable of this for statement. */
    Expr getIter() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the body of this for statement. */
    StmtList getBody() {
        py_stmt_lists(result, this, 3)
    }


    /** Gets the nth statement of this for statement. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this for statement. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }


    /** Gets the else block of this for statement. */
    StmtList getOrelse() {
        py_stmt_lists(result, this, 4)
    }


    /** Gets the nth else statement of this for statement. */
    Stmt getOrelse(int index) {
        result = this.getOrelse().getItem(index)
    }

    /** Gets an else statement of this for statement. */
    Stmt getAnOrelse() {
        result = this.getOrelse().getAnItem()
    }

    string toString() {
        result = "For"
    }

}

library class Function_ extends @py_Function {


    /** Gets the name of this function. */
    string getName() {
        py_strs(result, this, 0)
    }


    /** Gets the positional parameter list of this function. */
    ParameterList getArgs() {
        py_parameter_lists(result, this)
    }


    /** Gets the nth positional parameter of this function. */
    Parameter getArg(int index) {
        result = this.getArgs().getItem(index)
    }

    /** Gets a positional parameter of this function. */
    Parameter getAnArg() {
        result = this.getArgs().getAnItem()
    }


    /** Gets the tuple (*) parameter of this function. */
    Expr getVararg() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the keyword-only parameter list of this function. */
    ExprList getKwonlyargs() {
        py_expr_lists(result, this, 3)
    }


    /** Gets the nth keyword-only parameter of this function. */
    Expr getKwonlyarg(int index) {
        result = this.getKwonlyargs().getItem(index)
    }

    /** Gets a keyword-only parameter of this function. */
    Expr getAKwonlyarg() {
        result = this.getKwonlyargs().getAnItem()
    }


    /** Gets the dictionary (**) parameter of this function. */
    Expr getKwarg() {
        py_exprs(result, _, this, 4)
    }


    /** Gets the body of this function. */
    StmtList getBody() {
        py_stmt_lists(result, this, 5)
    }


    /** Gets the nth statement of this function. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this function. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }

    FunctionParent getParent() {
        py_Functions(this, result)
    }

    string toString() {
        result = "Function"
    }

}

library class FunctionExpr_ extends @py_FunctionExpr, Expr {


    /** Gets the name of this function definition. */
    string getName() {
        py_strs(result, this, 2)
    }


    /** Gets the parameters of this function definition. */
    Arguments getArgs() {
        py_arguments(result, this)
    }


    /** Gets the return annotation of this function definition. */
    Expr getReturns() {
        py_exprs(result, _, this, 4)
    }


    /** Gets the function scope of this function definition. */
    Function getInnerScope() {
        py_Functions(result, this)
    }

    string toString() {
        result = "FunctionExpr"
    }

}

library class FunctionParent_ extends @py_Function_parent {

    string toString() {
        result = "FunctionParent"
    }

}

library class GeneratorExp_ extends @py_GeneratorExp, Expr {


    /** Gets the implementation of this generator expression. */
    Function getFunction() {
        py_Functions(result, this)
    }


    /** Gets the iterable of this generator expression. */
    Expr getIterable() {
        py_exprs(result, _, this, 3)
    }

    string toString() {
        result = "GeneratorExp"
    }

}

library class Global_ extends @py_Global, Stmt {


    /** Gets the names of this global statement. */
    StringList getNames() {
        py_str_lists(result, this)
    }


    /** Gets the nth name of this global statement. */
    string getName(int index) {
        result = this.getNames().getItem(index)
    }

    /** Gets a name of this global statement. */
    string getAName() {
        result = this.getNames().getAnItem()
    }

    string toString() {
        result = "Global"
    }

}

library class Gt_ extends @py_Gt, Cmpop {

    string toString() {
        result = "Gt"
    }

}

library class GtE_ extends @py_GtE, Cmpop {

    string toString() {
        result = "GtE"
    }

}

library class If_ extends @py_If, Stmt {


    /** Gets the test of this if statement. */
    Expr getTest() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the if-true block of this if statement. */
    StmtList getBody() {
        py_stmt_lists(result, this, 2)
    }


    /** Gets the nth if-true statement of this if statement. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets an if-true statement of this if statement. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }


    /** Gets the if-false block of this if statement. */
    StmtList getOrelse() {
        py_stmt_lists(result, this, 3)
    }


    /** Gets the nth if-false statement of this if statement. */
    Stmt getOrelse(int index) {
        result = this.getOrelse().getItem(index)
    }

    /** Gets an if-false statement of this if statement. */
    Stmt getAnOrelse() {
        result = this.getOrelse().getAnItem()
    }

    string toString() {
        result = "If"
    }

}

library class IfExp_ extends @py_IfExp, Expr {


    /** Gets the test of this if expression. */
    Expr getTest() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the if-true expression of this if expression. */
    Expr getBody() {
        py_exprs(result, _, this, 3)
    }


    /** Gets the if-false expression of this if expression. */
    Expr getOrelse() {
        py_exprs(result, _, this, 4)
    }

    string toString() {
        result = "IfExp"
    }

}

library class Import_ extends @py_Import, Stmt {


    /** Gets the alias list of this import statement. */
    AliasList getNames() {
        py_alias_lists(result, this)
    }


    /** Gets the nth alias of this import statement. */
    Alias getName(int index) {
        result = this.getNames().getItem(index)
    }

    /** Gets an alias of this import statement. */
    Alias getAName() {
        result = this.getNames().getAnItem()
    }

    string toString() {
        result = "Import"
    }

}

library class ImportExpr_ extends @py_ImportExpr, Expr {


    /** Gets the level of this import expression. */
    int getLevel() {
        py_ints(result, this)
    }


    /** Gets the name of this import expression. */
    string getName() {
        py_strs(result, this, 3)
    }


    /** Whether the top level property of this import expression is true. */
    predicate isTop() {
        py_bools(this, 4)
    }

    string toString() {
        result = "ImportExpr"
    }

}

library class ImportStar_ extends @py_ImportStar, Stmt {


    /** Gets the module of this import * statement. */
    Expr getModule() {
        py_exprs(result, _, this, 1)
    }

    string toString() {
        result = "ImportStar"
    }

}

library class ImportMember_ extends @py_ImportMember, Expr {


    /** Gets the module of this from import. */
    Expr getModule() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the name of this from import. */
    string getName() {
        py_strs(result, this, 3)
    }

    string toString() {
        result = "ImportMember"
    }

}

library class In_ extends @py_In, Cmpop {

    string toString() {
        result = "In"
    }

}

library class Invert_ extends @py_Invert, Unaryop {

    string toString() {
        result = "Invert"
    }

}

library class Is_ extends @py_Is, Cmpop {

    string toString() {
        result = "Is"
    }

}

library class IsNot_ extends @py_IsNot, Cmpop {

    string toString() {
        result = "IsNot"
    }

}

library class LShift_ extends @py_LShift, Operator {

    string toString() {
        result = "LShift"
    }

}

library class Lambda_ extends @py_Lambda, Expr {


    /** Gets the arguments of this lambda expression. */
    Arguments getArgs() {
        py_arguments(result, this)
    }


    /** Gets the function scope of this lambda expression. */
    Function getInnerScope() {
        py_Functions(result, this)
    }

    string toString() {
        result = "Lambda"
    }

}

library class List_ extends @py_List, Expr {


    /** Gets the element list of this list expression. */
    ExprList getElts() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth element of this list expression. */
    Expr getElt(int index) {
        result = this.getElts().getItem(index)
    }

    /** Gets an element of this list expression. */
    Expr getAnElt() {
        result = this.getElts().getAnItem()
    }


    /** Gets the context of this list expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    string toString() {
        result = "List"
    }

}

library class ListComp_ extends @py_ListComp, Expr {


    /** Gets the implementation of this list comprehension. */
    Function getFunction() {
        py_Functions(result, this)
    }


    /** Gets the iterable of this list comprehension. */
    Expr getIterable() {
        py_exprs(result, _, this, 3)
    }


    /** Gets the generators of this list comprehension. */
    ComprehensionList getGenerators() {
        py_comprehension_lists(result, this)
    }


    /** Gets the nth generator of this list comprehension. */
    Comprehension getGenerator(int index) {
        result = this.getGenerators().getItem(index)
    }

    /** Gets a generator of this list comprehension. */
    Comprehension getAGenerator() {
        result = this.getGenerators().getAnItem()
    }


    /** Gets the elements of this list comprehension. */
    Expr getElt() {
        py_exprs(result, _, this, 5)
    }

    string toString() {
        result = "ListComp"
    }

}

library class Load_ extends @py_Load, ExprContext {

    string toString() {
        result = "Load"
    }

}

library class Lt_ extends @py_Lt, Cmpop {

    string toString() {
        result = "Lt"
    }

}

library class LtE_ extends @py_LtE, Cmpop {

    string toString() {
        result = "LtE"
    }

}

library class Mod_ extends @py_Mod, Operator {

    string toString() {
        result = "Mod"
    }

}

library class Module_ extends @py_Module {


    /** Gets the name of this module. */
    string getName() {
        py_strs(result, this, 0)
    }


    /** Gets the hash (not populated) of this module. */
    string getHash() {
        py_strs(result, this, 1)
    }


    /** Gets the body of this module. */
    StmtList getBody() {
        py_stmt_lists(result, this, 2)
    }


    /** Gets the nth statement of this module. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this module. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }


    /** Gets the kind of this module. */
    string getKind() {
        py_strs(result, this, 3)
    }

    string toString() {
        result = "Module"
    }

}

library class Mult_ extends @py_Mult, Operator {

    string toString() {
        result = "Mult"
    }

}

library class Name_ extends @py_Name, Expr {


    /** Gets the variable of this name expression. */
    Variable getVariable() {
        py_variables(result, this)
    }


    /** Gets the context of this name expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    ExprParent getParent() {
        py_exprs(this, _, result, _)
    }

    string toString() {
        result = "Name"
    }

}

library class Nonlocal_ extends @py_Nonlocal, Stmt {


    /** Gets the names of this nonlocal statement. */
    StringList getNames() {
        py_str_lists(result, this)
    }


    /** Gets the nth name of this nonlocal statement. */
    string getName(int index) {
        result = this.getNames().getItem(index)
    }

    /** Gets a name of this nonlocal statement. */
    string getAName() {
        result = this.getNames().getAnItem()
    }

    string toString() {
        result = "Nonlocal"
    }

}

library class Not_ extends @py_Not, Unaryop {

    string toString() {
        result = "Not"
    }

}

library class NotEq_ extends @py_NotEq, Cmpop {

    string toString() {
        result = "NotEq"
    }

}

library class NotIn_ extends @py_NotIn, Cmpop {

    string toString() {
        result = "NotIn"
    }

}

library class Num_ extends @py_Num, Expr {


    /** Gets the value of this numeric literal. */
    string getN() {
        py_numbers(result, this, 2)
    }


    /** Gets the text of this numeric literal. */
    string getText() {
        py_numbers(result, this, 3)
    }

    string toString() {
        result = "Num"
    }

}

library class Or_ extends @py_Or, Boolop {

    string toString() {
        result = "Or"
    }

}

library class Param_ extends @py_Param, ExprContext {

    string toString() {
        result = "Param"
    }

}

library class Pass_ extends @py_Pass, Stmt {

    string toString() {
        result = "Pass"
    }

}

library class PlaceHolder_ extends @py_PlaceHolder, Expr {


    /** Gets the variable of this template place-holder expression. */
    Variable getVariable() {
        py_variables(result, this)
    }


    /** Gets the context of this template place-holder expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    string toString() {
        result = "PlaceHolder"
    }

}

library class Pow_ extends @py_Pow, Operator {

    string toString() {
        result = "Pow"
    }

}

library class Print_ extends @py_Print, Stmt {


    /** Gets the destination of this print statement. */
    Expr getDest() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the values of this print statement. */
    ExprList getValues() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth value of this print statement. */
    Expr getValue(int index) {
        result = this.getValues().getItem(index)
    }

    /** Gets a value of this print statement. */
    Expr getAValue() {
        result = this.getValues().getAnItem()
    }


    /** Whether the new line property of this print statement is true. */
    predicate isNl() {
        py_bools(this, 3)
    }

    string toString() {
        result = "Print"
    }

}

library class ExprOrPrint_ extends @py_Print_or_expr {

    string toString() {
        result = "ExprOrPrint"
    }

}

library class RShift_ extends @py_RShift, Operator {

    string toString() {
        result = "RShift"
    }

}

library class Raise_ extends @py_Raise, Stmt {


    /** Gets the exception of this raise statement. */
    Expr getExc() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the cause of this raise statement. */
    Expr getCause() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the type of this raise statement. */
    Expr getType() {
        py_exprs(result, _, this, 3)
    }


    /** Gets the instance of this raise statement. */
    Expr getInst() {
        py_exprs(result, _, this, 4)
    }


    /** Gets the traceback of this raise statement. */
    Expr getTback() {
        py_exprs(result, _, this, 5)
    }

    string toString() {
        result = "Raise"
    }

}

library class Repr_ extends @py_Repr, Expr {


    /** Gets the value of this backtick expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }

    string toString() {
        result = "Repr"
    }

}

library class Return_ extends @py_Return, Stmt {


    /** Gets the value of this return statement. */
    Expr getValue() {
        py_exprs(result, _, this, 1)
    }

    string toString() {
        result = "Return"
    }

}

library class Set_ extends @py_Set, Expr {


    /** Gets the elements of this set expression. */
    ExprList getElts() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth element of this set expression. */
    Expr getElt(int index) {
        result = this.getElts().getItem(index)
    }

    /** Gets an element of this set expression. */
    Expr getAnElt() {
        result = this.getElts().getAnItem()
    }

    string toString() {
        result = "Set"
    }

}

library class SetComp_ extends @py_SetComp, Expr {


    /** Gets the implementation of this set comprehension. */
    Function getFunction() {
        py_Functions(result, this)
    }


    /** Gets the iterable of this set comprehension. */
    Expr getIterable() {
        py_exprs(result, _, this, 3)
    }

    string toString() {
        result = "SetComp"
    }

}

library class Slice_ extends @py_Slice, Expr {


    /** Gets the start of this slice. */
    Expr getStart() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the stop of this slice. */
    Expr getStop() {
        py_exprs(result, _, this, 3)
    }


    /** Gets the step of this slice. */
    Expr getStep() {
        py_exprs(result, _, this, 4)
    }

    string toString() {
        result = "Slice"
    }

}

library class Starred_ extends @py_Starred, Expr {


    /** Gets the value of this starred expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the context of this starred expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    string toString() {
        result = "Starred"
    }

}

library class Store_ extends @py_Store, ExprContext {

    string toString() {
        result = "Store"
    }

}

library class Str_ extends @py_Str, Expr {


    /** Gets the text of this unicode literal. */
    string getS() {
        py_strs(result, this, 2)
    }


    /** Gets the prefix of this unicode literal. */
    string getPrefix() {
        py_strs(result, this, 3)
    }


    /** Gets the implicitly_concatenated_parts of this unicode literal. */
    StringPartList getImplicitlyConcatenatedParts() {
        py_StringPart_lists(result, this)
    }


    /** Gets the nth implicitly_concatenated_part of this unicode literal. */
    StringPart getImplicitlyConcatenatedPart(int index) {
        result = this.getImplicitlyConcatenatedParts().getItem(index)
    }

    /** Gets an implicitly_concatenated_part of this unicode literal. */
    StringPart getAnImplicitlyConcatenatedPart() {
        result = this.getImplicitlyConcatenatedParts().getAnItem()
    }

    string toString() {
        result = "Str"
    }

}

library class StringPart_ extends @py_StringPart {


    /** Gets the text of this implicitly concatenated part. */
    string getText() {
        py_strs(result, this, 0)
    }


    /** Gets the location of this implicitly concatenated part. */
    Location getLocation() {
        py_locations(result, this)
    }

    StringPartList getParent() {
        py_StringParts(this, result, _)
    }

    string toString() {
        result = "StringPart"
    }

}

library class StringPartList_ extends @py_StringPart_list {

    BytesOrStr getParent() {
        py_StringPart_lists(this, result)
    }

    /** Gets an item of this implicitly concatenated part list */
    StringPart getAnItem() {
        py_StringParts(result, this, _)
    }

    /** Gets the nth item of this implicitly concatenated part list */
    StringPart getItem(int index) {
        py_StringParts(result, this, index)
    }

    string toString() {
        result = "StringPartList"
    }

}

library class Sub_ extends @py_Sub, Operator {

    string toString() {
        result = "Sub"
    }

}

library class Subscript_ extends @py_Subscript, Expr {


    /** Gets the value of this subscript expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the index of this subscript expression. */
    Expr getIndex() {
        py_exprs(result, _, this, 3)
    }


    /** Gets the context of this subscript expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    string toString() {
        result = "Subscript"
    }

}

library class TemplateDottedNotation_ extends @py_TemplateDottedNotation, Expr {


    /** Gets the object of this template dotted notation expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the attribute name of this template dotted notation expression. */
    string getAttr() {
        py_strs(result, this, 3)
    }


    /** Gets the context of this template dotted notation expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    string toString() {
        result = "TemplateDottedNotation"
    }

}

library class TemplateWrite_ extends @py_TemplateWrite, Stmt {


    /** Gets the value of this template write statement. */
    Expr getValue() {
        py_exprs(result, _, this, 1)
    }

    string toString() {
        result = "TemplateWrite"
    }

}

library class Try_ extends @py_Try, Stmt {


    /** Gets the body of this try statement. */
    StmtList getBody() {
        py_stmt_lists(result, this, 1)
    }


    /** Gets the nth statement of this try statement. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this try statement. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }


    /** Gets the else block of this try statement. */
    StmtList getOrelse() {
        py_stmt_lists(result, this, 2)
    }


    /** Gets the nth else statement of this try statement. */
    Stmt getOrelse(int index) {
        result = this.getOrelse().getItem(index)
    }

    /** Gets an else statement of this try statement. */
    Stmt getAnOrelse() {
        result = this.getOrelse().getAnItem()
    }


    /** Gets the exception handlers of this try statement. */
    StmtList getHandlers() {
        py_stmt_lists(result, this, 3)
    }


    /** Gets the nth exception handler of this try statement. */
    Stmt getHandler(int index) {
        result = this.getHandlers().getItem(index)
    }

    /** Gets an exception handler of this try statement. */
    Stmt getAHandler() {
        result = this.getHandlers().getAnItem()
    }


    /** Gets the finally block of this try statement. */
    StmtList getFinalbody() {
        py_stmt_lists(result, this, 4)
    }


    /** Gets the nth finally statement of this try statement. */
    Stmt getFinalstmt(int index) {
        result = this.getFinalbody().getItem(index)
    }

    /** Gets a finally statement of this try statement. */
    Stmt getAFinalstmt() {
        result = this.getFinalbody().getAnItem()
    }

    string toString() {
        result = "Try"
    }

}

library class Tuple_ extends @py_Tuple, Expr {


    /** Gets the elements of this tuple expression. */
    ExprList getElts() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth element of this tuple expression. */
    Expr getElt(int index) {
        result = this.getElts().getItem(index)
    }

    /** Gets an element of this tuple expression. */
    Expr getAnElt() {
        result = this.getElts().getAnItem()
    }


    /** Gets the context of this tuple expression. */
    ExprContext getCtx() {
        py_expr_contexts(result, _, this)
    }

    ExprParent getParent() {
        py_exprs(this, _, result, _)
    }

    string toString() {
        result = "Tuple"
    }

}

library class UAdd_ extends @py_UAdd, Unaryop {

    string toString() {
        result = "UAdd"
    }

}

library class USub_ extends @py_USub, Unaryop {

    string toString() {
        result = "USub"
    }

}

library class UnaryExpr_ extends @py_UnaryExpr, Expr {


    /** Gets the operator of this unary expression. */
    Unaryop getOp() {
        py_unaryops(result, _, this)
    }


    /** Gets the operand of this unary expression. */
    Expr getOperand() {
        py_exprs(result, _, this, 3)
    }

    string toString() {
        result = "UnaryExpr"
    }

}

library class While_ extends @py_While, Stmt {


    /** Gets the test of this while statement. */
    Expr getTest() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the body of this while statement. */
    StmtList getBody() {
        py_stmt_lists(result, this, 2)
    }


    /** Gets the nth statement of this while statement. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this while statement. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }


    /** Gets the else block of this while statement. */
    StmtList getOrelse() {
        py_stmt_lists(result, this, 3)
    }


    /** Gets the nth else statement of this while statement. */
    Stmt getOrelse(int index) {
        result = this.getOrelse().getItem(index)
    }

    /** Gets an else statement of this while statement. */
    Stmt getAnOrelse() {
        result = this.getOrelse().getAnItem()
    }

    string toString() {
        result = "While"
    }

}

library class With_ extends @py_With, Stmt {


    /** Gets the context manager of this with statement. */
    Expr getContextExpr() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the optional variable of this with statement. */
    Expr getOptionalVars() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the body of this with statement. */
    StmtList getBody() {
        py_stmt_lists(result, this, 3)
    }


    /** Gets the nth statement of this with statement. */
    Stmt getStmt(int index) {
        result = this.getBody().getItem(index)
    }

    /** Gets a statement of this with statement. */
    Stmt getAStmt() {
        result = this.getBody().getAnItem()
    }

    string toString() {
        result = "With"
    }

}

library class Yield_ extends @py_Yield, Expr {


    /** Gets the value of this yield expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }

    string toString() {
        result = "Yield"
    }

}

library class YieldFrom_ extends @py_YieldFrom, Expr {


    /** Gets the value of this yield-from expression. */
    Expr getValue() {
        py_exprs(result, _, this, 2)
    }

    string toString() {
        result = "YieldFrom"
    }

}

library class Alias_ extends @py_alias {


    /** Gets the value of this alias. */
    Expr getValue() {
        py_exprs(result, _, this, 0)
    }


    /** Gets the name of this alias. */
    Expr getAsname() {
        py_exprs(result, _, this, 1)
    }

    AliasList getParent() {
        py_aliases(this, result, _)
    }

    string toString() {
        result = "Alias"
    }

}

library class AliasList_ extends @py_alias_list {

    Import getParent() {
        py_alias_lists(this, result)
    }

    /** Gets an item of this alias list */
    Alias getAnItem() {
        py_aliases(result, this, _)
    }

    /** Gets the nth item of this alias list */
    Alias getItem(int index) {
        py_aliases(result, this, index)
    }

    string toString() {
        result = "AliasList"
    }

}

library class Arguments_ extends @py_arguments {


    /** Gets the keyword default values of this parameters definition. */
    ExprList getKwDefaults() {
        py_expr_lists(result, this, 0)
    }


    /** Gets the nth keyword default value of this parameters definition. */
    Expr getKwDefault(int index) {
        result = this.getKwDefaults().getItem(index)
    }

    /** Gets a keyword default value of this parameters definition. */
    Expr getAKwDefault() {
        result = this.getKwDefaults().getAnItem()
    }


    /** Gets the default values of this parameters definition. */
    ExprList getDefaults() {
        py_expr_lists(result, this, 1)
    }


    /** Gets the nth default value of this parameters definition. */
    Expr getDefault(int index) {
        result = this.getDefaults().getItem(index)
    }

    /** Gets a default value of this parameters definition. */
    Expr getADefault() {
        result = this.getDefaults().getAnItem()
    }


    /** Gets the annotations of this parameters definition. */
    ExprList getAnnotations() {
        py_expr_lists(result, this, 2)
    }


    /** Gets the nth annotation of this parameters definition. */
    Expr getAnnotation(int index) {
        result = this.getAnnotations().getItem(index)
    }

    /** Gets an annotation of this parameters definition. */
    Expr getAnAnnotation() {
        result = this.getAnnotations().getAnItem()
    }


    /** Gets the *arg annotation of this parameters definition. */
    Expr getVarargannotation() {
        py_exprs(result, _, this, 3)
    }


    /** Gets the **kwarg annotation of this parameters definition. */
    Expr getKwargannotation() {
        py_exprs(result, _, this, 4)
    }


    /** Gets the kw_annotations of this parameters definition. */
    ExprList getKwAnnotations() {
        py_expr_lists(result, this, 5)
    }


    /** Gets the nth kw_annotation of this parameters definition. */
    Expr getKwAnnotation(int index) {
        result = this.getKwAnnotations().getItem(index)
    }

    /** Gets a kw_annotation of this parameters definition. */
    Expr getAKwAnnotation() {
        result = this.getKwAnnotations().getAnItem()
    }

    ArgumentsParent getParent() {
        py_arguments(this, result)
    }

    string toString() {
        result = "Arguments"
    }

}

library class ArgumentsParent_ extends @py_arguments_parent {

    string toString() {
        result = "ArgumentsParent"
    }

}

library class AstNode_ extends @py_ast_node {

    string toString() {
        result = "AstNode"
    }

}

library class Boolop_ extends @py_boolop {

    BoolExpr getParent() {
        py_boolops(this, _, result)
    }

    string toString() {
        result = "Boolop"
    }

}

library class Cmpop_ extends @py_cmpop {

    CmpopList getParent() {
        py_cmpops(this, _, result, _)
    }

    string toString() {
        result = "Cmpop"
    }

}

library class CmpopList_ extends @py_cmpop_list {

    Compare getParent() {
        py_cmpop_lists(this, result)
    }

    /** Gets an item of this comparison operator list */
    Cmpop getAnItem() {
        py_cmpops(result, _, this, _)
    }

    /** Gets the nth item of this comparison operator list */
    Cmpop getItem(int index) {
        py_cmpops(result, _, this, index)
    }

    string toString() {
        result = "CmpopList"
    }

}

library class Comprehension_ extends @py_comprehension {


    /** Gets the location of this comprehension. */
    Location getLocation() {
        py_locations(result, this)
    }


    /** Gets the iterable of this comprehension. */
    Expr getIter() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the target of this comprehension. */
    Expr getTarget() {
        py_exprs(result, _, this, 2)
    }


    /** Gets the conditions of this comprehension. */
    ExprList getIfs() {
        py_expr_lists(result, this, 3)
    }


    /** Gets the nth condition of this comprehension. */
    Expr getIf(int index) {
        result = this.getIfs().getItem(index)
    }

    /** Gets a condition of this comprehension. */
    Expr getAnIf() {
        result = this.getIfs().getAnItem()
    }

    ComprehensionList getParent() {
        py_comprehensions(this, result, _)
    }

    string toString() {
        result = "Comprehension"
    }

}

library class ComprehensionList_ extends @py_comprehension_list {

    ListComp getParent() {
        py_comprehension_lists(this, result)
    }

    /** Gets an item of this comprehension list */
    Comprehension getAnItem() {
        py_comprehensions(result, this, _)
    }

    /** Gets the nth item of this comprehension list */
    Comprehension getItem(int index) {
        py_comprehensions(result, this, index)
    }

    string toString() {
        result = "ComprehensionList"
    }

}

library class Expr_ extends @py_expr {


    /** Gets the location of this expression. */
    Location getLocation() {
        py_locations(result, this)
    }


    /** Whether the parenthesised property of this expression is true. */
    predicate isParenthesised() {
        py_bools(this, 1)
    }

    ExprParent getParent() {
        py_exprs(this, _, result, _)
    }

    string toString() {
        result = "Expr"
    }

}

library class ExprContext_ extends @py_expr_context {

    ExprContextParent getParent() {
        py_expr_contexts(this, _, result)
    }

    string toString() {
        result = "ExprContext"
    }

}

library class ExprContextParent_ extends @py_expr_context_parent {

    string toString() {
        result = "ExprContextParent"
    }

}

library class ExprList_ extends @py_expr_list {

    ExprListParent getParent() {
        py_expr_lists(this, result, _)
    }

    /** Gets an item of this expression list */
    Expr getAnItem() {
        py_exprs(result, _, this, _)
    }

    /** Gets the nth item of this expression list */
    Expr getItem(int index) {
        py_exprs(result, _, this, index)
    }

    string toString() {
        result = "ExprList"
    }

}

library class ExprListParent_ extends @py_expr_list_parent {

    string toString() {
        result = "ExprListParent"
    }

}

library class ExprOrStmt_ extends @py_expr_or_stmt {

    string toString() {
        result = "ExprOrStmt"
    }

}

library class ExprParent_ extends @py_expr_parent {

    string toString() {
        result = "ExprParent"
    }

}

library class Keyword_ extends @py_keyword {


    /** Gets the name of this keyword. */
    string getArg() {
        py_strs(result, this, 0)
    }


    /** Gets the value of this keyword. */
    Expr getValue() {
        py_exprs(result, _, this, 1)
    }


    /** Gets the location of this keyword. */
    Location getLocation() {
        py_locations(result, this)
    }

    KeywordList getParent() {
        py_keywords(this, result, _)
    }

    string toString() {
        result = "Keyword"
    }

}

library class KeywordList_ extends @py_keyword_list {

    KeywordListParent getParent() {
        py_keyword_lists(this, result)
    }

    /** Gets an item of this keyword list */
    Keyword getAnItem() {
        py_keywords(result, this, _)
    }

    /** Gets the nth item of this keyword list */
    Keyword getItem(int index) {
        py_keywords(result, this, index)
    }

    string toString() {
        result = "KeywordList"
    }

}

library class KeywordListParent_ extends @py_keyword_list_parent {

    string toString() {
        result = "KeywordListParent"
    }

}

library class LocationParent_ extends @py_location_parent {

    string toString() {
        result = "LocationParent"
    }

}

library class Operator_ extends @py_operator {

    BinaryExpr getParent() {
        py_operators(this, _, result)
    }

    string toString() {
        result = "Operator"
    }

}

library class Parameter_ extends @py_parameter {

    string toString() {
        result = "Parameter"
    }

}

library class Scope_ extends @py_scope {

    string toString() {
        result = "Scope"
    }

}

library class Stmt_ extends @py_stmt {


    /** Gets the location of this statement. */
    Location getLocation() {
        py_locations(result, this)
    }

    StmtList getParent() {
        py_stmts(this, _, result, _)
    }

    string toString() {
        result = "Stmt"
    }

}

library class StmtList_ extends @py_stmt_list {

    StmtListParent getParent() {
        py_stmt_lists(this, result, _)
    }

    /** Gets an item of this statement list */
    Stmt getAnItem() {
        py_stmts(result, _, this, _)
    }

    /** Gets the nth item of this statement list */
    Stmt getItem(int index) {
        py_stmts(result, _, this, index)
    }

    string toString() {
        result = "StmtList"
    }

}

library class StmtListParent_ extends @py_stmt_list_parent {

    string toString() {
        result = "StmtListParent"
    }

}

library class StringList_ extends @py_str_list {

    StrListParent getParent() {
        py_str_lists(this, result)
    }

    /** Gets an item of this string list */
    string getAnItem() {
        py_strs(result, this, _)
    }

    /** Gets the nth item of this string list */
    string getItem(int index) {
        py_strs(result, this, index)
    }

    string toString() {
        result = "StringList"
    }

}

library class StrListParent_ extends @py_str_list_parent {

    string toString() {
        result = "StrListParent"
    }

}

library class StrParent_ extends @py_str_parent {

    string toString() {
        result = "StrParent"
    }

}

library class Unaryop_ extends @py_unaryop {

    UnaryExpr getParent() {
        py_unaryops(this, _, result)
    }

    string toString() {
        result = "Unaryop"
    }

}

library class VariableParent_ extends @py_variable_parent {

    string toString() {
        result = "VariableParent"
    }

}

