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

/** Base class for operators */
class Operator extends Operator_ {

    /** Gets the name of the special method used to implement this operator */
    string getSpecialMethodName() { none() }

}

/* Unary Expression and its operators */

/** A unary expression: (`+x`), (`-x`) or (`~x`) */
class UnaryExpr extends UnaryExpr_ {

    Expr getASubExpression() {
       result = this.getOperand()
    }

}

/** A unary operator: `+`, `-`, `~` or `not` */
class Unaryop extends Unaryop_ {

    /** Gets the name of the special method used to implement this operator */
    string getSpecialMethodName() { none() }

}

/** An invert (`~`) unary operator */
class Invert extends Invert_ {

    string getSpecialMethodName() { result = "__invert__" }

}

/** A positive (`+`) unary operator */ 
class UAdd extends UAdd_ {

    string getSpecialMethodName() { result = "__pos__" }

}

/** A negation (`-`) unary operator */
class USub extends USub_ {

    string getSpecialMethodName() { result = "__neg__" }

}

/** A `not` unary operator */
class Not extends Not_ {

    string getSpecialMethodName() { none() }

}


/* Binary Operation and its operators */

/** A binary expression, such as `x + y` */
class BinaryExpr extends BinaryExpr_ {

  Expr getASubExpression() {
      result = this.getLeft() or result = this.getRight()
  }

}

/** A power (`**`) binary operator */
class Pow extends Pow_ {
  
    string getSpecialMethodName() { result = "__pow__" }

}

/** A right shift (`>>`) binary operator */
class RShift extends RShift_ {

    string getSpecialMethodName() { result = "__rshift__" }
}

/** A subtract (`-`) binary operator */
class Sub extends Sub_ {

    string getSpecialMethodName() { result = "__sub__" }

}

/** A bitwise and (`&`) binary operator */
class BitAnd extends BitAnd_ {

    string getSpecialMethodName() { result = "__and__" }

}

/** A bitwise or (`|`) binary operator */
class BitOr extends BitOr_ {

    string getSpecialMethodName() { result = "__or__" }

}

/** A bitwise exclusive-or (`^`) binary operator */
class BitXor extends BitXor_ {

    string getSpecialMethodName() { result = "__xor__" }

}

/** An add (`+`) binary operator */
class Add extends Add_ {

    string getSpecialMethodName() { result = "__add__" }
}

/** An (true) divide (`/`) binary operator */
class Div extends Div_ {

    string getSpecialMethodName() { 
        result = "__truediv__"
        or
        major_version() = 2 and result = "__div__"
    }
}

/** An floor divide (`//`) binary operator */
class FloorDiv extends FloorDiv_ {

    string getSpecialMethodName() { result = "__floordiv__" }

}

/** A left shift (`<<`) binary operator */
class LShift extends LShift_ {

    string getSpecialMethodName() { result = "__lshift__" }

}

/** A modulo (`%`) binary operator, which includes  string formatting */
class Mod extends Mod_ {

    string getSpecialMethodName() { result = "__mod__" }

}

/** A multiplication (`*`) binary operator */
class Mult extends Mult_ {

    string getSpecialMethodName() { result = "__mul__" }

}

/** A matrix multiplication (`@`) binary operator */
class MatMult extends MatMult_ {

    string getSpecialMethodName() { result = "__matmul__" }

}

/* Comparison Operation and its operators */

/** A comparison operation, such as `x<y` */
class Compare extends Compare_ {

    Expr getASubExpression() {
        result = this.getLeft() or result = this.getAComparator()
    }

    /** Whether as part of this comparison 'left' is compared with 'right' using the operator 'op'.
     *  For example, the comparison `a<b<c` compares(`a`, `b`, `<`) and compares(`b`, `c`, `<`). */
    predicate compares(Expr left, Cmpop op, Expr right)
    {
        this.getLeft() = left and this.getComparator(0) = right and op = this.getOp(0)
        or
        exists(int n | this.getComparator(n) = left and this.getComparator(n+1) = right and op = this.getOp(n+1)) 
    }

}

/** List of comparison operators in a comparison */
class CmpopList extends CmpopList_ {

}

/** A comparison operator */
abstract class Cmpop extends Cmpop_ {

    string getSymbol() {
        none() 
    }

    string getSpecialMethodName() { none() }

}

/** A greater than (`>`) comparison operator */
class Gt extends Gt_ {

    string getSymbol() {
        result = ">" 
    }

    string getSpecialMethodName() { result = "__gt__" }

}

/** A greater than or equals (`>=`) comparison operator */
class GtE extends GtE_ {

    string getSymbol() {
        result = ">=" 
    }

    string getSpecialMethodName() { result = "__ge__" }

}

/** An `in` comparison operator */
class In extends In_ {

    string getSymbol() {
        result = "in" 
    }

}

/** An `is` comparison operator */
class Is extends Is_ {

    string getSymbol() {
        result = "is" 
    }

}

/** An `is not` comparison operator */
class IsNot extends IsNot_ {

    string getSymbol() {
        result = "is not" 
    }

}

/** An equals (`==`) comparison operator */
class Eq extends Eq_ {

    string getSymbol() {
        result = "==" 
    }

    string getSpecialMethodName() { result = "__eq__" }

}

/** A less than (`<`) comparison operator */
class Lt extends Lt_ {

    string getSymbol() {
        result = "<" 
    }

    string getSpecialMethodName() { result = "__lt__" }

}

/** A less than or equals (`<=`) comparison operator */
class LtE extends LtE_ {

    string getSymbol() {
        result = "<=" 
    }

    string getSpecialMethodName() { result = "__le__" }

}

/** A not equals (`!=`) comparison operator */
class NotEq extends NotEq_ {

    string getSymbol() {
        result = "!=" 
    }

    string getSpecialMethodName() { result = "__ne__" }

}

/** An `not in` comparison operator */
class NotIn extends NotIn_ {

  string getSymbol() {
      result = "not in" 
  }

}

/* Boolean Operation (and/or) and its operators */

/** A boolean shortcut (and/or) operation */
class BoolExpr extends BoolExpr_ {

  Expr getASubExpression() {
    result = this.getAValue()
  }

  string getOperator() {
      this.getOp() instanceof And and result = "and"
      or
      this.getOp() instanceof Or and result = "or"
  }

  /** Whether part evaluates to partIsTrue if this evaluates to wholeIsTrue */
  predicate impliesValue(Expr part, boolean partIsTrue, boolean wholeIsTrue) {
      if this.getOp() instanceof And then (
          wholeIsTrue = true and partIsTrue = true and part = this.getAValue()
          or
          wholeIsTrue = true and ((BoolExpr)this.getAValue()).impliesValue(part, partIsTrue, true)
      ) else (
          wholeIsTrue = false and partIsTrue = false and part = this.getAValue()
          or
          wholeIsTrue = false and ((BoolExpr)this.getAValue()).impliesValue(part, partIsTrue, false)
      )
  }

}

/** A short circuit boolean operator, and/or */
class Boolop extends Boolop_ {

}

/** An `and` boolean operator */
class And extends And_ {

}

/** An `or` boolean operator */
class Or extends Or_ {

}
