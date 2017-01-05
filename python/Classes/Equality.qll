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


private Attribute dictAccess(LocalVariable var) {
    result.getName() = "__dict__" and
    result.getObject() = var.getAnAccess()
}

/** A generic equality method that compares all attributes in its dict. */
class GenericEqMethod extends Function {

    GenericEqMethod() {
        this.getName() = "__eq__" and
        exists(LocalVariable self, LocalVariable other |
            self.getAnAccess() = this.getArg(0) and self.getId() = "self" and
            other.getAnAccess() = this.getArg(1) and
            exists(Compare eq | eq.getOp(0) instanceof Eq |
                eq.getAChildNode() = dictAccess(self) and
                eq.getAChildNode() = dictAccess(other)
            )
        )
    }
}

/** An __eq__ method that just does self is other */
class IdentityEqMethod extends Function {
 
    IdentityEqMethod() {
        this.getName() = "__eq__" and
        exists(LocalVariable self, LocalVariable other |
            self.getAnAccess() = this.getArg(0) and self.getId() = "self" and
            other.getAnAccess() = this.getArg(1) and
            exists(Compare eq | eq.getOp(0) instanceof Is |
                eq.getAChildNode() = self.getAnAccess() and
                eq.getAChildNode() = other.getAnAccess()
            )
        )
    }

}

/** An (in)equality method that delegates to its complement */
class DelegatingEqualityMethod extends Function {
 
    DelegatingEqualityMethod() {
        exists(Return ret, UnaryExpr not_, Compare comp, Cmpop op, Parameter p0, Parameter p1 |
            ret.getScope() = this and
            ret.getValue() = not_ and
            not_.getOp() instanceof Not and not_.getOperand() = comp and
            comp.compares(p0.getVariable().getAnAccess(), op, p1.getVariable().getAnAccess()) |
            this.getName() = "__eq__" and op instanceof NotEq or 
            this.getName() = "__ne__" and op instanceof Eq
        )
    }
}
