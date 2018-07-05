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

import cpp

class IgnoreAllVolatileSpecifiersEverywhere extends Specifier {
    override string getName() { result = super.getName() and result != "volatile" }
}

class SizeofImpureExprOperator extends SizeofExprOperator {
    SizeofImpureExprOperator () {
        exists (Expr e |
                e = this.getExprOperand()
            and not e.isPure()
            and not e.isAffectedByMacro()
            and not e.(OverloadedPointerDereferenceExpr).getExpr().isPure()
            and not exists(OverloadedArrayExpr op | op = e |
                           op.getArrayBase().isPure()
                       and op.getArrayOffset().isPure()))
    }
}

