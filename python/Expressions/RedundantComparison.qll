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

class RedundantComparison extends Compare {

    RedundantComparison() {
        exists(Expr left, Expr right |
            this.compares(left, _, right)
            and
            same_variable(left, right)
        )
    }
   
    predicate maybeMissingSelf() {
        exists(Name left |
            this.compares(left, _, _) and
            not this.isConstant() and
            exists(Class cls | left.getScope().getScope() = cls |
                exists(SelfAttribute sa | sa.getName() = left.getId() |
                    sa.getClass() = cls
                )
            )
        )
    }

}

private predicate same_variable(Expr left, Expr right) {
    same_name(left, right)
    or
    same_attribute(left, right)
}

private predicate name_in_comparison(Compare comp, Name n, Variable v) {
    comp.contains(n) and v = n.getVariable()
}

private predicate same_name(Name n1, Name n2) {
    n1 != n2 and
    exists(Compare comp, Variable v | name_in_comparison(comp, n1, v) and name_in_comparison(comp, n2, v))
}

private predicate same_attribute(Attribute a1, Attribute a2) {
    a1 != a2 and
    exists(Compare comp | comp.contains(a1) and comp.contains(a2)) and
    a1.getName() = a2.getName() and same_name(a1.getObject(), a2.getObject())
}
