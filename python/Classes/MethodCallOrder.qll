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

// Helper predicates for multiple call to __init__/__del__ queries.

/** Holds if `self.name` calls `multi` by mutliple paths, and thus calls it more than once */
predicate multiple_calls_to_superclass_method(ClassObject self, FunctionObject multi, string name) {
    exists(FunctionInvocation top, FunctionInvocation i1, FunctionInvocation i2 |
        i1 != i2 and
        top.runtime(self.declaredAttribute(name)) and
        i1 = top.getACallee+() and
        i2 = top.getACallee+() and
        i1.getFunction() = multi and
        i2.getFunction() = multi and
        self.getASuperType().declaredAttribute(name) = multi
    )
}

/** Holds if `self.name` does not call `missing`, even though it is expected to */
predicate missing_call_to_superclass_method(ClassObject self, FunctionObject missing, string name) {
    missing = self.getASuperType().declaredAttribute(name) and
    exists(FunctionInvocation top |
        top.runtime(self.lookupAttribute(name)) and
        /* There is no call to missing originating from top */
        not exists(FunctionInvocation i |
            i = top.getACallee*() and
            i.getFunction() = missing
        )
    ) and
    /* Make sure that all 'methods' are objects that we can understand */
    forall(ClassObject sup |
        sup = self.getAnImproperSuperType() and
        sup.declaresAttribute(name) |
        sup.declaredAttribute(name) instanceof FunctionObject
    ) and
    not self.isAbstract()
}
