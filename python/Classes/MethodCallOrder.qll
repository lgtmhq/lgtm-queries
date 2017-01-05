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

// Helper predicates for mutliple call to __init__/__del__ queries.

predicate multiple_calls_to_superclass_method(ClassObject self, FunctionObject multi, string name) {
    exists(FunctionObject top_method |
        super_class_method(self, top_method, multi, name) and
        strictcount(FunctionObject x | 
            super_class_method(self, top_method, x, name) and
            x.getACallee() = multi
        ) > 1
    )
}

private predicate super_class_method(ClassObject self, FunctionObject top_method, FunctionObject method, string name) {
    (name = "__init__" or name = "__del__") and
    self.lookupAttribute(name) = top_method and
    top_method.getACallee*() = method and
    self.getAnImproperSuperType().declaredAttribute(name) = method
}

predicate missing_call_to_superclass_method(ClassObject self, FunctionObject top_method, FunctionObject missing, string name) {
    self.lookupAttribute(name) = top_method and
    missing != top_method and
    self.getAnImproperSuperType().declaredAttribute(name) = missing and
    not top_method.getACallee*() = missing and
    /* Make sure that all 'methods' are objects that we can understand */
    forall(Object init |
        init = self.getAnImproperSuperType().declaredAttribute(name) |
        init instanceof FunctionObject
    )
}
