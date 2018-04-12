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
private import semmle.python.pointsto.Final

/** A bound method object, x.f where type(x) has a method f */
class BoundMethod extends Object {

    BoundMethod() {
        bound_method(this, _)
    }

    /* Gets the method 'f' in 'x.f' */
    FunctionObject getMethod() {
         bound_method(this, result)
    }

}

private predicate bound_method(AttrNode binding, FunctionObject method) {
    binding = method.getAMethodCall().getFunction()
}

private predicate decorator_call(Object method, ClassObject decorator, FunctionObject func) {
    exists(CallNode f |
        method = f and
        f.getFunction().refersTo(decorator) and
        FinalPointsTo::points_to(f.getArg(0), _, func, _, _)
    )
}

/** A class method object. Either a decorated function or an explicit call to classmethod(f) */ 
class ClassMethodObject extends Object {

    ClassMethodObject() {
        decorator_call(this, theClassMethodType(), _)
    }

    FunctionObject getFunction() {
        decorator_call(this, theClassMethodType(), result)
    }

}

/** A static method object. Either a decorated function or an explicit call to staticmethod(f) */ 
class StaticMethodObject extends Object {

    StaticMethodObject() {
        decorator_call(this, theStaticMethodType(), _)
    }

    FunctionObject getFunction() {
        decorator_call(this, theStaticMethodType(), result)
    }

}

