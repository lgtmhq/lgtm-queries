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

/** A variable, either a global or local variable (including parameters) */
class Variable extends @py_variable {

    /** Gets the identifier (name) of this variable */
    string getId() {
        variable(this, _, result)
    }

    string toString() {
        result = "Variable " + this.getId()
    }

    /** Gets an access (load or store) of this variable */
    Name getAnAccess() {
        result = this.getALoad()
        or
        result = this.getAStore()
    }

    /** Gets a load of this variable */
    Name getALoad() {
        result.uses(this)
    }

    /** Gets a store of this variable */
    Name getAStore() {
        result.defines(this)
    }

    /** Gets the scope of this variable */
    Scope getScope() {
        variable(this, result, _)
    }

    /** Whether there is an access to this variable outside
     * of its own scope. Usually occurs in nested functions.
     */
    predicate escapes() {
        none()
    }

    /** Whether this variable is a parameter */
    predicate isParameter() {
        none()
    }

}

/** A local (function or class) variable */
class LocalVariable extends Variable {

    LocalVariable() {
        exists(Scope s | s = this.getScope() | s instanceof Function or s instanceof Class)
    }

    string toString() {
        result = "Local Variable " + this.getId()
    }

    predicate escapes() {
        exists(Name n | n = this.getAnAccess() | n.getScope() != this.getScope())
    }

    /** Whether this variable is a parameter */
    predicate isParameter() {
        exists(Parameter p | this.getAnAccess() = p)
    }

}

/** A local variable that uses "load fast" semantics, for lookup:
 * If the variable is undefined, then raise an exception. 
 */
class FastLocalVariable extends LocalVariable {

    FastLocalVariable() {
        this.getScope() instanceof FastLocalsFunction
    }

}

/** A local variable that uses "load name" semantics, for lookup:
 * If the variable is undefined, then lookup the value in globals().
 */
class NameLocalVariable extends LocalVariable {
 
    NameLocalVariable() {
        not this instanceof FastLocalVariable 
    }

}

/** A global (module-level) variable */
class GlobalVariable extends Variable {

    GlobalVariable() {
        exists(Module m | m = this.getScope())
    }

    string toString() {
        result = "Global Variable " + this.getId()
    }

}


