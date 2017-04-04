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

/** Utilities for handling the zope libraries */

import python

/** A method that to a sub-class of `zope.interface.Interface` */
class ZopeInterfaceMethod extends PyFunctionObject {

    /** Holds if this method belongs to a class that sub-classes `zope.interface.Interface` */
    ZopeInterfaceMethod() {
        exists(ModuleObject zope, Object interface, ClassObject owner |
            zope.getAttribute("Interface") = interface and
            zope.getName() = "zope.interface" and
            owner.declaredAttribute(_) = this and
            owner.getAnImproperSuperType().getABaseType() = interface
        )
    }

    int minParameters() {
        result = super.minParameters() + 1
    }

    int maxParameters() {
        if exists(this.getFunction().getVararg()) then
            result = super.maxParameters()
        else
            result = super.maxParameters() + 1
    }

}
