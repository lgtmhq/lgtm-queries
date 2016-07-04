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
import semmle.python.types.ImportTime

abstract class ModuleObject extends Object {

    ModuleObject () {
        exists(Module m | m.getEntryNode() = this)
        or
        py_cobjecttypes(this, theModuleType())
    }

    /** Gets the scope corresponding to this module, if this is a Python module */
    Module getModule() {
        none()
    }

    /** Gets the name of this scope */
    abstract string getName();

    string toString() {
        result = "Module " + this.getName()
    }

    /** Gets the named attribute of this module. Using attributeRefersTo() instead
     * may provide better results for presentation. */
    abstract cached Object getAttribute(string name);

    /** Whether the named attribute of this module "refers-to" value, with a known origin.
     */
    abstract predicate attributeRefersTo(string name, Object value, ControlFlowNode origin);

    /** Gets the package for this module. */
    PackageObject getPackage() {
        this.getName().matches("%.%") and
        result.getName() = this.getName().regexpReplaceAll("\\.[^.]*$", "")
    }

    /** Whether this module "exports" `name`. That is, whether using `import *` on this module
     will result in `name` being added to the namespace. */
    abstract predicate exports(string name);

    /** Whether the complete set of names "exported" by this module can be accurately determined */
    abstract predicate exportsComplete();

    /** Gets the short name of the module. For example the short name of module x.y.z is 'z' */
    string getShortName() {
        result = this.getName().suffix(this.getPackage().getName().length()+1)
        or
        result = this.getName() and not exists(this.getPackage())
    }

    /** Whether this module is imported by 'import name'. For example on a linux system,
      * the module 'posixpath' is imported as 'os.path' or as 'posixpath' */
    predicate importedAs(string name) {
        import_time_module_imported_as(this, name)
    }

    abstract predicate hasAttribute(string name);

    ModuleObject getAnImportedModule() {
        result.importedAs(this.getModule().getAnImportedModuleName())
    }

}

class BuiltinModuleObject extends ModuleObject {

    BuiltinModuleObject () {
        py_cobjecttypes(this, theModuleType())
    }

    string getName() {
        py_cobjectnames(this, result)
    }

    Object getAttribute(string name) {
        py_cmembers(this, name, result)
    }

    predicate exports(string name) {
        py_cmembers(this, name, _) and
        not name.matches("\\_%")
    }

    predicate hasAttribute(string name) {
        py_cmembers(this, name, _)
    }

    predicate attributeRefersTo(string name, Object value, ControlFlowNode origin) {
        none() 
    }

    predicate exportsComplete() {
        any()
    }


}

class PythonModuleObject extends ModuleObject {

    PythonModuleObject() {
        exists(Module m | m.getEntryNode() = this |
            not m.isPackage()
        )
    }

    string getName() {
        result = this.getModule().getName()
    }

    Module getModule() {
        result = this.getOrigin()
    }

    cached Object getAttribute(string name) {
        import_time_py_module_attributes(this.getModule(), name, result, _)
    }

    predicate exports(string name) {
        import_time_exports(this.getModule(), name)
    }

    predicate exportsComplete() {
        import_time_exports_complete(this.getModule())
    }

    predicate hasAttribute(string name) {
        ((ImportTimeScope)this.getModule()).definesName(name)
        or
        /* The interpreter always adds the __name__ and __package__ attributes */
        name = "__name__" or name = "__package__"
    }

    predicate attributeRefersTo(string name, Object value, ControlFlowNode origin) {
         import_time_py_module_attributes(this.getModule(), name, value, origin)
    }

}

/**  Primarily for internal use.
 *
 * Gets the object for the string text. 
 * The extractor will have populated a str object 
 * for each module name, with the name b'text' or u'text' (including the quotes).
 */
Object object_for_string(string text) {
    py_cobjecttypes(result, theStrType()) and
    exists(string repr |
        py_cobjectnames(result, repr) and
        repr.charAt(1) = "'" |
        /* Strip quotes off repr */
        text = repr.substring(2, repr.length()-1)
    )
}

class PackageObject extends ModuleObject {

    PackageObject() {
        exists(Module p | p.getEntryNode() = this |
            p.isPackage()
        )
    }

    string getName() {
        result = this.getModule().getName()
    }

    Module getModule() {
        result = this.getOrigin()
    }

    ModuleObject submodule(string name) {
        result.getPackage() = this and
        name = result.getShortName()
    }

    Object getAttribute(string name) {
        import_time_package_attributes(this.getModule(), name, result, _)
    }

    PythonModuleObject getInitModule() {
        result.getModule() = this.getModule().getInitModule()
    }

    predicate exports(string name) {
        import_time_exports(this.getModule(), name)
    }

    predicate exportsComplete() {
        not exists(this.getInitModule())
        or
        this.getInitModule().exportsComplete()
    }

    predicate hasAttribute(string name) {
        exists(this.submodule(name))
        or
        this.getInitModule().hasAttribute(name)
    }

    predicate attributeRefersTo(string name, Object value, ControlFlowNode origin) {
        import_time_package_attributes(this.getModule(), name, value, origin)
    }

}

