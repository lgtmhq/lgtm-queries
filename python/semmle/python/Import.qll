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


/** An alias in an import statement, the `mod as name` part of `import mod as name`. May be artificial;
    `import x` is transformed into `import x as x` */
class Alias extends Alias_ {

    Location getLocation() {
        result = this.getValue().getLocation()
    }

}

private
predicate hasFromFutureImportAbsoluteImport(Module module) {
    exists(Import i, ImportMember im, ImportExpr ie, Alias a, Name name |
        im.getModule() = ie and ie.getName() = "__future__" and
        a.getAsname() = name and name.getId() = "absolute_import" and
        i.getASubExpression() = im and
        i.getAName() = a and
        i.getEnclosingModule() = module)
}

private predicate valid_module_name(string name) {
    exists(Module m | m.getName() = name)
    or
    exists(Object cmod | py_cobjecttypes(cmod, theModuleType()) and py_cobjectnames(cmod, name))
}

/** An artificial expression representing an import */
class ImportExpr extends ImportExpr_ {

    private Module basePackage(int n) {
        n = 1 and result = this.getEnclosingModule().getPackage()
        or
        exists(int nm1 | n = nm1 + 1 | result = this.basePackage(nm1).getPackage())
    }

    private predicate implicitRelativeImportsAllowed() {
         // relative imports are no longer allowed in Python 3
        major_version() < 3 and
        // and can be explicitly turned off in later versions of Python 2
        not hasFromFutureImportAbsoluteImport(getEnclosingModule())
    }

    /** The language specifies level as -1 if relative imports are to be tried first, 0 for absolute imports,
        and level > 0 for explicit relative imports. */
    int getLevel() {
        exists(int l | l = super.getLevel() |
            l > 0 and result = l
            or
            /* The extractor may set level to 0 even though relative imports apply */
            l = 0 and (
                if this.implicitRelativeImportsAllowed() then
                    result = -1
                else
                    result = 0
            )
        )
    }

    /**
     * If this import is relative, and relative imports are allowed, compute
     * the name of the topmost module that will be imported.
     */
    private string relativeTopName() {
        getLevel() = -1 and
        result = basePackage(1).getName() + "." + this.getTopName() and
        valid_module_name(result)
    }

    private string qualifiedTopName() {
        if (this.getLevel() <= 0) then (
            result = this.getTopName()
        ) else (
            result = basePackage(this.getLevel()).getName() and
            valid_module_name(result)
        )
    }

    /** Gets the name by which the lowest level module or package is imported. 
     *  NOTE: This is the name that used to import the module, 
     *  which may not be the name of the module. */
    string bottomModuleName() {
        result = relativeTopName() + this.remainderOfName()
        or
        (
            not exists(relativeTopName()) and
            result = this.qualifiedTopName() + this.remainderOfName()
        )
    }

    /** Gets the name of topmost module or package being imported */
    string topModuleName() {
        result = relativeTopName()
        or
        (
            not exists(relativeTopName()) and
            result = this.qualifiedTopName()
        )
    }

    /** Gets the full name of the module resulting from evaluating this import.
     *  NOTE: This is the name that used to import the module, 
     *  which may not be the name of the module. */
    string getImportedModuleName() {
        exists(string bottomName | bottomName = this.bottomModuleName() |
            if this.isTop() then
                result = topModuleName()
            else
                result = bottomName
        )
    }

    /** Gets the names of the modules that may be imported by this import.
     * For example this predicate would return 'x' and 'x.y' for `import x.y`
     */
    string getAnImportedModuleName() {
        result = this.bottomModuleName()
        or
        result = this.getAnImportedModuleName().regexpReplaceAll("\\.[^.]*$", "")
    }

    Expr getASubExpression() {
        none()
    }

    predicate hasSideEffects() {
        any()
    }

    private string getTopName() {
        result = this.getName().regexpReplaceAll("\\..*", "")
    }

    private string remainderOfName() {
        not exists(this.getName()) and result = "" or
        this.getLevel() <= 0 and result = this.getName().regexpReplaceAll("^[^\\.]*", "") or
        this.getLevel() > 0 and result = "." + this.getName()
    }

    /** Whether this import is relative, that is not absolute.
     * See https://www.python.org/dev/peps/pep-0328/ */
    predicate isRelative() {
        /* Implicit */
        exists(this.relativeTopName())
        or
        /* Explicit */
        this.getLevel() > 0
    }

}

/** A `from ... import ...` expression */
class ImportMember extends ImportMember_ {

    Expr getASubExpression() {
        result = this.getModule()
    }

    predicate hasSideEffects() {
        /* Strictly this only has side-effects if the module is a package */
        any()
    }

    /** Gets the full name of the module resulting from evaluating this import.
     *  NOTE: This is the name that used to import the module, 
     *  which may not be the name of the module. */
    string getImportedModuleName() {
        result = this.getModule().(ImportExpr).getImportedModuleName() + "." + this.getName()
    }

    ImportMemberNode getAFlowNode() { result = super.getAFlowNode() }
}

/** An import statement */
class Import extends Import_ {

    private ImportExpr getAModuleExpr() {
        result = this.getAName().getValue()
        or 
        result = ((ImportMember)this.getAName().getValue()).getModule()
    }

    /** Use getAnImportedModuleName(), 
     * possibly combined with ModuleObject.importedAs()
     * Gets a module imported by this import statement */
    deprecated Module getAModule() {
        result.getName() = this.getAnImportedModuleName()
    }

    /** Whether this a `from ... import ...` statement */
    predicate isFromImport() {
        this.getAName().getValue() instanceof ImportMember
    }

    Expr getASubExpression() {
        result = this.getAModuleExpr() or
        result = this.getAName().getAsname() or
        result = this.getAName().getValue()
    }

    Stmt getASubStatement() {
        none()
    }

    /** Gets the name of an imported module. 
     * For example, for the import statement `import bar` which
     * is a relative import in package "foo", this would return
     * "foo.bar".
     * The import statment `from foo import bar` would return 
     * `foo` and `foo.bar`
     *  */
    string getAnImportedModuleName() {
        result = this.getAModuleExpr().getAnImportedModuleName()
        or
        exists(ImportMember m, string modname |
            m = this.getAName().getValue() and
            modname = m.getModule().(ImportExpr).getImportedModuleName() |
            result = modname
            or
            result = modname + "." + m.getName()
        )
    }

}

/** An import * statement */
class ImportStar extends ImportStar_ {

    ImportExpr getModuleExpr() {
        result = this.getModule()
        or
        result = ((ImportMember)this.getModule()).getModule()
    }

    string toString() {
        result = "from " + this.getModuleExpr().getName() + " import *"
    }

    /** Use getAnImportedModuleName(), 
     * possibly combined with ModuleObject.importedAs()
     * Gets the module imported by this import * statement 
     */
    deprecated Module getTheModule() {
        result.getName() = this.getImportedModuleName()
    }

    Expr getASubExpression() {
        result = this.getModule()
    }

    Stmt getASubStatement() {
        none()
    }

    /** Gets the name of the imported module. */
    string getImportedModuleName() {
        result = this.getModuleExpr().getImportedModuleName()
    }

}


class ImportingStmt extends Stmt {
 
    ImportingStmt() {
        this instanceof Import
        or
        this instanceof ImportStar
    }

    /** Gets the name of an imported module. */
    string getAnImportedModuleName() {
        result = this.(Import).getAnImportedModuleName() 
        or
        result = this.(ImportStar).getImportedModuleName()
    }

}
