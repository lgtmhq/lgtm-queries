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

/**
 * Provides classes and predicates for working with Java imports.
 */

import semmle.code.Location
import CompilationUnit

/** A common super-class for all kinds of Java import declarations. */
class Import extends Element, @import {
  /** The compilation unit in which this import declaration occurs. */
  override CompilationUnit getCompilationUnit() { result = this.getFile() }

  /** Holds if this import declaration occurs in source code. */
  override predicate fromSource() { any() }

  /*abstract*/ override string toString() { result = "import" }
}

/**
 * A single-type-import declaration.
 *
 * For example, `import java.util.Set;`.
 */
class ImportType extends Import {
  ImportType() { imports(this,_,_,1) }

  /** The imported type. */
  RefType getImportedType() { imports(this,result,_,_) }

  override string toString() { result = "import " + this.getImportedType().toString() }
}

/**
 * A type-import-on-demand declaration that allows all accessible
 * nested types of a named type to be imported as needed.
 *
 * For example, `import java.util.Map.*;` imports
 * the nested type `java.util.Map.Entry` from the type
 * `java.util.Map`.
 */
class ImportOnDemandFromType extends Import {
  ImportOnDemandFromType() { imports(this,_,_,2) }

  /** The type from which accessible nested types are imported. */
  RefType getTypeHoldingImport() { imports(this,result,_,_) }

  /** An imported type. */
  NestedType getAnImport() { result.getEnclosingType() = this.getTypeHoldingImport() }

  override string toString() {
    result = "import " + this.getTypeHoldingImport().toString() + ".*"
  }
}

/**
 * A type-import-on-demand declaration that allows all accessible
 * types of a named package to be imported as needed.
 *
 * For example, `import java.util.*;`.
 */
class ImportOnDemandFromPackage extends Import {
  ImportOnDemandFromPackage() { imports(this,_,_,3) }

  /** The package from which accessible types are imported. */
  Package getPackageHoldingImport() { imports(this,result,_,_) }

  /** An imported type. */
  RefType getAnImport() { result.getPackage() = this.getPackageHoldingImport() }

  /** A printable representation of this import declaration. */
  override string toString() {
    result = "import " + this.getPackageHoldingImport().toString() + ".*"
  }
}

/**
 * A static-import-on-demand declaration, which allows all accessible
 * static members of a named type to be imported as needed.
 *
 * For example, `import static java.lang.System.*;`.
 */
class ImportStaticOnDemand extends Import {
  ImportStaticOnDemand() { imports(this,_,_,4) }

  /** The type from which accessible static members are imported. */
  RefType getTypeHoldingImport() { imports(this,result,_,_) }

  /** An imported type. */
  NestedType getATypeImport() { result.getEnclosingType() = this.getTypeHoldingImport() }

  /** An imported method. */
  Method getAMethodImport() { result.getDeclaringType() = this.getTypeHoldingImport() }

  /** An imported field. */
  Field getAFieldImport() { result.getDeclaringType() = this.getTypeHoldingImport() }

  /** A printable representation of this import declaration. */
  override string toString() {
    result = "import static " + this.getTypeHoldingImport().toString() + ".*"
  }
}

/**
 * A single-static-import declaration, which imports all accessible
 * static members with a given simple name from a type.
 *
 * For example, `import static java.util.Collections.sort;`
 * imports all the static methods named `sort` from the
 * class `java.util.Collections`.
 */
class ImportStaticTypeMember extends Import {
  ImportStaticTypeMember() { imports(this,_,_,5) }

  /** The type from which static members with a given name are imported. */
  RefType getTypeHoldingImport() { imports(this,result,_,_) }

  /** The name of the imported member(s). */
  override string getName() { imports(this,_,result,_) }

  /** An imported member. */
  Member getAMemberImport() {
    this.getTypeHoldingImport().getAMember() = result
    and result.getName() = this.getName() and result.isStatic()
  }

  /** An imported type. */
  NestedType getATypeImport() { result = this.getAMemberImport() }

  /** An imported method. */
  Method getAMethodImport() { result = this.getAMemberImport() }

  /** An imported field. */
  Field getAFieldImport() { result = this.getAMemberImport() }

  /** A printable representation of this import declaration. */
  override string toString() {
    result = "import static " + this.getTypeHoldingImport().toString()
             + "." + this.getName()
  }
}
