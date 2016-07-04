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

import default
import Collections

/** A reference type that extends a parameterization of `java.util.Map`. */
class MapType extends RefType {
  MapType() {
    exists(ParameterizedInterface coll |
      coll.getSourceDeclaration().hasQualifiedName("java.util", "Map") |
      this.hasSupertype*(coll)
    )
  }
  
  /** The type of keys stored in this map. */
  RefType getKeyType() {
    exists (GenericInterface map | map.hasQualifiedName("java.util", "Map") |
      indirectlyInstantiates(this, map, 0, result)
    )
  }
  
  /** The type of values stored in this map. */
  RefType getValueType() {
    exists (GenericInterface map | map.hasQualifiedName("java.util", "Map") |
      indirectlyInstantiates(this, map, 1, result)
    )
  }
}

/** A method declared in a map type. */
class MapMethod extends Method {
  MapMethod() {
    this.getDeclaringType() instanceof MapType
  }
  
  /** The type of keys of the map to which this method belongs. */
  RefType getReceiverKeyType() {
    result = ((MapType)this.getDeclaringType()).getKeyType()
  }
  
  /** The type of values of the map to which this method belongs. */
  RefType getReceiverValueType() {
    result = ((MapType)this.getDeclaringType()).getValueType()
  }
}

/** A method that mutates the map it belongs to. */
class MapMutator extends MapMethod {
  MapMutator() {
    this.getName().regexpMatch("(put.*|remove|clear)")
  }
}

/** The `size` method of `java.util.Map`. */
class MapSizeMethod extends MapMethod {
	MapSizeMethod() {
		this.hasName("size") and this.hasNoParameters()
	}
}

/** A method call that mutates a map. */
class MapMutation extends MethodAccess {
  MapMutation() {
    this.getMethod() instanceof MapMutator
  }
  
  predicate resultIsChecked() {
    not this.getParent() instanceof ExprStmt 
  }
}

/** A method that queries the contents of the map it belongs to without mutating it. */
class MapQueryMethod extends MapMethod {
  MapQueryMethod() {
    this.getName().regexpMatch("get|containsKey|containsValue|entrySet|keySet|values|isEmpty|size")
  }
}

/** A `new` expression that allocates a fresh, empty map. */
class FreshMap extends ClassInstanceExpr {
  FreshMap() {
    this.getConstructedType() instanceof MapType and
    this.getNumArgument() = 0 and
    not exists(this.getAnonymousClass())
  }
}

/**
 * A call to `Map.put(key, value)`.
 */
class MapPutCall extends MethodAccess {
  MapPutCall() {
    getCallee().(MapMethod).hasName("put")
  }

  Expr getKey() {
    result = getArgument(0)
  }

  Expr getValue() {
    result = getArgument(1)
  }
}
