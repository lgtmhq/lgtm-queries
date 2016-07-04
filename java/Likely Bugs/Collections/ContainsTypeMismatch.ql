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

/**
 * @name Type mismatch on contains
 * @description Calling 'Collection.contains' with an object of a different type
 *              than that of the collection is unlikely to return 'true'.
 * @kind problem
 * @problem.severity error
 */
import default
import semmle.code.java.Collections

/** A call to a method implementing `Collection.contains(java.lang.Object)`. */
class ContainsCall extends MethodAccess {
	ContainsCall() {
		exists(CollectionMethod cm | cm = this.getCallee() |
			cm.getSignature() = "contains(java.lang.Object)"
		)
	}
	
	/** The type of elements of the collection on which `contains` is invoked. */
	RefType getReceiverElementType() {
		result = getCallee().(CollectionMethod).getReceiverElementType()
	}
	
	/** The type of the (only) argument to `contains`, boxed if it is a primitive. */
	RefType getArgumentType() {
		exists(Type argtp | argtp = this.getArgument(0).getType() |
			result = argtp or result = argtp.(PrimitiveType).getBoxedType()
		)
	}
}

from ContainsCall ma, RefType typearg, RefType argtype
where typearg = ma.getReceiverElementType().getSourceDeclaration() and
			argtype = ma.getArgumentType() and
      not haveIntersection(typearg, argtype)
select ma, "Actual argument type " + argtype.getName() 
           + " is incompatible with expected argument type " + typearg.getName() + "."
