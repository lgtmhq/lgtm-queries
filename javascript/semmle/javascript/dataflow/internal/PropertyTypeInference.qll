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
 * INTERNAL: Do not use directly; use `semmle.javascript.dataflow.TypeInference` instead.
 *
 * Provides classes implementing type inference for properties.
 */

import javascript
import semmle.javascript.dataflow.AbstractProperties
private import AbstractPropertiesImpl
private import AbstractValuesImpl

/**
 * Flow analysis for property reads, either explicitly (`x.p` or `x[e]`) or
 * implicitly.
 */
abstract class AnalyzedPropertyRead extends DataFlow::AnalyzedNode {
  /**
   * Holds if this property read may read property `propName` of a concrete value represented
   * by `base`.
   */
  pragma[nomagic]
  abstract predicate reads(AbstractValue base, string propName);

  override AbstractValue getAValue() {
    result = getASourceProperty().getAValue() or
    result = DataFlow::AnalyzedNode.super.getAValue()
  }

  override AbstractValue getALocalValue() {
    result = getASourceProperty().getALocalValue() or
    result = DataFlow::AnalyzedNode.super.getALocalValue()
  }

  /**
   * Gets an abstract property representing one of the concrete properties that
   * this read may refer to.
   */
  pragma[noinline]
  private AbstractProperty getASourceProperty() {
    exists (AbstractValue base, string prop | reads(base, prop) |
      result = MkAbstractProperty(base, prop)
    )
  }

  override predicate isIncomplete(DataFlow::Incompleteness cause) {
    super.isIncomplete(cause) or
    exists (AbstractValue base | reads(base, _) |
      base.isIndefinite(cause)
    )
  }
}

/**
 * Flow analysis for (non-numeric) property read accesses.
 */
private class AnalyzedPropertyAccess extends AnalyzedPropertyRead, DataFlow::ValueNode {
  DataFlow::AnalyzedNode baseNode;
  string propName;

  AnalyzedPropertyAccess() {
    astNode.(PropAccess).accesses(baseNode.asExpr(), propName) and
    not exists(propName.toInt()) and
    astNode instanceof RValue
  }

  override predicate reads(AbstractValue base, string prop) {
    base = baseNode.getALocalValue() and
    prop = propName
  }
}

/**
 * Holds if properties named `prop` should be tracked.
 */
pragma[noinline]
private predicate isTrackedPropertyName(string prop) {
  exists (MkAbstractProperty(_, prop))
}

/**
 * Flow analysis for property writes, including exports (which are
 * modeled as assignments to `module.exports`).
 */
abstract class AnalyzedPropertyWrite extends DataFlow::Node {
  /**
   * Holds if this property write assigns `source` to property `propName` of one of the
   * concrete objects represented by `baseVal`.
   */
  abstract predicate writes(AbstractValue baseVal, string propName, DataFlow::AnalyzedNode source);
}

/**
 * Flow analysis for property writes.
 */
private class AnalyzedExplicitPropertyWrite extends AnalyzedPropertyWrite, DataFlow::ValueNode {
  DataFlow::AnalyzedNode baseNode;
  string prop;
  DataFlow::AnalyzedNode rhs;

  AnalyzedExplicitPropertyWrite() {
    exists (PropWriteNode pwn | astNode = pwn |
      baseNode = pwn.getBase().analyze() and
      prop = pwn.getPropertyName() and
      rhs = pwn.getRhs().analyze()
    ) and
    isTrackedPropertyName(prop)
  }

  override predicate writes(AbstractValue baseVal, string propName, DataFlow::AnalyzedNode source) {
    baseVal = baseNode.getALocalValue() and
    propName = prop and
    source = rhs and
    shouldTrackProperties(baseVal)
  }
}

/**
 * Flow analysis for `arguments.callee`. We assume it is never redefined,
 * which is unsound in practice, but pragmatically useful.
 */
private class AnalyzedArgumentsCallee extends AnalyzedPropertyAccess {
  AnalyzedArgumentsCallee() {
    propName = "callee"
  }

  override AbstractValue getALocalValue() {
    exists (AbstractArguments baseVal | reads(baseVal, _) |
      result = TAbstractFunction(baseVal.getFunction())
    )
    or
    hasNonArgumentsBase(astNode) and result = super.getALocalValue()
  }
}

/**
 * Holds if `pacc` is of the form `e.callee` where `e` could evaluate to some
 * value that is not an arguments object.
 */
private predicate hasNonArgumentsBase(PropAccess pacc) {
  pacc.getPropertyName() = "callee" and
  exists (AbstractValue baseVal |
    baseVal = pacc.getBase().analyze().getALocalValue() and
    not baseVal instanceof AbstractArguments
  )
}
