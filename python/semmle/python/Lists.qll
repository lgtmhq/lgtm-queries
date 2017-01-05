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

/** A parameter list */
class ParameterList extends @py_parameter_list {

    Function getParent() {
        py_parameter_lists(this, result)
    }

    /** Gets a parameter */
    Parameter getAnItem() {
        /* Item can be a Name or a Tuple, both of which are expressions */
        py_exprs(result, _, this, _)
    }

    /** Gets the nth parameter */
    Parameter getItem(int index) {
        /* Item can be a Name or a Tuple, both of which are expressions */
        py_exprs(result, _, this, index)
    }

    string toString() {
        result = "ParameterList"
    }
}

/** A list of Comprehensions (for generating parts of a set, list or dictionary comprehension) */
class ComprehensionList extends ComprehensionList_ {

}

/** A list of expressions */
class ExprList extends ExprList_ {

}


library class DictItemList extends DictItemList_ {

}

library class DictItemListParent extends DictItemListParent_ {

}

/** A list of strings (the primitive type string not Bytes or Unicode) */
class StringList extends StringList_ {

}

/** A list of aliases in an import statement */
class AliasList extends AliasList_ {

}

