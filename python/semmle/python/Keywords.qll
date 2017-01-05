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

class KeyValuePair extends KeyValuePair_, DictDisplayItem {

    Location getLocation() {
        result = KeyValuePair_.super.getLocation()
    }

    string toString() {
        result = KeyValuePair_.super.toString()
    }

    /** Gets the value of this dictionary unpacking. */
    Expr getValue() {
        result = KeyValuePair_.super.getValue()
    }

    Scope getScope() {
        result = this.getValue().getScope()
    }

    AstNode getAChildNode() {
        result = this.getValue()
    }

}

/** A double-starred expression in a call or dict literal. */
class DictUnpacking extends DictUnpacking_, DictUnpackingOrKeyword, DictDisplayItem {

    Location getLocation() {
        result = DictUnpacking_.super.getLocation()
    }

    string toString() {
        result = DictUnpacking_.super.toString()
    }

    /** Gets the value of this dictionary unpacking. */
    Expr getValue() {
        result = DictUnpacking_.super.getValue()
    }

    Scope getScope() {
        result = this.getValue().getScope()
    }

    AstNode getAChildNode() {
        result = this.getValue()
    }

}

abstract class DictUnpackingOrKeyword extends DictItem, AstNode {


    Location getLocation() { none() }

    abstract Expr getValue();

    string toString() {
        none() 
    }

}

abstract class DictDisplayItem extends DictItem, AstNode {

    Location getLocation() { none() }

    abstract Expr getValue();

    string toString() {
        none() 
    }

}

class Keyword extends Keyword_, DictUnpackingOrKeyword  {

    Location getLocation() {
        result = Keyword_.super.getLocation()
    }

    string toString() {
        result = Keyword_.super.toString()
    }

    /** Gets the value of this keyword argument. */
    Expr getValue() {
        result = Keyword_.super.getValue()
    }

    Scope getScope() {
        result = this.getValue().getScope()
    }

    AstNode getAChildNode() {
        result = this.getValue()
    }

}

