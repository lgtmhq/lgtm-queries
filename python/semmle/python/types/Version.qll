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

import python
import semmle.python.GuardedControlFlow
private import semmle.python.pointsto.Final

/** A major version of the Python interpreter, either 2 or 3 */
class Version extends int {

    Version() {
        this = 2 or this = 3
    }

}

Object theSysVersionInfoTuple() {
    py_cmembers_versioned(theSysModuleObject(), "version_info", result, major_version().toString())
}

Object theSysHexVersionNumber() {
    py_cmembers_versioned(theSysModuleObject(), "hexversion", result, major_version().toString())
}

Object theSysVersionString() {
    py_cmembers_versioned(theSysModuleObject(), "version", result, major_version().toString())
}


string reversed(Cmpop op) {
    op instanceof Lt and result = ">"
    or
    op instanceof Gt and result = "<"
    or
    op instanceof GtE and result = "<="
    or
    op instanceof LtE and result = ">="
    or
    op instanceof Eq and result = "=="
    or
    op instanceof NotEq and result = "!="
}


/** DEPRECATED: 
 *  A test on the major version of the Python interpreter 
 * */
class VersionTest extends @py_flow_node {

    string toString() {
        result = "VersionTest"
    }

    VersionTest() {
        FinalPointsTo::version_const(this, _, _)
    }

    predicate isTrue() {
        FinalPointsTo::version_const(this, _, true)
    }

    AstNode getNode() {
        result = this.(ControlFlowNode).getNode()
    }

}

/** A guard on the major version of the Python interpreter */
class VersionGuard extends ConditionBlock {

    VersionGuard() {
        exists(VersionTest v |
            FinalPointsTo::points_to(this.getLastNode(), _, v, _, _) or
            FinalPointsTo::points_to(this.getLastNode(), _, _, _, v)
        )
    }

    predicate isTrue() {
        exists(VersionTest v |
            v.isTrue() |
            FinalPointsTo::points_to(this.getLastNode(), _, v, _, _) or
            FinalPointsTo::points_to(this.getLastNode(), _, _, _, v)
        )
    }

}

string os_name(StrConst s) {
    exists(string t | 
        t = s.getText() |
        t = "Darwin" and result = "darwin"
        or
        t = "Windows" and result = "win32"
        or
        t = "Linux" and result = "linux"
        or
        not t = "Darwin" and not t = "Windows" and not t = "Linux" and result = t
    )
}

predicate get_platform_name(Expr e) {
    exists(Attribute a, Name n | a = e and n = a.getObject() |
        n.getId() = "sys" and a.getName() = "platform"
    )
        or
    exists(Call c, Attribute a, Name n | 
        c = e and a = c.getFunc() and n = a.getObject() |
        a.getName() = "system" and n.getId() = "platform"
    )
}

predicate os_compare(ControlFlowNode f, string name) {
    exists(Compare c, Expr l, Expr r, Cmpop op |
        c = f.getNode() and
        l = c.getLeft() and
        r = c.getComparator(0) and
        op = c.getOp(0) |
        (op instanceof Eq or op instanceof Is)
        and
        ( get_platform_name(l) and name = os_name(r)
          or
          get_platform_name(r) and name = os_name(l)
        )
    )
}

class OsTest extends @py_flow_node {

    OsTest() {
        os_compare(this, _)
    }

    string getOs() {
        os_compare(this, result)
    }

    string toString() {
        result = "OsTest"
    }

    AstNode getNode() {
        result = this.(ControlFlowNode).getNode()
    }

}


class OsGuard extends ConditionBlock {

    OsGuard() {
        exists(OsTest t |
            FinalPointsTo::points_to(this.getLastNode(), _, theBoolType(), t, _)
        )
    }

    string getOs() {
        exists(OsTest t |
            FinalPointsTo::points_to(this.getLastNode(), _, theBoolType(), t, _) and result = t.getOs()
        )
    }

}


