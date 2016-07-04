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
import semmle.python.GuardedControlFlow

/** A major version of the Python interpreter, either 2 or 3 */
class Version extends int {

    Version() {
        this = 2 or this = 3
    }

}

private Object theSysVersionInfoTuple() {
    py_cmembers(theSysModuleObject(), "version_info", result)
}

/** Does f refer to sys.version_info? */
private predicate sys_version_info(ControlFlowNode f) {
     simple_points_to(f, theSysVersionInfoTuple())
}

Object source_tuple_value(TupleObject t, int n) {
    simple_points_to(t.getSourceElement(n), result)
}

/** Is f a comparison between version and value. `cmp` is the comparison when `version` is the lhs and `value` the rhs. */
private pragma [nomagic] predicate version_comparison(CompareNode f, ControlFlowNode version, string cmp, Object value) {
    exists(ControlFlowNode left, ControlFlowNode right, Cmpop op |
        f.operands(left, op, right) |
        (simple_points_to(left, version) or left = version) and
        simple_points_to(right, value) and
        cmp = op.getSymbol()
        or
        simple_points_to(left, value) and
        (simple_points_to(right, version) or right = version) and
        cmp = reversed(op)
    )
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

/** Whether f is a comparison between a version info tuple `version` and some object `value` */
private Version version_info_tuple(CompareNode f, ControlFlowNode version, string cmp, Object value) {
    version_comparison(f, version, cmp, value) and
    (
        /* sys.version_info */
        sys_version_info(version)
        or
        /* sys.version_info[:n] */
        sys_version_info(version.(SubscriptNode).getValue()) and
        version.(SubscriptNode).getIndex().getNode() instanceof Slice
    )
    and
    exists(Version v, TupleObject t |
        t = value and
        source_tuple_value(t, 0).(NumericObject).intValue() = v
        |
        // sys.version_info <= (2, x, y)
        result = v and v = 2 and (cmp = "<" or cmp = "<=") 
        or
        // sys.version_info >= (3, x, y)
        result = v and v = 3 and (cmp = ">" or cmp = ">=")
        or
        // sys.version_info < (3, 0, 0)
        result = 2 and v = 3 and cmp = "<" and 
        /* Tuples must be (3,) or (3,0) or (3,0,0) */
        (not exists(t.getSourceElement(1)) or source_tuple_value(t, 1).(NumericObject).intValue() = 0) and
        (not exists(t.getSourceElement(2)) or source_tuple_value(t, 2).(NumericObject).intValue() = 0)
    )
}

/** Whether f is a comparison between a major version info number `version` and some object `value` which implies that 
 * the major versions is the result */
private Version version_info_index(CompareNode f, ControlFlowNode version, string cmp, Object value) {
    /* sys.version_info[0] */
    version_comparison(f, version, cmp, value) and
    exists(NumericObject zero | zero.intValue() = 0 | simple_points_to(version.(SubscriptNode).getIndex(), zero))
    and
    simple_points_to(version.(SubscriptNode).getValue().(AttrNode).getObject("version_info"), theSysModuleObject())
    and
    exists(Version v |
        value.(NumericObject).intValue() = v |
        cmp = "==" and result = v
        or
        cmp = "!=" and result != v
    )
}

/** Whether f is a comparison between sys.hexversion, `version`, and some numeric object `value` which implies that 
 * the major versions is the result */
private Version hexversion(CompareNode f, ControlFlowNode version, string cmp, Object value) {
    version_comparison(f, version, cmp, value) and
    /* sys.hexversion */
    simple_points_to(version.(AttrNode).getObject("hexversion"), theSysModuleObject())
    and
    // What version? If sys.hexversion >= Ox03000000, then result = 3.
    exists(int hex, int three | 
        value.(NumericObject).intValue() = hex and 
        three = 50331648 /* Ox03000000 */ |
        // sys.hexversion < x where x <= three => sys.hexversion < three
        cmp = "<" and hex <= three and result = 2
        or
        // sys.hexversion <= x where x < three => sys.hexversion < three
        cmp = "<=" and hex < three and result = 2
        or
        // sys.hexversion > x where x >= three-1 => sys.hexversion >= three
        cmp = ">" and hex >= three-1 and result = 3
        or
        // sys.hexversion >= x where x >= three => sys.hexversion >= three
        cmp = ">=" and hex >= three and result = 3
    )
}

private predicate py_version(CompareNode f, Version v) {
    v = version_info_tuple(f, _, _, _)
    or
    v = version_info_index(f, _, _, _)
    or
    v = hexversion(f, _, _, _)
}

/** A test on the major version of the Python interpreter */
class VersionTest extends ControlFlowNode {

    VersionTest() {
        py_version(this, _)
    }

    Version getVersion() {
        py_version(this, result)
    }

}

/* Minimal points-to for version tests. Other, more general points-to depend on
 * this, so it must be self contained.
 */
private predicate points_to_version(ControlFlowNode f, Version version) {
    py_version(f, version)
    or
    attribute_version(f, version)
    or
    import_member_version(f, version)
    or
    exists(SsaVariable var | f = var.getAUse() | ssa_version(var, version))
}

private predicate ssa_const_bool(SsaVariable var, boolean b) {
    var.getDefinition().(DefinitionNode).getValue().getNode().(BooleanLiteral).booleanValue() = b
}

private predicate ssa_version(SsaVariable var, Version v) {
    exists(ConditionBlock guard, boolean sense, Version guardv |
        version_guard(guard, guardv) |
        exists(SsaVariable in1 | 
            in1 = var.getAPhiInput() |
            guard.controls(in1.getDefinition().getBasicBlock(), sense) and ssa_const_bool(in1, sense) and guardv = v
            or
            guard.controls(in1.getDefinition().getBasicBlock(), sense.booleanNot()) and ssa_const_bool(in1, sense) and guardv != v
        )
    )
    or
    points_to_version(var.getDefinition().(DefinitionNode).getValue(), v)
}

private predicate module_attribute_version(ModuleObject m, string name, Version v) {
    exists(SsaVariable var | var.getAUse() = m.getModule().getANormalExit() and var.getId() = name |
        ssa_version(var, v)
    )
}

private predicate attribute_version(AttrNode f, Version v) {
    f.isLoad() and
    exists(ModuleObject m, string name |
        simple_points_to(f.getObject(name), m) |
        module_attribute_version(m, name, v)
    )
}

private predicate import_member_version(ImportMemberNode f, Version v) {
    /* Three options here:
     * 1. The majority of imports.
     * 2. Importing from the package in an __init__ module, that is locally defined
     * 3. Importing from the package in an __init__ module, that is not locally defined
     */
    exists(string name, ModuleObject module, ImportMember im |
        im.getAFlowNode() = f and name = im.getName() and
        simple_points_to(f.getModule(name), module) |
        module_attribute_version(module, name, v)
    )
}

private predicate version_guard(ConditionBlock guard, Version version) {
    /* Is this a simple version test ( sys.version < (3,) ) */
    points_to_version(guard.getLastNode(), version)
}

/** A guard on the major version of the Python interpreter */
class VersionGuard extends ConditionBlock {

    VersionGuard() {
        version_guard(this, _)
    }

    int getVersion() {
        version_guard(this, result)
    }

}

private string os_name(StrConst s) {
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

private predicate get_platform_name(Expr e) {
    exists(Attribute a, Name n | a = e and n = a.getObject() |
        n.getId() = "sys" and a.getName() = "platform"
    )
        or
    exists(Call c, Attribute a, Name n | 
        c = e and a = c.getFunc() and n = a.getObject() |
        a.getName() = "system" and n.getId() = "platform"
    )
}

private predicate os_compare(ControlFlowNode f, string name) {
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

class OsTest extends Object {

    OsTest() {
        os_compare(this, _)
    }

    string getOs() {
        os_compare(this, result)
    }

}


class OsGuard extends ConditionBlock {

    OsGuard() {
        exists(OsTest t |
            simple_points_to(this.getLastNode(), t)
        )
    }

    string getOs() {
        exists(OsTest t |
            simple_points_to(this.getLastNode(), t) and result = t.getOs()
        )
    }

}


