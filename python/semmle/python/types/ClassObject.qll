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
import semmle.python.SelfAttribute


private predicate is_c_metaclass(Object o) {
    py_special_objects(o, "type")
    or
    exists(Object sup | py_cmembers(o, ".super.", sup) and is_c_metaclass(sup))
}


library class ObjectOrCfg extends @py_object {

    string toString() {
        /* Not to be displayed */
        none() 
    }

}

/** A class whose instances represents Python classes.
    Instances of this class represent either builtin classes 
    such as `list` or `str`, or program-defined Python classes 
    present in the source code.
     
    Generally there is a one-to-one mapping between classes in 
    the Python program and instances of this class in the database. 
    However, that is not always the case. For example, dynamically 
    generated classes may share a single QL class instance.
    Also the existence of a class definition in the source code 
    does not guarantee that such a class will ever exist in the 
    running program.
*/
class ClassObject extends Object {

    ClassObject() {
        this.getOrigin() instanceof ClassExpr or
        py_cobjecttypes(_, this) or
        exists(Object meta | py_cobjecttypes(this, meta) and is_c_metaclass(meta)) or
        py_special_objects(this, "_semmle_unknown_type")
    }

    /** Gets the short (unqualified) name of this class */
    string getName() {
        /* Remove 'exceptions.' prefix from class names as Python programmers are more familiar 
         * with 'Exception' than 'exceptions.Exception'.
         */
        exists(string name | py_cobjectnames(this, name) and result = name.regexpReplaceAll("^exceptions\\.", ""))
        or
        result = this.getPyClass().getName()
    }

    /** Gets the qualified name for this class.
     * Should return the same name as the `__qualname__` attribute on classes in Python 3.
     */
    string getQualifiedName() {
        py_cobjectnames(this, _) and result = this.getName()
        or
        result = this.getPyClass().getQualifiedName()
    }

    /** Gets the nth base class of this class */
    ClassObject getBaseType(int n) {
        exists(ClassExpr cls | this.getOrigin() = cls |
            /* To avoid negative recursion, we have to use intermediate_points_to rather than full points. */
            intermediate_points_to(cls.getBase(n).getAFlowNode(), result, _)
            or
            this.isNewStyle() and not exists(cls.getBase(0)) and result = theObjectType() and n = 0
        )
        or
        /* The extractor uses the special name ".super." to indicate the super class of a builtin class */
        py_cmembers(this, ".super.", result) and n = 0
    }

    /** Gets a base class of this class */
    ClassObject getABaseType() {
        result = this.getBaseType(_)
    }

    /** Whether this class has a base class */
    private predicate hasABase() {
        exists(ClassExpr cls | this.getOrigin() = cls | exists(cls.getABase()))
    }

    /** Don't expose this predicate as it is easy to misuse if not thinking about multiple inheritance, old-style 
       classes. Use nextInMro() instead. */
    private ClassObject getImmediateSuperType() {
        result = this.getBaseType(_)
    }

    /** Gets a super class of this class (includes transitive super classes) */
    cached ClassObject getASuperType() {
        result = this.getImmediateSuperType+()
    }

    /** Gets a super class of this class (includes transitive super classes) or this class */
    cached ClassObject getAnImproperSuperType() {
        result = this.getImmediateSuperType*()
    }

    /** Whether this class is a new style class. 
        A new style class is one that implicitly or explicitly inherits from `object`. */
    cached predicate isNewStyle() {
        this.newStyle()
        or
        this.getABaseType().isNewStyle()
    }

    private predicate newStyle() {
        this.isC()
        or
        major_version() >= 3
        or
        exists(this.declaredMetaClass())
    }

    /** Whether this class is a legal exception class. 
     *  What constitutes a legal exception class differs between major versions */
    predicate isLegalExceptionType() {
        not this.isNewStyle() or
        this.getAnImproperSuperType() = theBaseExceptionType()
        or
        major_version() = 2 and this = theTupleType()
    }

    /** Gets the scope associated with this class, if it is not a builtin class */
    Class getPyClass() {
        result.getClassObject() = this
    }

    /** Returns an attribute declared on this class (not on a super-class) */
    cached Object declaredAttribute(string name) {
        this.declaredAttribute(name, result, _)
    }

    private predicate declaredAttribute(string name, Object obj, ObjectOrCfg origin) {
        /* TO DO -- This needs to handle class decorators */
        this.getImportTimeScope().objectReachingExit(name, obj, origin.(ControlFlowNode))
        or
        py_cmembers(this, name, obj) and this.declaresAttribute(name) and not name = ".super." and origin = obj
    }

    /** Returns an attribute declared on this class (not on a super-class) */
    cached predicate declaresAttribute(string name) {
        this.getImportTimeScope().definesName(name)
        or
        not name = ".super." and
        exists(Object o |
            py_cmembers(this, name, o) and 
            not exists(ClassObject sup | py_cmembers(this, ".super.", sup) and 
                py_cmembers(sup, name, o)
            )
        )
    }

    /** Returns an attribute as it would be when looked up at runtime on this class.
      Will include attributes of super-classes */
    Object lookupAttribute(string name) {
        this.lookupAttributeInternal(this, name, result, _)
    }

    /** Looks up an attribute by searching this class' MRO starting at `start` */
    Object lookupMro(ClassObject start, string name) {
        this.lookupAttributeInternal(start, name, result, _)
    }

    /** Whether the named attribute refers to the object and origin */
    predicate attributeRefersTo(string name, Object obj, ControlFlowNode origin) {
        this.lookupAttributeInternal(this, name, obj, origin.(ObjectOrCfg))
    }

    /** Helper for `lookupAttribute`, `lookupMro` and `attributeRefersTo`.
     * Looks up the attribute `name` in this class, starting at `start`.  */
    private cached predicate lookupAttributeInternal(ClassObject start, string name, Object object, ObjectOrCfg origin) {
        /* Choose attribute from superclass declared closest to, but not before, `start` in MRO. */
        exists(int i, int j |
            start = this.getMroItem(i) and
            j = min(int k | k = this.declaringClassIndex(name) and k >= i) and
            this.getMroItem(j).declaredAttribute(name, object, origin)
        )
    }

    private int declaringClassIndex(string name) {
        this.getMroItem(result).declaresAttribute(name)
    }

    /** Whether this class has a attribute named `name`, either declared or inherited.*/
    cached predicate hasAttribute(string name) {
        this.declaresAttribute(name) or this.getASuperType().declaresAttribute(name)
        or
        this.getMetaClass().assignedInInit(name)
    }

    /** Whether it is impossible to know all the attributes of this class. Usually because it is
        impossible to calculate the full class hierarchy or because some attribute is too dynamic. */
    predicate unknowableAttributes() {
        /* True for a class with undeterminable superclasses, unanalysable metaclasses, or other confusions */
        this.failedInference()
        or
        this.explicitMetaclass().failedInference()
        or
        this.getABaseType().unknowableAttributes()
    }

    private predicate hasExplicitMetaclass() {
        exists(this.declaredMetaClass())
        or
        py_cobjecttypes(this, _)
        or
        six_add_metaclass(_, this, _)
    }

    private ClassObject explicitMetaclass() {
        intermediate_points_to(this.declaredMetaClass(), result, _)
        or
        py_cobjecttypes(this, result) and is_c_metaclass(result)
        or
        exists(ControlFlowNode meta |
            six_add_metaclass(_, this, meta) and
            import_time_points_to(meta, result, _)
        )
    }

    /** Gets the class of this object for simple cases, namely constants, functions, comprehensions and built-in objects. 
     *  This exists primarily for internal use. Use getAnInferredType() instead.
     */
    ClassObject simpleClass() {
        result = this.implicitSimpleClass()
        or
        result = this.explicitSimpleClass()
    }

    private ClassObject explicitSimpleClass() {
        simple_points_to(this.declaredMetaClass(), result)
        or
        py_cobjecttypes(this, result)
    }

    private ClassObject implicitSimpleClass() {
        this.approxHasTypeType() and result = theTypeType()
        or
        this.approxHasClassType() and result = theClassType()
    }

    private predicate hasTypeType() {
        not this.hasExplicitMetaclass() and this.isNewStyle()
    }

    private predicate hasClassType() {
      not this.hasExplicitMetaclass() and not this.isNewStyle()
    }

    private ClassObject inheritedMetaClass() {
        result = this.getASuperType().explicitMetaclass()
        and
        forall(ClassObject possibleMeta | 
            possibleMeta = this.getASuperType().explicitMetaclass() |
            result.getAnImproperSuperType() = possibleMeta
        )
    }

    /** Gets the metaclass for this class */
    ClassObject getMetaClass() {
        not this.failedInference() and
        (
            this.hasExplicitMetaclass() and result = this.explicitMetaclass()
            or
            /* Meta class determination http://gnosis.cx/publish/programming/metaclass_2.html */
            not this.hasExplicitMetaclass() and result = this.inheritedMetaClass()
            or
            /* No declared or inherited metaclass */
            not this.hasExplicitMetaclass() and not exists(this.getASuperType().explicitMetaclass())
            and
            (
              this.hasTypeType() and result = theTypeType()
              or
              this.hasClassType() and result = theClassType()
            )
        )
    }

    private predicate approxHasTypeType() {
        not exists(declaredMetaClass()) and (major_version() >= 3 or hasABase())
        and
        not py_cobjecttypes(this, _)
    }

    private predicate approxHasClassType() {
        not exists(declaredMetaClass()) and major_version() < 3 and not hasABase()
        and
        not py_cobjecttypes(this, _)
    }

    /* Whether this class is abstract. */
    predicate isAbstract() {
        this.explicitMetaclass() = theAbcMetaClassObject()
    }

    private ControlFlowNode declaredMetaClass() {
        result = this.getPyClass().getMetaClass().getAFlowNode()
    }

    /** Has type inference failed to compute the full class hierarchy for this class for the reason given. */ 
    predicate failedInference(string reason) {
        strictcount(this.getPyClass().getADecorator()) > 1 and reason = "Multiple decorators"
        or
        exists(this.getPyClass().getADecorator()) and not six_add_metaclass(_, this, _) and reason = "Decorator not understood"
        or
        exists(int i | exists(((ClassExpr)this.getOrigin()).getBase(i)) and not exists(this.getBaseType(i)) and reason = "Missing base " + i)
        or
        exists(this.getPyClass().getMetaClass()) and not exists(this.explicitMetaclass()) and reason = "Failed to infer metaclass"
        or
        exists(int i | this.getBaseType(i).failedInference() and reason = "Failed inference for base class at position " + i)
        or
        exists(int i | strictcount(this.getBaseType(i)) > 1 and reason = "Multiple bases at position " + i)
    }

    /** Has type inference failed to compute the full class hierarchy for this class */ 
    predicate failedInference() {
        this.failedInference(_)
    }

    /** Gets an object which is the sole instance of this class, if this class is probably a singleton.
     *  Note the 'probable' in the name; there is no guarantee that this class is in fact a singleton.
     *  It is guaranteed that getProbableSingletonInstance() returns at most one Object for each ClassObject. */
     Object getProbableSingletonInstance() {
        exists(ControlFlowNode use, Expr origin |
            use.refersTo(result, this, origin.getAFlowNode())
            |
            this.hasStaticallyUniqueInstance()
            and
            /* Ensure that original expression will be executed only one. */
            origin.getScope() instanceof ImportTimeScope and
            not exists(Expr outer | outer.getASubExpression+() = origin)
        )
        or
        this = theNoneType() and result = theNoneObject()
    }

    /** This class is only instantiated at one place in the code */
    private  predicate hasStaticallyUniqueInstance() {
        strictcount(Object instances | runtime_points_to(_, instances, this, _)) = 1
    }

    private ImportTimeScope getImportTimeScope() {
        result = this.getPyClass()
    }

    string toString() {
        /* _semmle_unknown_type should be invisible */
        this.isC() and not py_special_objects(this, "_semmle_unknown_type") and result = "builtin-class " + this.getName()
        or
        not this.isC() and result = "class " + this.getName()
    }

    /* Method Resolution Order */

    /** Returns the next class in the MRO of 'this' after 'sup' */
     ClassObject nextInMro(ClassObject sup) {
        exists(int i |
            sup = this.getMroItem(i) and
            result = this.getMroItem(i+1)
        )
    }

    /** The MRO for this class. ClassObject `sup` occurs at `index` in the list of classes. 
     * `this` has an index of `1`, the next class in the MRO has an index of `2`, and so on.
     */
    ClassObject getMroItem(int index) {
        /* Collapse the sparse array into a dense one */
        exists(int idx | this.mroSparse(result, idx) |
            idx = rank[index](int i, ClassObject s | this.mroSparse(s, i) | i) 
        )
    }

    /** Eliminate duplicates classes from  the (super-class, index) tuples of depthFirstIndexed.
     * Old-style classes perform depth-first search (like C++), so we eliminate all duplicates
     * but the left-most (lowest index).
     * New-style classes use the C3 MRO, so we eliminate all duplicates but the right-most.
     */
    private predicate mroSparse(ClassObject sup, int index) {
        if this.isNewStyle() then (
            this.depthFirstIndexed(sup, index) and
            not exists(int after | this.depthFirstIndexed(sup, after) and after > index)
        ) else (
            this.depthFirstIndexed(sup, index) and
            not exists(int before | this.depthFirstIndexed(sup, before) and before < index)
        )
    }

    /** Index all super-classes using depth-first search, 
     * numbering parent nodes before their children */
    private predicate depthFirstIndexed(ClassObject sup, int index) {
        not this.hasIllegalBases() and this.getAnImproperSuperType() = sup and
        (
            sup = this and index = 0
            or
            exists(ClassObject base, int base_offset, int sub_index |
                base = this.getABaseType() and 
                this.baseOffset(base, base_offset) and
                base.depthFirstIndexed(sup, sub_index) and
                index = base_offset + sub_index + 1
            )
        )
    }

    /** An index for the base class in the mro such that the index for superclasses of the base
     * class are guaranteed not to clash with the superclasses of other base classes.  */
    private predicate baseOffset(ClassObject base, int index) {
        exists(int n |
            this.getBaseType(n) = base |
            index = sum(ClassObject left_base |
                exists(int i | left_base = this.getBaseType(i) and i < n) |
                count (left_base.getAnImproperSuperType())
            )
        )
    }

    /** This class has duplicate base classes */
    predicate hasDuplicateBases() {
        exists(ClassObject base, int i, int j | i != j and base = this.getBaseType(i) and base = this.getBaseType(j))
    }

    private predicate hasIllegalBases() {
        this.hasDuplicateBases() or this.getABaseType().getASuperType() = this or this.getABaseType() = this
    }

    /** Whether this class is an iterable. */
    predicate isIterable() {
        this.hasAttribute("__iter__") or this.hasAttribute("__getitem__")
    }

    /** Whether this class is an iterator. */
    predicate isIterator() {
        this.hasAttribute("__iter__") and 
        (major_version() = 3 and this.hasAttribute("__next__")
         or   
         /* Because 'next' is a common method name we need to check that an __iter__
          * method actually returns this class. This is not needed for Py3 as the
          * '__next__' method exists to define a class an an iterator.
          */
         major_version() = 2 and this.hasAttribute("next") and 
         exists(ClassObject other, FunctionObject iter | 
            other.declaredAttribute("__iter__") = iter |
            iter.getAnInferredReturnType() = this
         )
        )
        or
        /* This will be redundant when we have C class information */
        this = theGeneratorType()
    }

    /** Whether this class is an improper subclass of the other class.
     *  True if this is a sub-class of other or this is the same class as other.
     *
     *  Equivalent to the Python builtin function issubclass().
     */
    predicate isSubclassOf(ClassObject other) {
        this = other or this.getASuperType() = other
    }

    /** Synonymous with isContainer(), retained for backwards compatibility. */
    predicate isCollection() {
        this.isContainer()
    }

    /** Whether this class is a container(). That is, does it have a __getitem__ method.*/
    predicate isContainer() {
        exists(this.lookupAttribute("__getitem__"))
    }

    /** Whether this class is a mapping. */
    predicate isMapping() {
        exists(this.lookupAttribute("__getitem__"))
        and
        not this.isSequence()
    }

    /** Whether this class is probably a sequence. */
    predicate isSequence() {
        /* To determine whether something is a sequence or a mapping is not entirely clear,
         * so we need to guess a bit. 
         */
        this.getAnImproperSuperType() = theTupleType()
        or
        this.getAnImproperSuperType() = theListType()
        or
        this.getAnImproperSuperType() = theRangeType()
        or
        this.getAnImproperSuperType() = theBytesType()
        or
        this.getAnImproperSuperType() = theUnicodeType()
        or
        /* Does this inherit from abc.Sequence? */
        this.getASuperType().getName() = "Sequence"
        or
        /* Does it have an index or __reversed__ method? */
        this.isContainer() and
        (
            this.hasAttribute("index") or 
            this.hasAttribute("__reversed__")
        )
    }

    predicate isCallable() {
        this.hasAttribute("__call__")
    }

    predicate isContextManager() {
        this.hasAttribute("__enter__") and this.hasAttribute("__exit__")
    }

    predicate assignedInInit(string name) {
        exists(FunctionObject init | init = this.lookupAttribute("__init__") |
            attribute_assigned_in_method(init, name)
        )
    }

    /** Whether this class is unhashable */
    predicate unhashable() {
        this.lookupAttribute("__hash__") = theNoneObject()
        or
        ((FunctionObject)this.lookupAttribute("__hash__")).neverReturns() 
    }

    /** Whether this class is a descriptor */
    predicate isDescriptorType() {
        this.hasAttribute("__get__") 
    }

    /** Whether this class is an overriding descriptor */
    predicate isOverridingDescriptorType() {
        this.hasAttribute("__get__") and this.hasAttribute("__set__") 
    }

}

/* INTERNAL -- Do not use */
predicate six_add_metaclass(CallNode decorator_call, ClassObject decorated, ControlFlowNode metaclass) {
    exists(CallNode decorator, FunctionObject six_meta |
        decorator_call.getArg(0) = decorated and
        decorator = decorator_call.getFunction() |
        import_time_points_to(decorator.getFunction(), six_meta, _) and
        decorator.getArg(0) = metaclass and
        exists(ModuleObject six |
            six.getName() = "six" and
            six.getAttribute("add_metaclass") = six_meta
        )
    )
}

/** The 'str' class. This is the same as the 'bytes' class for
  * Python 2 and the 'unicode' class for Python 3 */
ClassObject theStrType() {
    if major_version() = 2 then
        result = theBytesType()
    else
        result = theUnicodeType()
}

private
ModuleObject theAbcModuleObject() {
    exists(Module sys_module | sys_module.getName() = "abc" and
           result.getOrigin() = sys_module)
}

private
Object theAbcMetaClassObject() {
    result = theAbcModuleObject().getAttribute("ABCMeta")
}

/* Common builtin classes */

/** The built-in class NoneType*/
ClassObject theNoneType() {
    py_special_objects(result, "NoneType")
}

/** The built-in class 'bool' */
ClassObject theBoolType() {
    py_special_objects(result, "bool")
}

/** The builtin class 'type' */
ClassObject theTypeType() {
    py_special_objects(result, "type")
}

/** The builtin object ClassType (for old-style classes) */
ClassObject theClassType() {
    py_special_objects(result, "ClassType")
}

/** The builtin object InstanceType (for old-style classes) */
ClassObject theInstanceType() {
    py_special_objects(result, "InstanceType")
}

/** The builtin class 'tuple' */
ClassObject theTupleType() {
    py_special_objects(result, "tuple")
}

/** The builtin class 'int' */
ClassObject theIntType() {
    py_special_objects(result, "int")
}

/** The builtin class 'long' (Python 2 only) */
ClassObject theLongType() {
    py_special_objects(result, "long")
}

/** The builtin class 'float' */
ClassObject theFloatType() {
    py_special_objects(result, "float")
}

/** The builtin class 'complex' */
ClassObject theComplexType() {
    py_special_objects(result, "complex")
}

/** The builtin class 'object' */
ClassObject theObjectType() {
    py_special_objects(result, "object")
}

/** The builtin class 'list' */
ClassObject theListType() {
    py_special_objects(result, "list")
}

/** The builtin class 'dict' */

ClassObject theDictType() {
    py_special_objects(result, "dict")
}

/** The builtin class 'Exception' */

ClassObject theExceptionType() {
    py_special_objects(result, "Exception")
}

/** The builtin class for unicode. unicode in Python2, str in Python3 */
ClassObject theUnicodeType() {
    py_special_objects(result, "unicode")
}

/** The builtin class '(x)range' */
ClassObject theRangeType() {
    result = builtin_object("xrange")
    or
    major_version() = 3 and result = builtin_object("range")
}

/** The builtin class for bytes. str in Python2, bytes in Python3 */
ClassObject theBytesType() {
    py_special_objects(result, "bytes")
}

/** The builtin class 'set' */
ClassObject theSetType() {
    py_special_objects(result, "set")
}

/** The builtin class 'property' */
ClassObject thePropertyType() {
    py_special_objects(result, "property")
}

/** The builtin class 'BaseException' */
ClassObject theBaseExceptionType() {
    py_special_objects(result, "BaseException")
}

/** The class of builtin-functions */
ClassObject theBuiltinFunctionType() {
    py_special_objects(result, "BuiltinFunctionType")
}

/** The class of Python functions */
ClassObject thePyFunctionType() {
    py_special_objects(result, "FunctionType")
}

/** The builtin class 'classmethod' */
ClassObject theClassMethodType() {
    py_special_objects(result, "ClassMethod")
}

/** The builtin class 'staticmethod' */
ClassObject theStaticMethodType() {
    py_special_objects(result, "StaticMethod")
}

/** The class of modules */
ClassObject theModuleType() {
    py_special_objects(result, "ModuleType")
}

/** The class of generators */
ClassObject theGeneratorType() {
    py_special_objects(result, "generator")
}

/** The builtin class 'TypeError' */
ClassObject theTypeErrorType() {
    py_special_objects(result, "TypeError")
}

/** The builtin class 'AttributeError' */
ClassObject theAttributeErrorType() {
    py_special_objects(result, "AttributeError")
}

/** The builtin class 'KeyError' */
ClassObject theKeyErrorType() {
    py_special_objects(result, "KeyError")
}

/** The builtin class 'IOError' */
ClassObject theIOErrorType() {
    py_special_objects(result, "IOError")
}

/** The builtin class of bound methods */
ClassObject theBoundMethodType() {
     py_special_objects(result, "MethodType")
}

/** The builtin class of builtin properties */
ClassObject theGetSetDescriptorType() {
     py_special_objects(result, "GetSetDescriptorType")
}

/** The method descriptor class */
ClassObject theMethodDescriptorType() {
    py_special_objects(result, "MethodDescriptorType")
}

/** The class of builtin properties */
ClassObject theBuiltinPropertyType() {
    /* This is CPython specific */ 
    result.isC() and
    result.getName() = "getset_descriptor"
}

/** The builtin class 'super' */
ClassObject theSuperType() {
    result = builtin_object("super")
}

/** The builtin class 'StopIteration' */
ClassObject theStopIterationType() {
    result = builtin_object("StopIteration")
}
