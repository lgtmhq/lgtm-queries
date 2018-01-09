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

/** Retained for backwards compatibility use ClassObject.isIterator() instead. */
predicate is_iterator(ClassObject c) {
    c.isIterator()
}

/** Retained for backwards compatibility use ClassObject.isIterable() instead. */
predicate is_iterable(ClassObject c) {
    c.isIterable()
}

/** Retained for backwards compatibility use ClassObject.isCollection() instead. */
predicate is_collection(ClassObject c) {
    c.isCollection()
}

/** Retained for backwards compatibility use ClassObject.isMapping() instead. */
predicate is_mapping(ClassObject c) {
    c.isMapping()
}

/** Retained for backwards compatibility use ClassObject.isSequence() instead. */
predicate is_sequence(ClassObject c) {
    c.isSequence()
}

/** Retained for backwards compatibility use ClassObject.isContextManager() instead. */
predicate is_context_manager(ClassObject c) {
    c.isContextManager()
}
