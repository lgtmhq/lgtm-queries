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
import semmle.python.security.injection.Sql

/** A taint kind representing a django cursor object.
 */
class DjangoDbCursor extends DbCursor {

    DjangoDbCursor() {
        this = "django.db.connection.cursor"
    }

}

private Object theDjangoConnectionObject() {
    any(ModuleObject m | m.getName() = "django.db").getAttribute("connection") = result
}

/** A kind of taint source representing sources of django cursor objects.
 */
class DjangoDbCursorSource extends DbConnectionSource {

    DjangoDbCursorSource() {
        exists(AttrNode cursor |
            this.(CallNode).getFunction()= cursor and
            cursor.getObject("cursor").refersTo(theDjangoConnectionObject())
        )
    }

    string toString() {
        result = "django.db.connection.cursor"
    }

    predicate isSourceOf(TaintKind kind) { 
        kind instanceof DjangoDbCursor
    }

}
