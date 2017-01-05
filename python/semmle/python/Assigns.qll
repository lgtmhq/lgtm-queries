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

/** 
 * In order to handle data flow and other analyses efficiently the extractor transforms various statements which perform binding in assignments.
 * These classes provide a wrapper to provide a more 'natural' interface to the syntactic elements transformed to assignments.
 */

import python


/** An assignment statement */
class AssignStmt extends Assign {

    AssignStmt() {
        not this instanceof FunctionDef and not this instanceof ClassDef
    }

    string toString() {
        result = "AssignStmt"
    }
}
