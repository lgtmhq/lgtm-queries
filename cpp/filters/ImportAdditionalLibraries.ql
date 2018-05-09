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
 * @name (Import additional libraries)
 * @description This query produces no results but imports some libraries we
 *              would like to make available in the LGTM query console even
 *              if they are not used by any queries.
 * @kind file-classifier
 * @id cpp/lgtm/import-additional-libraries
 */

import cpp

import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.dataflow.DataFlow2
import semmle.code.cpp.dataflow.DataFlow3
import semmle.code.cpp.dataflow.DataFlow4
import semmle.code.cpp.dataflow.TaintTracking

from File f, string tag
where none()
select f, tag
