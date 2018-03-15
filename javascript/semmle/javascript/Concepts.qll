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
 * Provides abstract classes representing generic concepts such as file system
 * access or system command execution, for which individual framework libraries
 * provide concrete subclasses.
 */

import javascript

/**
 * A data flow node that executes an operating system command,
 * for instance by spawning a new process.
 */
abstract class SystemCommandExecution extends DataFlow::Node {
  /** Gets an argument to this execution that specifies the command. */
  abstract DataFlow::Node getACommandArgument();
}

/**
 * A data flow node that performs a file system access.
 */
abstract class FileSystemAccess extends DataFlow::Node {
  /** Gets an argument to this file system access that is interpreted as a path. */
  abstract DataFlow::Node getAPathArgument();
}

/**
 * A data flow node that performs a database access.
 */
abstract class DatabaseAccess extends DataFlow::Node {
  /** Gets an argument to this database access that is interpreted as a query. */
  abstract DataFlow::Node getAQueryArgument();
}
