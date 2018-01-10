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

import semmle.code.cpp.File

/**
 * These two helper predicates are used to associate a unique integer with
 * each `@compilation`, for use in the `toString` method of `Compilation`.
 * These integers are not stable across trap imports, but stable across
 * runs with the same database.
 */
private predicate id(@compilation x, @compilation y) { x = y }
private predicate idOf(@compilation x, int y) = equivalenceRelation(id/2)(x, y)

/**
 * An invocation of the compiler. Note that more than one file may be
 * compiled per invocation. For example, this command compiles three
 * source files:
 *
 *   gcc -c f1.c f2.c f3.c
 *
 * Three things happen to each file during a compilation:
 *
 *   1. The file is compiled by a real compiler, such as gcc or VC.
 *   2. The file is parsed by Semmle's C++ front-end.
 *   3. The parsed representation is converted to database tables by
 *      Semmle's extractor.
 *
 * This class provides CPU and elapsed time information for steps 2 and 3,
 * but not for step 1.
 */
class Compilation extends @compilation {
  /** Gets a textual representation of this element. */
  string toString() {
    exists(int i
    | idOf(this, i) and
      result = "<compilation #" + i.toString() + ">")
  }

  /** Gets a file compiled during this invocation. */
  File getAFileCompiled() { result = getFileCompiled(_) }
  File getFileCompiled(int i) {
    compilation_compiling_files(this, i, result)
  }

  /**
   * Gets the amount of CPU time spent processing file number `i` in the C++
   * front-end.
   */
  float getFrontendCpuSeconds(int i) {
    compilation_time(this, i, 1, result)
  }

  /**
   * Gets the amount of elapsed time while processing file number `i` in the
   * C++ front-end.
   */
  float getFrontendElapsedSeconds(int i) {
    compilation_time(this, i, 2, result)
  }

  /**
   * Gets the amount of CPU time spent processing file number `i` in the
   * extractor.
   */
  float getExtractorCpuSeconds(int i) {
    compilation_time(this, i, 3, result)
  }

  /**
   * Gets the amount of elapsed time while processing file number `i` in the
   * extractor.
   */
  float getExtractorElapsedSeconds(int i) {
    compilation_time(this, i, 4, result)
  }

  /** Gets an argument passed to the extractor on this invocation. */
  string getAnArgument() { result = getArgument(_) }
  string getArgument(int i) {
    compilation_args(this, i, result)
  }

  /**
   * Gets the total amount of CPU time spent processing all the files in the
   * front-end and extractor.
   */
  float getTotalCpuSeconds() {
    compilation_finished(this, result, _)
  }

  /**
   * Gets the total amount of elapsed time while processing all the files in
   * the front-end and extractor.
   */
  float getTotalElapsedSeconds() {
    compilation_finished(this, _, result)
  }

  /**
   * Holds if the extractor terminated normally. Terminating with an exit
   * code indicating that an error occurred is considered normal
   * termination, but crashing due to something like a segfault is not.
   */
  predicate normalTermination() {
    compilation_finished(this, _, _)
  }
}
