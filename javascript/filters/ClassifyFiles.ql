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
 * @name Classify files
 * @description This query produces a list of all files in a snapshot
 *              that are classified as generated code, test code or
 *              externs.
 * @kind file-classifier
 */

import semmle.javascript.GeneratedCode
import semmle.javascript.frameworks.Testing
import semmle.javascript.dependencies.FrameworkLibraries

/**
 * Gets a string that is known to be used as a template delimiter.
 */
string getATemplateDelimiter() {
  result = "<%" or result = "%>" or
  result = "{{" or result = "}}" or
  result = "{%" or result = "%}" or
  result = "<@" or result = "@>" or
  result = "<#" or result = "#>" or
  result = "{#" or result = "#}" or
  result = "[%" or result = "%]" or
  result = "<?" or result = "?>"
}

/**
 * Holds if `e` may be caused by parsing a template HTML file as plain HTML.
 *
 * Our heuristic is to check for the presence of a known template delimiter preceding
 * the error on the same line.
 */
predicate maybeCausedByTemplate(JSParseError e) {
  exists (HTMLFile f | f = e.getFile() |
    // to check whether a known template delimiter precedes `e`, we take the prefix
    // of the line on which `e` occurs up to the start of `e` plus the maximum length
    // of a template delimiter (to account for the possibility that the parser gives
    // up somewhere half-way through the delimiter), and look for an occurrence of
    // a delimiter inside this string
    exists (string prefix, string pattern, int errStart, int n |
      errStart = e.getLocation().getStartColumn() and
      n = min(int nn |
        nn = errStart + max(getATemplateDelimiter().length()) or
        // take the entire line if it is too short
        nn = e.getLine().length()
      ) and
      prefix = e.getLine().substring(0, n) and
      pattern = concat("\\Q" + getATemplateDelimiter() + "\\E", "|") |
      prefix.regexpMatch(".*(" + pattern + ").*")
    )
    or
    f.getAbsolutePath().regexpMatch("(?i).*\\btemplates?\\b.*")
  )
}

/**
 * Holds if `f` is classified as belonging to `category`.
 *
 * There are currently four categories:
 *   - `"generated"`: `f` contains generated or minified code;
 *   - `"test"`: `f` contains test code;
 *   - `"externs"`: `f` contains externs declarations;
 *   - `"library"`: `f` contains library code;
 *   - `"template"`: `f` contains as HTML template.
 */
predicate classify(File f, string category) {
  isGenerated(f.getATopLevel()) and category = "generated"
  or
  exists (Test t | t.getFile() = f | category = "test")
  or
  f.getATopLevel().isExterns() and category = "externs"
  or
  f.getATopLevel() instanceof FrameworkLibraryInstance and category = "library"
  or
  exists (JSParseError err | maybeCausedByTemplate(err) |
    f = err.getFile() and category = "template"
  )
}

from File f, string category
where classify(f, category)
select f, category
