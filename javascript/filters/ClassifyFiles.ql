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
 * @name Classify files
 * @description This query produces a list of all files in a snapshot
 *              that are classified as generated code, test code,
 *              externs declarations, library code or template code.
 * @kind file-classifier
 * @id js/file-classifier
 */

import semmle.javascript.GeneratedCode
import semmle.javascript.frameworks.Testing
import semmle.javascript.frameworks.Templating
import semmle.javascript.dependencies.FrameworkLibraries

/**
 * Holds if `e` may be caused by parsing a template file as plain HTML or JavaScript.
 *
 * Our heuristic is to check for the presence of a known template delimiter preceding
 * the error on the same line.
 */
predicate maybeCausedByTemplate(JSParseError e) {
  exists (File f | f = e.getFile() |
    // to check whether a known template delimiter precedes `e`, we take the prefix
    // of the line on which `e` occurs up to the start of `e` plus the maximum length
    // of a template delimiter (to account for the possibility that the parser gives
    // up somewhere half-way through the delimiter), and look for an occurrence of
    // a delimiter inside this string
    exists (string prefix, int errStart, int n |
      errStart = e.getLocation().getStartColumn() and
      n = min(int nn |
        nn = errStart + max(Templating::getADelimiter().length()) or
        // take the entire line if it is too short
        nn = e.getLine().length()
      ) and
      prefix = e.getLine().substring(0, n) and
      prefix.regexpMatch(Templating::getDelimiterMatchingRegexp())
    )
    or
    f.getAbsolutePath().regexpMatch("(?i).*\\btemplates?\\b.*")
  )
}


/**
 * Holds if `e` is an expression in the form `o.p1.p2.p3....pn`.
 */
private predicate isNestedDotExpr(DotExpr e) {
  e.getBase() instanceof VarAccess or
  isNestedDotExpr(e.getBase())
}

/**
 * Holds if `tl` only contains variable declarations and field reads.
 */
private predicate looksLikeExterns(TopLevel tl) {
  forex (Stmt s | s.getParent() = tl |
    exists (VarDeclStmt vds | vds = s |
      forall (VariableDeclarator vd | vd = vds.getADecl() | not exists(vd.getInit()))
    )
    or
    isNestedDotExpr(s.(ExprStmt).getExpr())
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
 *   - `"template"`: `f` contains template code.
 */
predicate classify(File f, string category) {
  isGenerated(f.getATopLevel()) and category = "generated"
  or
  exists (Test t | t.getFile() = f | category = "test")
  or
  (f.getATopLevel().isExterns() or looksLikeExterns(f.getATopLevel())) and category = "externs"
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
