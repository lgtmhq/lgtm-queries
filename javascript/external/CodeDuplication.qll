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

import semmle.javascript.Files

private
string relativePath(File file) {
  result = file.getRelativePath().replaceAll("\\", "/")
}

// This relation is cached to prevent inlining for performance reasons
private cached
predicate tokenLocation(File file, int sl, int sc, int ec, int el, Copy copy, int index) {
  file = copy.sourceFile() and
  tokens(copy, index, sl, sc, ec, el)
}

class Copy extends @duplication_or_similarity
{
  private
  int lastToken() {
    result = max(int i | tokens(this, i, _, _, _, _) | i)
  }

  int tokenStartingAt(Location loc) {
    tokenLocation(loc.getFile(), loc.getStartLine(), loc.getStartColumn(),
      _, _, this, result)
  }

  int tokenEndingAt(Location loc) {
    tokenLocation(loc.getFile(), _, _,
      loc.getEndLine(), loc.getEndColumn(), this, result)
  }

  int sourceStartLine() {
    tokens(this, 0, result, _, _, _)
  }

  int sourceStartColumn() {
    tokens(this, 0, _, result, _, _)
  }

  int sourceEndLine() {
    tokens(this, this.lastToken(), _, _, result, _)
  }

  int sourceEndColumn() {
    tokens(this, this.lastToken(), _, _, _, result)
  }

  int sourceLines() {
    result = this.sourceEndLine() + 1 - this.sourceStartLine()
  }

  int getEquivalenceClass() {
    duplicateCode(this, _, result) or similarCode(this, _, result)
  }

  File sourceFile() {
    exists(string name |
      duplicateCode(this, name, _) or similarCode(this, name, _) |
      name.replaceAll("\\", "/") = relativePath(result)
    )
  }

  predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
      sourceFile().getPath() = filepath and
      startline = sourceStartLine() and
      startcolumn = sourceStartColumn() and
      endline = sourceEndLine() and
      endcolumn = sourceEndColumn()
  }

  string toString() { none() }

  Copy extendingBlock() {
    exists(File file, int sl, int sc, int ec, int el |
      tokenLocation(file, sl, sc, ec, el, this, _) and
      tokenLocation(file, sl, sc, ec, el, result, 0)) and
    this != result
  }
}

predicate similar_extension(SimilarBlock start1, SimilarBlock start2, SimilarBlock ext1, SimilarBlock ext2, int start, int ext) {
    start1.getEquivalenceClass() = start and
    start2.getEquivalenceClass() = start and
    ext1.getEquivalenceClass() = ext and
    ext2.getEquivalenceClass() = ext and
    start1 != start2 and
    (ext1 = start1 and ext2 = start2 or
     similar_extension(start1.extendingBlock(), start2.extendingBlock(), ext1, ext2, _, ext)
    )
}

predicate duplicate_extension(DuplicateBlock start1, DuplicateBlock start2, DuplicateBlock ext1, DuplicateBlock ext2, int start, int ext) {
    start1.getEquivalenceClass() = start and
    start2.getEquivalenceClass() = start and
    ext1.getEquivalenceClass() = ext and
    ext2.getEquivalenceClass() = ext and
    start1 != start2 and
    (ext1 = start1 and ext2 = start2 or
     duplicate_extension(start1.extendingBlock(), start2.extendingBlock(), ext1, ext2, _, ext)
    )
}


class DuplicateBlock extends Copy, @duplication
{
  string toString() {
    result = "Duplicate code: " + sourceLines() + " duplicated lines."
  }
}

class SimilarBlock extends Copy, @similarity
{
  string toString() {
    result = "Similar code: " + sourceLines() + " almost duplicated lines."
  }
}

private
predicate stmtInContainer(Stmt s, StmtContainer c) {
  s.getContainer() = c and
  not s instanceof BlockStmt
}

predicate duplicateStatement(StmtContainer container1, StmtContainer container2, Stmt stmt1, Stmt stmt2) {
     exists(int equivstart, int equivend, int first, int last |
        stmtInContainer(stmt1, container1) and
        stmtInContainer(stmt2, container2) and
        duplicateCoversStatement(equivstart, equivend, first, last, stmt1) and
        duplicateCoversStatement(equivstart, equivend, first, last, stmt2) and
        stmt1 != stmt2 and
        container1 != container2
    )
}

private
predicate duplicateCoversStatement(int equivstart, int equivend, int first, int last, Stmt stmt) {
  exists(DuplicateBlock b1, DuplicateBlock b2, Location loc |
    stmt.getLocation() = loc and
    first = b1.tokenStartingAt(loc) and
    last = b2.tokenEndingAt(loc) and
    b1.getEquivalenceClass() = equivstart and
    b2.getEquivalenceClass() = equivend and
    duplicate_extension(b1, _, b2, _, equivstart, equivend)
  )
}

private
predicate duplicateStatements(StmtContainer c1, StmtContainer c2, int duplicate, int total) {
  duplicate = strictcount(Stmt stmt | duplicateStatement(c1, c2, stmt, _)) and
  total = strictcount(Stmt stmt | stmtInContainer(stmt, c1))
}

/**
 * Find pairs of functions or toplevels that have more than 90% duplicate statements.
 */
predicate duplicateContainers(StmtContainer s, StmtContainer other, float percent) {
    exists(int total, int duplicate |
      duplicateStatements(s, other, duplicate, total) |
      percent = 100.0*duplicate/total and
      percent > 90.0
   )
}

private
predicate similarStatement(StmtContainer container1, StmtContainer container2, Stmt stmt1, Stmt stmt2) {
     exists(int start, int end, int first, int last |
        stmtInContainer(stmt1, container1) and
        stmtInContainer(stmt2, container2) and
        similarCoversStatement(start, end, first, last, stmt1) and
        similarCoversStatement(start, end, first, last, stmt2) and
        stmt1 != stmt2 and
        container1 != container2
    )
}

private
predicate similarCoversStatement(int equivstart, int equivend, int first, int last, Stmt stmt) {
  exists(SimilarBlock b1, SimilarBlock b2, Location loc |
    stmt.getLocation() = loc and
    first = b1.tokenStartingAt(loc) and
    last = b2.tokenEndingAt(loc) and
    b1.getEquivalenceClass() = equivstart and
    b2.getEquivalenceClass() = equivend and
    similar_extension(b1, _, b2, _, equivstart, equivend)
  )
}

private
predicate similarStatements(StmtContainer s1, StmtContainer s2, int similar, int total) {
  similar = strictcount(Stmt stmt | similarStatement(s1, s2, stmt, _)) and
  total = strictcount(Stmt stmt | stmtInContainer(stmt, s1))
}

/**
 * Find pairs of functions or toplevels that have more than 90% similar statements.
 */
predicate similarContainers(StmtContainer s, StmtContainer other, float percent) {
    exists(int total, int similar |
      similarStatements(s, other, similar, total) |
      percent = 100.0*similar/total and
      percent > 90.0
    )
}
