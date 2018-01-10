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
                name.replaceAll("\\", "/") = relativePath(result))
    }

    predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
        sourceFile().getName() = filepath and
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

Stmt lowest_level_statement(Scope s) {
    s.contains(result) and not exists(Stmt inner | s.contains(inner))
}

predicate duplicateStatement(Scope scope1, Scope scope2, Stmt stmt1, Stmt stmt2) {
    exists(int equivstart, int equivend, int first, int last |
        scope1.contains(stmt1) and
        scope2.contains(stmt2) and
        duplicateCoversStatement(equivstart, equivend, first, last, stmt1) and
        duplicateCoversStatement(equivstart, equivend, first, last, stmt2) and
        stmt1 != stmt2 and scope1 != scope2
   )
}

private
predicate duplicateCoversStatement(int equivstart, int equivend, int first, int last, Stmt stmt) {
    exists(DuplicateBlock b1, DuplicateBlock b2, Location startloc, Location endloc |
        stmt.getLocation() = startloc and
        stmt.getLastStatement().getLocation() = endloc and
        first = b1.tokenStartingAt(startloc) and
        last = b2.tokenEndingAt(endloc) and
        b1.getEquivalenceClass() = equivstart and
        b2.getEquivalenceClass() = equivend and
        duplicate_extension(b1, _, b2, _, equivstart, equivend)
    )
}

predicate duplicateStatements(Scope s1, Scope s2, int duplicate, int total) {
    duplicate = strictcount(Stmt stmt | duplicateStatement(s1, s2, stmt, _)) and
    total = strictcount(Stmt stmt | s1.contains(stmt))
}

/**
 * Find pairs of scopes that are identical or almost identical
 */
predicate duplicateScopes(Scope s, Scope other, float percent, string message) {
    exists(int total, int duplicate | 
        duplicateStatements(s, other, duplicate, total) |
        percent = 100.0 * duplicate / total and percent >= 80.0 and
        if duplicate = total then
            message = "All " + total + " statements in " + s.getName() + " are identical in $@."
        else
            message = duplicate + " out of " + total + " statements in " + s.getName() + " are duplicated in $@."
    )
}

private
predicate similarStatement(Scope scope1, Scope scope2, Stmt stmt1, Stmt stmt2) {
     exists(int start, int end, int first, int last |
        scope1.contains(stmt1) and
        scope2.contains(stmt2) and
        similarCoversStatement(start, end, first, last, stmt1) and
        similarCoversStatement(start, end, first, last, stmt2) and
        stmt1 != stmt2 and scope1 != scope2
    )
}

private
predicate similarCoversStatement(int equivstart, int equivend, int first, int last, Stmt stmt) {
    exists(SimilarBlock b1, SimilarBlock b2, Location startloc, Location endloc |
        stmt.getLocation() = startloc and
        stmt.getLastStatement().getLocation() = endloc and
        first = b1.tokenStartingAt(startloc) and
        last = b2.tokenEndingAt(endloc) and
        b1.getEquivalenceClass() = equivstart and
        b2.getEquivalenceClass() = equivend and
        similar_extension(b1, _, b2, _, equivstart, equivend)
    )
}

predicate similarStatements(Scope s1, Scope s2, int similar, int total) {
    similar = strictcount(Stmt stmt | similarStatement(s1, s2, stmt, _)) and
    total = strictcount(Stmt stmt | s1.contains(stmt))
}

/**
 * Find pairs of scopes that are similar
 */
predicate similarScopes(Scope s, Scope other, float percent, string message) {
    exists(int total, int similar | 
        similarStatements(s, other, similar, total) |
        percent = 100.0 * similar / total and percent >= 80.0 and
        if similar = total then
            message = "All statements in " + s.getName() + " are similar in $@."
        else
            message = similar + " out of " + total + " statements in " + s.getName() + " are similar in $@."
    )
}

predicate scopeLevelDuplication(Scope s, Scope other) {
    similarScopes(s, other, _, _) or duplicateScopes(s, other,_ ,_)
}

predicate whitelistedLineForDuplication(File f, int line) {
    exists(ImportingStmt i |
        i.getLocation().getFile() = f and i.getLocation().getStartLine() = line
    )
}
