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


import python

/** A file */
class File extends Container {

    File() {
        files(this, _, _, _, _)
    }

    /** The name of this file (the full path) */
    string getName() {
        files(this, result, _, _, _)
    }

    /**
     * An alias for getName(), provided for compatibility with the Java and C++ libraries.
     */
    string getFullName() {
        result = getName()
    }

    string toString() {
        result = "file:" + getName()
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        this.getName() = filepath and bl = 0 and bc = 0 and el = 0 and ec = 0
    }

    /** Whether this file is a source code file. */
    predicate fromSource() {
        /* If we start to analyse .pyc files, then this will have to change. */
        any()
    }

    /** Gets a short name for this file (just the file name) */
    string getShortName() {
        exists(string simple, string ext | files(this, _, simple, ext, _) |
             result = simple + ext)
    }

    /** Gets the base name for this file (without leading path or extension) */
    string getBaseName() {
        files(this, _, result, _, _)
    }

    /** Gets the extension of the file  */
    string getExtension() {
        files(this, _, _, result, _)
    }
 
    private int lastLine() {
        result = max(int i | exists(Location l | l.getFile() = this and l.getEndLine() = i))
    }

    /** Whether line n is empty (it contains neither code nor comment). */
    predicate emptyLine(int n) {
        n in [0..this.lastLine()]
        and
        not occupied_line(this, n)
    }

    string getSpecifiedEncoding() {
        exists(Comment c, Location l | 
            l = c.getLocation() and l.getFile() = this |
            l.getStartLine() < 3 and
            result = c.getText().regexpCapture(".*coding[:=]\\s*([-\\w.]+).*", 1)
        )
    }

}

private predicate occupied_line(File f, int n) {
    exists(Location l |
        l.getFile() = f | 
        l.getStartLine() = n
        or
        exists(StrConst s | s.getLocation() = l |
            n in [l.getStartLine() .. l.getEndLine()]
        )
     )
}

/** A folder (directory) */
class Folder extends Container {

    Folder() {
        folders(this, _, _)
    }

    string toString() {
        result = "folder:" + getName()
    }


    string getName() {
        folders(this, result, _)
    }

    /** The short (without leading path) name of this folder. */
    string getSimple() {
        folders(this, _, result)
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        this.getName() = filepath and bl = 0 and bc = 0 and el = 0 and ec = 0
    }

}

/** A container is an abstract representation of a file system object that can
    hold elements of interest. */
abstract class Container extends @container {

    Container getParent() {
        containerparent(result, this)
    }

    /** Gets a child of this container */
    Container getChild() {
        containerparent(this, result)
    }

    abstract string toString();

    /** Gets the name of this container */
    abstract string getName();

    /**
     * Gets the relative path of this file from the root of the analyzed source
     * location, or has no result if this file is not under the source location (i.e.
     * if `getFullName` does not have the source location as a prefix).
     */
    string getRelativePath() {
        exists(string prefix |
            sourceLocationPrefix(prefix) |
            (
                getName().matches(prefix + "/%") and
                // remove source location and the following slash
                result = getName().suffix(prefix.length() + 1)
            ) or (
                // special case for prefix = "/" and "/" at the beginning of path
                prefix = "/" and
                getName().charAt(0) = "/" and
                result = getName().suffix(1)
            )
        )
    }

    /** Whether this file or folder is part of the standard library */
    predicate inStdlib() {
        this.inStdlib(_, _)
    }

    /** Whether this file or folder is part of the standard library 
     * for version `major.minor`
     */
    predicate inStdlib(int major, int minor) {
        // https://docs.python.org/library/sys.html#sys.prefix
        exists(string sys_prefix, string version |
            version = major + "." + minor and
            allowable_version(major, minor) and
            py_flags_versioned("sys.prefix", sys_prefix, _) and
            this.getName().regexpMatch(sys_prefix + "/lib/python" + version + ".*")
        )
    }

}

private predicate allowable_version(int major, int minor) {
    major = 2 and minor in [6..7]
    or
    major = 3 and minor in [3..6] 
}

class Location extends @location {

    /** Gets the file for this location */
    File getFile() {
        locations_default(this, result, _, _, _, _)
        or
        exists(Module m | locations_ast(this, m, _, _, _, _) |
            result = m.getFile()
        )
    }

    /** Gets the start line of this location */
    int getStartLine() {
        locations_default(this, _, result, _, _, _)
        or locations_ast(this,_,result,_,_,_)
    }

    /** Gets the start column of this location */
    int getStartColumn() {
        locations_default(this, _, _, result, _, _)
        or locations_ast(this, _, _, result, _, _)
    }

    /** Gets the end line of this location */
    int getEndLine() {
        locations_default(this, _, _, _, result, _)
        or locations_ast(this, _, _, _, result, _)
    }

    /** Gets the end column of this location */
    int getEndColumn() {
        locations_default(this, _, _, _, _, result)
        or locations_ast(this, _, _, _, _, result)
    }

    string toString() {
        result = this.getFile().getName() + ":" + this.getStartLine().toString()
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        exists(File f | f.getName() = filepath |
            locations_default(this, f, bl, bc, el, ec)
            or
            exists(Module m | m.getFile() = f |
                locations_ast(this, m, bl, bc, el, ec))
            )
    }

}

/** A non-empty line in the source code */
class Line extends @py_line {

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        exists(Module m | m.getFile().getName() = filepath and
            el = bl and bc = 1 and
            py_line_lengths(this, m, bl, ec))
    }

    string toString() {
        exists(Module m | py_line_lengths(this, m, _, _) |
            result = m.getFile().getShortName() + ":" + this.getLineNumber().toString()
        )
    }

    /** Gets the line number of this line */
    int getLineNumber() {
        py_line_lengths(this, _, result, _)
    }

    /** Gets the length of this line */
    int getLength() {
        py_line_lengths(this, _, _, result)
    }

    /** Gets the file for this line */
    Module getModule() {
        py_line_lengths(this, result, _, _)
    }

}

/** A syntax error. Note that if there is a syntax error in a module,
   much information about that module will be lost */
class SyntaxError extends Location {

    SyntaxError() {
        py_syntax_error_versioned(this, _, major_version().toString())
    }

    string toString() {
        result = "Syntax Error"
    }

    /** Gets the message corresponding to this syntax error */
    string getMessage() {
        py_syntax_error_versioned(this, result, major_version().toString())
    }

}

/** An encoding error. Note that if there is an encoding error in a module,
   much information about that module will be lost */
class EncodingError extends SyntaxError {

    EncodingError() {
        /* Leave spaces around 'decode' in unlikely event it occurs as a name in a syntax error */
        this.getMessage().toLowerCase().matches("% decode %")
    }

    string toString() {
        result = "Encoding Error"
    }

}


