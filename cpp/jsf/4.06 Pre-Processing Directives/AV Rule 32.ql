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
 * @name Include header files only
 * @description The #include pre-processor directive should only be used to include header files.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @tags maintainability
 *       modularity
 */
import default
import semmle.code.cpp.AutogeneratedFile

from Include i, File f, string extension
where f = i.getIncludedFile() and extension = f.getExtension().toLowerCase()
  and extension != "inl"
  and extension != "tcc"
  and extension != "tpp"
  and extension != "txx"
  and extension != "xpm"
  and not (f instanceof AutogeneratedFile)
  and not (f instanceof HeaderFile)
select i, "The #include pre-processor directive should only be used to include header files."
