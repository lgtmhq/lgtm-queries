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
 * @name External dependencies
 * @description Count the number of dependencies that a Python source file has on external packages.
 * @kind treemap
 * @treemap.warnOn highValues 
 * @metricType externalDependency
 * @precision medium
 */

import python
import semmle.python.dependencies.TechInventory

/* 
 * These two columns encode four logical columns:
 * 
 * 1. Python source file where the dependency originates
 * 2. Package Object, ideally referring to a PyPI or similar externally provided package
 * 3. Version of that package Object, if known
 * 4. Number of dependencies from the source file to the package
 * 
 * Ideally this query would therefore return three columns,
 * but this would require changing the dashboard database schema
 * and dashboard extractor.
 * 
 * The first column (the Python source file) is prepended with a '/'
 * so that the file path matches the path used for the file in the
 * dashboard database, which is implicitly relative to the source
 * archive location.
 */

predicate src_package_count(File sourceFile, ExternalPackage package, int total) {
    total = strictcount(AstNode src | 
        dependency(src, package) and
        src.getLocation().getFile() = sourceFile
    )
}

from File sourceFile, int total, string entity, ExternalPackage package
where 
src_package_count(sourceFile, package, total) and
entity = munge(sourceFile, package)
select entity, total
order by total desc
