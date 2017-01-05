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
 * @name Empty synchronized block
 * @description Empty synchronized blocks may indicate the presence of
 *              incomplete code or incorrect synchronization, and may lead to concurrency problems.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       concurrency
 *       language-features
 *       external/cwe/cwe-585
 */
import java

from SynchronizedStmt sync
where not exists(sync.getBlock().getAChild())
select sync, "Empty synchronized block."
