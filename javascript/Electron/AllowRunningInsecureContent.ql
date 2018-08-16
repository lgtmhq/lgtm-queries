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
 * @name Enabling Electron allowRunningInsecureContent
 * @description Enabling allowRunningInsecureContent can allow remote code execution.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @tags security
 *       frameworks/electron
 * @id js/enabling-electron-insecure-content
 */


import javascript

from DataFlow::PropWrite allowRunningInsecureContent, Electron::WebPreferences preferences
where allowRunningInsecureContent = preferences.getAPropertyWrite("allowRunningInsecureContent")
  and allowRunningInsecureContent.getRhs().mayHaveBooleanValue(true)
select allowRunningInsecureContent, "Enabling allowRunningInsecureContent is strongly discouraged."
