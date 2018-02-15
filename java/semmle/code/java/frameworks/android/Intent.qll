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

import java

class TypeIntent extends Class {
  TypeIntent() {
    hasQualifiedName("android.content", "Intent")
  }
}

class TypeActivity extends Class {
  TypeActivity() {
    hasQualifiedName("android.app", "Activity")
  }
}

class TypeContext extends RefType {
  TypeContext() {
    hasQualifiedName("android.content", "Context")
  }
}

class TypeBroadcastReceiver extends Class {
  TypeBroadcastReceiver() {
    hasQualifiedName("android.content", "BroadcastReceiver")
  }
}

class AndroidGetIntentMethod extends Method {
  AndroidGetIntentMethod() {
    hasName("getIntent") and getDeclaringType() instanceof TypeActivity
  }
}

class AndroidReceiveIntentMethod extends Method {
  AndroidReceiveIntentMethod() {
    hasName("onReceive") and getDeclaringType() instanceof TypeBroadcastReceiver
  }
}

class ContextStartActivityMethod extends Method {
  ContextStartActivityMethod() {
    (hasName("startActivity") or hasName("startActivities")) and 
    getDeclaringType() instanceof TypeContext
  }
}

class IntentGetExtraMethod extends Method {
  IntentGetExtraMethod() {
    (getName().regexpMatch("get\\w+Extra") or hasName("getExtras")) and
    getDeclaringType() instanceof TypeIntent
  }
}