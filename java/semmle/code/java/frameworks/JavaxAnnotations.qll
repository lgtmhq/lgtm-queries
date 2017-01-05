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

import java

/*
 * javax.annotation annotations
 */

class GeneratedAnnotation extends Annotation {
  GeneratedAnnotation() {
    this.getType().hasQualifiedName("javax.annotation", "Generated")
  }
}

class PostConstructAnnotation extends Annotation {
  PostConstructAnnotation() {
    this.getType().hasQualifiedName("javax.annotation", "PostConstruct")
  }
}

class PreDestroyAnnotation extends Annotation {
  PreDestroyAnnotation() {
    this.getType().hasQualifiedName("javax.annotation", "PreDestroy")
  }
}

class ResourceAnnotation extends Annotation {
  ResourceAnnotation() {
    this.getType().hasQualifiedName("javax.annotation", "Resource")
  }
}

class ResourcesAnnotation extends Annotation {
  ResourcesAnnotation() {
    this.getType().hasQualifiedName("javax.annotation", "Resources")
  }
}

/*
 * javax.annotation.security annotations
 */

class DeclareRolesAnnotation extends Annotation {
  DeclareRolesAnnotation() {
    this.getType().hasQualifiedName("javax.annotation.security", "DeclareRoles")
  }
}

class DenyAllAnnotation extends Annotation {
  DenyAllAnnotation() {
    this.getType().hasQualifiedName("javax.annotation.security", "DenyAll")
  }
}

class PermitAllAnnotation extends Annotation {
  PermitAllAnnotation() {
    this.getType().hasQualifiedName("javax.annotation.security", "PermitAll")
  }
}

class RolesAllowedAnnotation extends Annotation {
  RolesAllowedAnnotation() {
    this.getType().hasQualifiedName("javax.annotation.security", "RolesAllowed")
  }
}

class RunAsAnnotation extends Annotation {
  RunAsAnnotation() {
    this.getType().hasQualifiedName("javax.annotation.security", "RunAs")
  }
}

/*
 * javax.interceptor annotations
 */

class AroundInvokeAnnotation extends Annotation {
  AroundInvokeAnnotation() {
    this.getType().hasQualifiedName("javax.interceptor", "AroundInvoke")
  }
}

class ExcludeClassInterceptorsAnnotation extends Annotation {
  ExcludeClassInterceptorsAnnotation() {
    this.getType().hasQualifiedName("javax.interceptor", "ExcludeClassInterceptors")
  }
}

class ExcludeDefaultInterceptorsAnnotation extends Annotation {
  ExcludeDefaultInterceptorsAnnotation() {
    this.getType().hasQualifiedName("javax.interceptor", "ExcludeDefaultInterceptors")
  }
}

class InterceptorsAnnotation extends Annotation {
  InterceptorsAnnotation() {
    this.getType().hasQualifiedName("javax.interceptor", "Interceptors")
  }
}

/*
 * javax.jws annotations
 */

class WebServiceAnnotation extends Annotation {
  WebServiceAnnotation() {
    this.getType().hasQualifiedName("javax.jws", "WebService")
  }
}

/*
 * javax.xml.ws annotations
 */

class WebServiceRefAnnotation extends Annotation {
  WebServiceRefAnnotation() {
    this.getType().hasQualifiedName("javax.xml.ws", "WebServiceRef")
  }
}
