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

/** Provides classes and predicates for modeling XML parsers in Java.*/

import java
import semmle.code.java.security.DataFlow

/*
 * Various XML parsers in Java.
 */

/**
 * An abstract type representing a call to parse XML files.
 */
abstract class XmlParserCall extends MethodAccess {
  /**
   * Gets the argument representing the XML content to be parsed.
   */
  abstract Expr getSink();
  /**
   * Holds if the call is safe.
   */
  abstract predicate isSafe();
}

/**
 * An access to a method use for configuring the parser.
 */
abstract class ParserConfig extends MethodAccess {

  /**
   * Holds if the method disables a property.
   */
  predicate disables(Expr e) {
    this.getArgument(0) = e and
    this.getArgument(1).(BooleanLiteral).getBooleanValue() = false
  }

  /**
   * Holds if the method enables a property.
   */
  predicate enables(Expr e) {
    this.getArgument(0) = e and
    this.getArgument(1).(BooleanLiteral).getBooleanValue() = true
  }
}

 /*
  *  https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#DocumentBuilder
  */

/** The class `javax.xml.parsers.DocumentBuilderFactory`. */
class DocumentBuilderFactory extends RefType {
  DocumentBuilderFactory() {
    this.hasQualifiedName("javax.xml.parsers", "DocumentBuilderFactory")
  }
}

/** The class `javax.xml.parsers.DocumentBuilder`. */
class DocumentBuilder extends RefType {
  DocumentBuilder() {
    this.hasQualifiedName("javax.xml.parsers", "DocumentBuilder")
  }
}

/** A call to `DocumentBuilder.parse`. */
class DocumentBuilderParse extends XmlParserCall {
  DocumentBuilderParse() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof DocumentBuilder and
      m.hasName("parse")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeDocumentBuilder sb | sb.flowsTo(this.getQualifier()))
  }
}

/**
 * A `ParserConfig` specific to `DocumentBuilderFactory`.
 */
class DocumentBuilderFactoryConfig extends ParserConfig {
  DocumentBuilderFactoryConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof DocumentBuilderFactory and
      m.hasName("setFeature")
    )
  }
}

/**
 * A general configuration that is safe when enabled.
 */
Expr singleSafeConfig() {
  result.(StringLiteral).getValue() = "http://apache.org/xml/features/disallow-doctype-decl" or
  result.(StringLiteral).getValue() = "http://javax.xml.XMLConstants/feature/secure-processing" or
  exists(Field f |
    result = f.getAnAccess() and
    f.hasName("FEATURE_SECURE_PROCESSING") and
    f.getDeclaringType().hasQualifiedName("javax.xml", "XMLConstants")
  )
}

/**
 * A safely configured `DocumentBuilderFactory` that is safe for creating `DocumentBuilder`.
 */
class SafeDocumentBuilderFactory extends FlowSource, VarAccess {
  SafeDocumentBuilderFactory() {
    exists(Variable v | v = this.getVariable() |
      exists(DocumentBuilderFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.enables(singleSafeConfig())
      )
      or
      (
        //These two need to be set together to work
        exists(DocumentBuilderFactoryConfig config | config.getQualifier() = v.getAnAccess() |
          config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-general-entities"))
        ) and
        exists(DocumentBuilderFactoryConfig config | config.getQualifier() = v.getAnAccess() |
          config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-parameter-entities"))
        )
      )
    )
  }
}

/**
 * A `DocumentBuilder` created from a safely configured `DocumentBuilderFactory`.
 */
class SafeDocumentBuilder extends FlowSource, MethodAccess {
  SafeDocumentBuilder() {
    exists(SafeDocumentBuilderFactory sdf, Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof DocumentBuilderFactory and
      m.hasName("newDocumentBuilder") and 
      sdf.flowsTo(this.getQualifier())
    )
  }
}


/*
 * https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#XMLInputFactory_.28a_StAX_parser.29
 */

/** The class `javax.xml.stream.XMLInputFactory`. */
class XmlInputFactory extends RefType {
  XmlInputFactory() {
    this.hasQualifiedName("javax.xml.stream", "XMLInputFactory")
  }
}

/** A call to `XMLInputFactory.createXMLStreamReader`. */
class XmlInputFactoryStreamReader extends XmlParserCall {
  XmlInputFactoryStreamReader() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof XmlInputFactory and
      m.hasName("createXMLStreamReader")
    )
  }

  override Expr getSink() {
    if this.getMethod().getParameterType(0) instanceof TypeString
    then
      result = this.getArgument(1)
    else
      result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeXmlInputFactory sf | sf.flowsTo(this.getQualifier()))
  }
}

/** A call to `XMLInputFactory.createEventReader`.*/
class XmlInputFactoryEventReader extends XmlParserCall {
  XmlInputFactoryEventReader() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof XmlInputFactory and
      m.hasName("createXMLEventReader")
    )
  }

  override Expr getSink() {
    if this.getMethod().getParameterType(0) instanceof TypeString
    then
      result = this.getArgument(1)
    else
      result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeXmlInputFactory sf | sf.flowsTo(this.getQualifier()))
  }
}

/**
 * A `ParserConfig` specific to `XMLInputFactory`.
 */
class XmlInputFactoryConfig extends ParserConfig {
  XmlInputFactoryConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof XmlInputFactory and
      m.hasName("setProperty")
    )
  }
}

/**
 * An `XmlInputFactory` specific expression that indicates whether parsing external entities is supported.
 */
Expr configOptionIsSupportingExternalEntities() {
  result.(StringLiteral).getValue() = "javax.xml.stream.isSupportingExternalEntities" or
  exists(Field f |
    result = f.getAnAccess() and
    f.hasName("IS_SUPPORTING_EXTERNAL_ENTITIES") and
    f.getDeclaringType() instanceof XmlInputFactory
  )
}

/**
 * An `XmlInputFactory` specific expression that indicates whether DTD is supported.
 */
Expr configOptionSupportDTD() {
  result.(StringLiteral).getValue() = "javax.xml.stream.supportDTD" or
  exists(Field f |
    result = f.getAnAccess() and
    f.hasName("SUPPORT_DTD") and
    f.getDeclaringType() instanceof XmlInputFactory
  )
}

/**
 * A safely configured `XmlInputFactory`.
 */
class SafeXmlInputFactory extends FlowSource, VarAccess {
  SafeXmlInputFactory() {
    exists(Variable v |
      v = this.getVariable() and
      exists(XmlInputFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(configOptionIsSupportingExternalEntities())
      ) and
      exists(XmlInputFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(configOptionSupportDTD())
      )
    )
  }
}


/*
 * https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#SAXBuilder
 */

/**
 * The class `org.jdom.input.SAXBuilder.`
 */
class SAXBuilder extends RefType {
  SAXBuilder() {
    this.hasQualifiedName("org.jdom.input", "SAXBuilder") or
    this.hasQualifiedName("org.jdom2.input", "SAXBuilder")
  }
}

/**
 * A call to `SAXBuilder.build.`
 */
class SAXBuilderParse extends XmlParserCall {
  SAXBuilderParse() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXBuilder and
      m.hasName("build")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeSAXBuilder sb | sb.flowsTo(this.getQualifier()))
  }
}

/**
 * A `ParserConfig` specific to `SAXBuilder`.
 */
class SAXBuilderConfig extends ParserConfig {
  SAXBuilderConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXBuilder and
      m.hasName("setFeature")
    )
  }
}

/** A safely configured `SAXBuilder`.*/
class SafeSAXBuilder extends FlowSource, VarAccess {
  SafeSAXBuilder() {
    exists(Variable v |
      v = this.getVariable() and
      exists(SAXBuilderConfig config | config.getQualifier() = v.getAnAccess() |
      config.enables(any(StringLiteral s | s.getValue() = "http://apache.org/xml/features/disallow-doctype-decl"))
      )
    )
  }
}

/*
 * The case in
 * https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#Unmarshaller
 * will be split into two, one covers a SAXParser as a sink, the other the SAXSource as a sink.
 */

/**
 * The class `javax.xml.parsers.SAXParser`.
 */
class SAXParser extends RefType {
  SAXParser() {
    this.hasQualifiedName("javax.xml.parsers", "SAXParser")
  }
}

/** The class `javax.xml.parsers.SAXParserFactory`. */
class SAXParserFactory extends RefType {
  SAXParserFactory() {
    this.hasQualifiedName("javax.xml.parsers", "SAXParserFactory")
  }
}

/** A call to `SAXParser.parse`.*/
class SAXParserParse extends XmlParserCall {
  SAXParserParse() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXParser and
      m.hasName("parse")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeSAXParser sp | sp.flowsTo(this.getQualifier()))
  }
}

/** A `ParserConfig` that is specific to `SAXParserFactory`.*/
class SAXParserFactoryConfig extends ParserConfig {
  SAXParserFactoryConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXParserFactory and
      m.hasName("setFeature")
    )
  }
}


/**
 * A safely configured `SAXParserFactory`.
 */
class SafeSAXParserFactory extends FlowSource, VarAccess {
  SafeSAXParserFactory() {
    exists(Variable v | v = this.getVariable() |
      exists(SAXParserFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-general-entities"))
      ) and
      exists(SAXParserFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-parameter-entities"))
      ) and
      exists(SAXParserFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(any(StringLiteral s | s.getValue() = "http://apache.org/xml/features/nonvalidating/load-external-dtd"))
      )
    )
  }
}

/** A `SAXParser` created from a safely configured `SAXParserFactory`.*/
class SafeSAXParser extends FlowSource, MethodAccess {
  SafeSAXParser() {
    exists(SafeSAXParserFactory sdf |
      this.getMethod().getDeclaringType() instanceof SAXParserFactory and
      this.getMethod().hasName("newSAXParser") and
      sdf.flowsTo(this.getQualifier())
    )
  }
}

/* SAXReader: https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#SAXReader */

/**
 * The class `org.dom4j.io.SAXReader`.
 */
class SAXReader extends RefType {
  SAXReader() {
    this.hasQualifiedName("org.dom4j.io", "SAXReader")
  }
}

/** A call to `SAXReader.read`.*/
class SAXReaderRead extends XmlParserCall {
  SAXReaderRead() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXReader and
      m.hasName("read")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeSAXReader sr | sr.flowsTo(this.getQualifier()))
  }
}

/** A `ParserConfig` specific to `SAXReader`.*/
class SAXReaderConfig extends ParserConfig {
  SAXReaderConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXReader and
      m.hasName("setFeature")
    )
  }
}

/** A safely configured `SAXReader`.*/
class SafeSAXReader extends FlowSource, VarAccess {
  SafeSAXReader() {
    exists(Variable v | v = this.getVariable() |
      exists(SAXReaderConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-general-entities"))
      ) and
      exists(SAXReaderConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-parameter-entities"))
      ) and
      exists(SAXReaderConfig config | config.getQualifier() = v.getAnAccess() |
        config.enables(any(StringLiteral s | s.getValue() = "http://apache.org/xml/features/disallow-doctype-decl"))
      )
    )
  }
}

/* https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#XMLReader*/

/** The class `org.xml.sax.XMLReader`.*/
class XMLReader extends RefType {
  XMLReader() {
    this.hasQualifiedName("org.xml.sax", "XMLReader")
  }
}

/** A call to `XMLReader.read`.*/
class XMLReaderParse extends XmlParserCall {
  XMLReaderParse() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof XMLReader and
      m.hasName("parse")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(ExplicitlySafeXMLReader sr | sr.flowsTo(this.getQualifier())) or
    exists(CreatedSafeXMLReader cr | cr.flowsTo(this.getQualifier()))
  }
}

/** A `ParserConfig` specific to the `XMLReader`.*/
class XMLReaderConfig extends ParserConfig {
    XMLReaderConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof XMLReader and
      m.hasName("setFeature")
    )
  }
}

/** An `XMLReader` that is explicitly configured to be safe.*/
class ExplicitlySafeXMLReader extends FlowSource, VarAccess {
  ExplicitlySafeXMLReader() {
    exists(Variable v | v = this.getVariable() |
      (
        exists(XMLReaderConfig config | config.getQualifier() = v.getAnAccess() |
          config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-general-entities"))
        ) and
        exists(XMLReaderConfig config | config.getQualifier() = v.getAnAccess() |
          config.disables(any(StringLiteral s | s.getValue() = "http://xml.org/sax/features/external-parameter-entities"))
        ) and
        exists(XMLReaderConfig config | config.getQualifier() = v.getAnAccess() |
          config.disables(any(StringLiteral s | s.getValue() = "http://apache.org/xml/features/nonvalidating/load-external-dtd"))
        )
      ) or
      exists(XMLReaderConfig config | config.getQualifier() = v.getAnAccess() |
        config.enables(any(StringLiteral s | s.getValue() = "http://apache.org/xml/features/disallow-doctype-decl")))
    )
  }
}

/** An `XMLReader` that is obtained from a safe source.*/
class CreatedSafeXMLReader extends FlowSource, MethodAccess {
  CreatedSafeXMLReader() {
    //Obtained from SAXParser
    exists(SafeSAXParser safeParser |
      this.getMethod().getDeclaringType() instanceof SAXParser and
      this.getMethod().hasName("getXMLReader") and
      safeParser.flowsTo(this.getQualifier())
    ) or
    //Obtained from SAXReader
    exists(SafeSAXReader safeReader |
      this.getMethod().getDeclaringType() instanceof SAXReader and
      this.getMethod().hasName("getXMLReader") and
      safeReader.flowsTo(this.getQualifier())
    )
  }
}

/*
 * SAXSource in
 * https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#Unmarshaller
 */

 /** The class `javax.xml.transform.sax.SAXSource` */
class SAXSource extends RefType {
  SAXSource() {
    this.hasQualifiedName("javax.xml.transform.sax", "SAXSource")
  }
}

/** A call to the constructor of `SAXSource` with `XMLReader` and `InputSource`.*/
class ConstructedSAXSource extends FlowSource, ClassInstanceExpr {
  ConstructedSAXSource() {
    this.getConstructedType() instanceof SAXSource and
    this.getNumArgument() = 2 and
    this.getArgument(0).getType() instanceof XMLReader
  }
  /**
   * Gets the argument representing the XML content to be parsed.
   */
  Expr getSink() {
    result = this.getArgument(1)
  }
  /** Holds if the resulting `SAXSource` is safe.*/
  predicate isSafe() {
    exists(CreatedSafeXMLReader safeReader | safeReader.flowsTo(this.getArgument(0))) or
    exists(ExplicitlySafeXMLReader safeReader | safeReader.flowsTo(this.getArgument(0)))
  }
}
/** A call to the `SAXSource.setXMLReader` method.*/
class SAXSourceSetReader extends MethodAccess {
  SAXSourceSetReader() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof SAXSource and
      m.hasName("setXMLReader")
    )
  }
}
/** A `SAXSource` that is safe to use.*/
class SafeSAXSource extends FlowSource, VarAccess {
  SafeSAXSource() {
    exists(Variable v | v = this.getVariable() |
      exists(SAXSourceSetReader s | s.getQualifier() = v.getAnAccess() |
        (
          exists(CreatedSafeXMLReader safeReader | safeReader.flowsTo(s.getArgument(0))) or
          exists(ExplicitlySafeXMLReader safeReader | safeReader.flowsTo(s.getArgument(0)))
        )
      )
    ) or
    exists(ConstructedSAXSource st | st.flowsTo(this) and st.isSafe())
  }
}

/* Transformer: https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#TransformerFactory*/

/** An access to a method use for configuring a transformer or schema.*/
abstract class TransformerConfig extends MethodAccess {
  /** Holds if the configuration is disabled */
  predicate disables(Expr e) {
    this.getArgument(0) = e and
    this.getArgument(1).(StringLiteral).getValue() = ""
  }
}

/** The class `javax.xml.XMLConstants`.*/
class XmlConstants extends RefType {
  XmlConstants() {
    this.hasQualifiedName("javax.xml", "XMLConstants")
  }
}

/** A configuration specific for transformers and schema.*/
Expr configAccessExternalDTD() {
  result.(StringLiteral).getValue() = "http://javax.xml.XMLConstants/property/accessExternalDTD" or
  exists(Field f |
    result = f.getAnAccess() and
    f.hasName("ACCESS_EXTERNAL_DTD") and
    f.getDeclaringType() instanceof XmlConstants
  )
}

/** A configuration specific for transformers.*/
Expr configAccessExternalStyleSheet() {
  result.(StringLiteral).getValue() = "http://javax.xml.XMLConstants/property/accessExternalStylesheet" or
  exists(Field f |
    result = f.getAnAccess() and
    f.hasName("ACCESS_EXTERNAL_STYLESHEET") and
    f.getDeclaringType() instanceof XmlConstants
  )
}

/** A configuration specific for schema.*/
Expr configAccessExternalSchema() {
  result.(StringLiteral).getValue() = "http://javax.xml.XMLConstants/property/accessExternalSchema" or
  exists(Field f |
    result = f.getAnAccess() and
    f.hasName("ACCESS_EXTERNAL_SCHEMA") and
    f.getDeclaringType() instanceof XmlConstants
  )
}

/** The class `javax.xml.transform.TransformerFactory` or `javax.xml.transform.sax.SAXTransformerFactory`.*/
class TransformerFactory extends RefType {
  TransformerFactory() {
    this.hasQualifiedName("javax.xml.transform", "TransformerFactory")
    or
    this.hasQualifiedName("javax.xml.transform.sax", "SAXTransformerFactory")
  }
}

/** The class `javax.xml.transform.Transformer`.*/
class Transformer extends RefType {
  Transformer() {
    this.hasQualifiedName("javax.xml.transform", "Transformer")
  }
}

/** A call to `Transformer.transform`.*/
class TransformerTransform extends XmlParserCall {
  TransformerTransform() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof Transformer and
      m.hasName("transform")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeTransformer st | st.flowsTo(this.getQualifier()))
  }
}

/** A call to `Transformer.newTransformer` with source.*/
class TransformerFactorySource extends XmlParserCall {
  TransformerFactorySource() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof TransformerFactory and
      m.hasName("newTransformer")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeTransformerFactory stf | stf.flowsTo(this.getQualifier()))
  }
}

/** A `ParserConfig` specific to `TransformerFactory`.*/
class TransformerFactoryConfig extends TransformerConfig {
  TransformerFactoryConfig() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof TransformerFactory and
      m.hasName("setAttribute")
    )
  }
}

/** A safely configured `TransformerFactory`.*/
class SafeTransformerFactory extends FlowSource, VarAccess {
  SafeTransformerFactory() {
    exists(Variable v | v = this.getVariable() |
      exists(TransformerFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(configAccessExternalDTD())
      ) and
      exists(TransformerFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(configAccessExternalStyleSheet())
      )
    )
  }
}

/** A `Transformer` created from a safely configured `TranformerFactory`.*/
class SafeTransformer extends FlowSource, MethodAccess {
  SafeTransformer() {
    exists(SafeTransformerFactory stf, Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof TransformerFactory and
      m.hasName("newTransformer") and
      stf.flowsTo(this.getQualifier())
    )
  }
}

/* SAXTransformer: https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#SAXTransformerFactory
 * Has an extra method called newFilter.
 */

 /** A call to `SAXTransformerFactory.newFilter`.*/
class SAXTransformerFactoryNewXMLFilter extends XmlParserCall {
  SAXTransformerFactoryNewXMLFilter() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType().hasQualifiedName("javax.xml.transform.sax", "SAXTransformerFactory") and
      m.hasName("newXMLFilter")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeTransformerFactory stf | stf.flowsTo(this.getQualifier()))
  }
}

/* Schema: https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#SchemaFactory*/
/** The class `javax.xml.validation.SchemaFactory`.*/
class SchemaFactory extends RefType {
  SchemaFactory() {
    this.hasQualifiedName("javax.xml.validation", "SchemaFactory")
  }
}

/** A `ParserConfig` specific to `SchemaFactory`.*/
class SchemaFactoryConfig extends TransformerConfig {
  SchemaFactoryConfig() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof SchemaFactory and
      m.hasName("setProperty")
    )
  }
}

/** A call to `SchemaFactory.newSchema`.*/
class SchemaFactoryNewSchema extends XmlParserCall {
  SchemaFactoryNewSchema() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof SchemaFactory and
      m.hasName("newSchema")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    exists(SafeSchemaFactory ssf | ssf.flowsTo(this.getQualifier()))
  }
}

/** A safely configured `SchemaFactory`.*/
class SafeSchemaFactory extends FlowSource, VarAccess {
  SafeSchemaFactory() {
    exists(Variable v | v = this.getVariable() |
      exists(SchemaFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(configAccessExternalDTD())) and
      exists(SchemaFactoryConfig config | config.getQualifier() = v.getAnAccess() |
        config.disables(configAccessExternalSchema()))
    )
  }
}

/* Unmarshaller: https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#Unmarshaller*/

/** The class `javax.xml.bind.Unmarshaller`.*/
class XmlUnmarshaller extends RefType {
  XmlUnmarshaller() {
    this.hasQualifiedName("javax.xml.bind", "Unmarshaller")
  }
}

/** A call to `Unmarshaller.unmarshal`*/
class XmlUnmarshal extends XmlParserCall {
  XmlUnmarshal() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof XmlUnmarshaller and
      m.hasName("unmarshal")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    none()
  }
}

/* XPathExpression: https://www.owasp.org/index.php/XML_External_Entity_(XXE)_Prevention_Cheat_Sheet#XPathExpression*/

/** The class `javax.xml.xpath.XPathExpression`.*/
class XPathExpression extends RefType {
  XPathExpression() {
    this.hasQualifiedName("javax.xml.xpath", "XPathExpression")
  }
}

/** A call to `XPathExpression.evaluate`.*/
class XPathEvaluate extends XmlParserCall {
  XPathEvaluate() {
    exists(Method m |
      this.getMethod() = m and
      m.getDeclaringType() instanceof XPathExpression and
      m.hasName("evaluate")
    )
  }

  override Expr getSink() {
    result = this.getArgument(0)
  }

  override predicate isSafe() {
    none()
  }
}