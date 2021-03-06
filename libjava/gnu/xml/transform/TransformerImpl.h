
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __gnu_xml_transform_TransformerImpl__
#define __gnu_xml_transform_TransformerImpl__

#pragma interface

#include <javax/xml/transform/Transformer.h>
#include <gcj/array.h>

extern "Java"
{
  namespace gnu
  {
    namespace xml
    {
      namespace transform
      {
          class Stylesheet;
          class TransformerFactoryImpl;
          class TransformerImpl;
      }
    }
  }
  namespace javax
  {
    namespace xml
    {
      namespace namespace
      {
          class QName;
      }
      namespace transform
      {
          class ErrorListener;
          class Result;
          class Source;
          class URIResolver;
        namespace stream
        {
            class StreamResult;
        }
      }
    }
  }
  namespace org
  {
    namespace w3c
    {
      namespace dom
      {
          class Document;
          class Node;
      }
    }
  }
}

class gnu::xml::transform::TransformerImpl : public ::javax::xml::transform::Transformer
{

public: // actually package-private
  TransformerImpl(::gnu::xml::transform::TransformerFactoryImpl *, ::gnu::xml::transform::Stylesheet *, ::java::util::Properties *);
public:
  virtual void transform(::javax::xml::transform::Source *, ::javax::xml::transform::Result *);
public: // actually package-private
  static jboolean strip(::gnu::xml::transform::Stylesheet *, ::org::w3c::dom::Node *);
private:
  static JArray< ::java::lang::String * > * tokenizeWhitespace(::java::lang::String *);
public: // actually package-private
  virtual void writeStreamResult(::org::w3c::dom::Node *, ::javax::xml::transform::stream::StreamResult *, jint, ::java::lang::String *);
  virtual void copyChildren(::org::w3c::dom::Document *, ::org::w3c::dom::Node *, ::org::w3c::dom::Node *);
public:
  virtual void setParameter(::java::lang::String *, ::java::lang::Object *);
  virtual ::java::lang::Object * getParameter(::java::lang::String *);
  virtual void clearParameters();
  virtual void setURIResolver(::javax::xml::transform::URIResolver *);
  virtual ::javax::xml::transform::URIResolver * getURIResolver();
  virtual void setOutputProperties(::java::util::Properties *);
  virtual ::java::util::Properties * getOutputProperties();
  virtual void setOutputProperty(::java::lang::String *, ::java::lang::String *);
  virtual ::java::lang::String * getOutputProperty(::java::lang::String *);
  virtual void setErrorListener(::javax::xml::transform::ErrorListener *);
  virtual ::javax::xml::transform::ErrorListener * getErrorListener();
public: // actually package-private
  virtual void reindent(::org::w3c::dom::Document *, ::org::w3c::dom::Node *, jint);
  virtual void convertCdataSectionElements(::org::w3c::dom::Document *, ::org::w3c::dom::Node *, ::java::util::List *);
  virtual jboolean match(::javax::xml::namespace::QName *, ::org::w3c::dom::Node *);
  ::gnu::xml::transform::TransformerFactoryImpl * __attribute__((aligned(__alignof__( ::javax::xml::transform::Transformer)))) factory;
  ::gnu::xml::transform::Stylesheet * stylesheet;
  ::javax::xml::transform::URIResolver * uriResolver;
  ::javax::xml::transform::ErrorListener * errorListener;
  ::java::util::Properties * outputProperties;
  static ::java::lang::String * INDENT_WHITESPACE;
public:
  static ::java::lang::Class class$;
};

#endif // __gnu_xml_transform_TransformerImpl__
