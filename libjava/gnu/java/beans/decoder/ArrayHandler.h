
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __gnu_java_beans_decoder_ArrayHandler__
#define __gnu_java_beans_decoder_ArrayHandler__

#pragma interface

#include <gnu/java/beans/decoder/AbstractElementHandler.h>
extern "Java"
{
  namespace gnu
  {
    namespace java
    {
      namespace beans
      {
        namespace decoder
        {
            class ArrayHandler;
            class Context;
            class ElementHandler;
        }
      }
    }
  }
  namespace java
  {
    namespace beans
    {
        class ExceptionListener;
    }
  }
  namespace org
  {
    namespace xml
    {
      namespace sax
      {
          class Attributes;
      }
    }
  }
}

class gnu::java::beans::decoder::ArrayHandler : public ::gnu::java::beans::decoder::AbstractElementHandler
{

public: // actually package-private
  ArrayHandler(::gnu::java::beans::decoder::ElementHandler *);
public: // actually protected
  virtual ::gnu::java::beans::decoder::Context * startElement(::org::xml::sax::Attributes *, ::java::beans::ExceptionListener *);
private:
  static ::java::util::HashMap * typeMap;
public:
  static ::java::lang::Class class$;
};

#endif // __gnu_java_beans_decoder_ArrayHandler__
