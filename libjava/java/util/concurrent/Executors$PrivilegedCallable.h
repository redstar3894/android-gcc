
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __java_util_concurrent_Executors$PrivilegedCallable__
#define __java_util_concurrent_Executors$PrivilegedCallable__

#pragma interface

#include <java/lang/Object.h>
extern "Java"
{
  namespace java
  {
    namespace security
    {
        class AccessControlContext;
    }
  }
}

class java::util::concurrent::Executors$PrivilegedCallable : public ::java::lang::Object
{

public: // actually package-private
  Executors$PrivilegedCallable(::java::util::concurrent::Callable *);
public:
  ::java::lang::Object * call();
public: // actually package-private
  static ::java::util::concurrent::Callable * access$0(::java::util::concurrent::Executors$PrivilegedCallable *);
  static void access$1(::java::util::concurrent::Executors$PrivilegedCallable *, ::java::lang::Object *);
  static void access$2(::java::util::concurrent::Executors$PrivilegedCallable *, ::java::lang::Exception *);
private:
  ::java::security::AccessControlContext * __attribute__((aligned(__alignof__( ::java::lang::Object)))) acc;
  ::java::util::concurrent::Callable * task;
  ::java::lang::Object * result;
  ::java::lang::Exception * exception;
public:
  static ::java::lang::Class class$;
};

#endif // __java_util_concurrent_Executors$PrivilegedCallable__
