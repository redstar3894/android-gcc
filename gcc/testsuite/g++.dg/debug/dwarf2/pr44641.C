// Origin: PR 44641
// { dg-do compile }
// { dg-options "-g -O0 -dA" }

template <class A> struct MisplacedDbg;
template<class T> struct MisplacedDbg<T*>;
struct Full;
template<> struct MisplacedDbg<Full>;

struct Arg;
typedef MisplacedDbg<Arg> Typedef1;
typedef MisplacedDbg<Arg*> Typedef2;
typedef MisplacedDbg<Full> Typedef3;

template<typename T> struct Base  {
  virtual ~Base() {
  }
};

template <>
struct MisplacedDbg<Full>
    : public Base<int>
{  // { dg-function-on-line {_ZN12MisplacedDbgI4FullEC[12]Ev} }
   // { dg-function-on-line {_ZN12MisplacedDbgI4FullED0Ev} { target *-*-* } 23 }
};

template <class T>
struct MisplacedDbg<T*>
    : public Base<int>
{  // { dg-function-on-line {_ZN12MisplacedDbgIP3ArgEC[12]Ev} }
   // { dg-function-on-line {_ZN12MisplacedDbgIP3ArgED0Ev} { target *-*-* } 30 }
};

template <class A>
struct MisplacedDbg
    : public Base<int>
{  // { dg-function-on-line {_ZN12MisplacedDbgI3ArgEC[12]Ev} }
   // { dg-function-on-line {_ZN12MisplacedDbgI3ArgED0Ev} { target *-*-* } 37 }
};

static MisplacedDbg<Arg> static_var1;
static MisplacedDbg<Arg*> static_var2;
static MisplacedDbg<Full> static_var3;
