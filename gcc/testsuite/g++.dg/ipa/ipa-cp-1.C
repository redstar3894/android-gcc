/* Test for segfault during updating of jump function in
   interprocedural constant propagation (b/3124518).  */
/* { dg-do compile } */
/* { dg-options "-O2"  } */

namespace std __attribute__ ((__visibility__ ("default"))) {
  template<class _CharT>
    struct char_traits;
}
typedef long int ptrdiff_t;
typedef long unsigned int size_t;
namespace std __attribute__ ((__visibility__ ("default"))) {
  void __throw_bad_cast(void) __attribute__((__noreturn__));
  typedef ptrdiff_t streamsize;
  template<> struct char_traits<char>
  {
    typedef char char_type;
    static size_t length(const char_type* __s) {
    }
  };
}
extern "C++" {
  namespace std {
    class exception {
    };
  }
  void operator delete(void*) throw();
}
namespace __gnu_cxx __attribute__ ((__visibility__ ("default"))) {
  template<typename _Tp>
    class new_allocator {
  public:
    typedef size_t size_type;
    typedef _Tp* pointer;
    template<typename _Tp1>
    struct rebind {
      typedef new_allocator<_Tp1> other;
    };
    void deallocate(pointer __p, size_type) {
      ::operator delete(__p);
    }
  };
}
namespace std __attribute__ ((__visibility__ ("default"))) {
  template<typename _Tp>
    class allocator
      : public __gnu_cxx::new_allocator<_Tp> {
  };
  template<typename _CharT, typename _Traits = char_traits<_CharT> >
    class basic_ostream;
  template<typename _CharT, typename _Traits = char_traits<_CharT> >
    class basic_fstream;
  typedef basic_ostream<char> ostream;
  typedef basic_fstream<char> fstream;
}
namespace __gnu_cxx __attribute__ ((__visibility__ ("default"))) {
  template<typename _CharT, typename _Traits, typename _Alloc>
    class __sso_string_base;
  template<typename _CharT, typename _Traits = std::char_traits<_CharT>, typename _Alloc = std::allocator<_CharT>, template <typename, typename, typename> class _Base = __sso_string_base>
    class __versa_string;
  template<typename _CharT, typename _Traits, typename _Alloc>
    struct __vstring_utility {
    typedef typename _Alloc::template rebind<_CharT>::other _CharT_alloc_type;
    template<typename _Alloc1>
    struct _Alloc_hider
      : public _Alloc1 {
      _Alloc_hider(_CharT* __ptr)
  : _Alloc1(), _M_p(__ptr) {
      }
      _CharT* _M_p;
    };
  };
  template<typename _CharT, typename _Traits, typename _Alloc>
    class __sso_string_base
      : protected __vstring_utility<_CharT, _Traits, _Alloc> {
  public:
    typedef _Traits traits_type;
    typedef __vstring_utility<_CharT, _Traits, _Alloc> _Util_Base;
    typedef typename _Util_Base::_CharT_alloc_type _CharT_alloc_type;
    typedef typename _CharT_alloc_type::size_type size_type;
  private:
    typename _Util_Base::template _Alloc_hider<_CharT_alloc_type>
    _M_dataplus;
    enum {
      _S_local_capacity = 15 };
    union {
      _CharT _M_local_data[_S_local_capacity + 1];
      size_type _M_allocated_capacity;
    };
    bool _M_is_local() const {
    }
    void _M_dispose() {
      if (!_M_is_local()) _M_destroy(_M_allocated_capacity);
    }
    void _M_destroy(size_type __size) throw() {
      _M_get_allocator().deallocate(_M_data(), __size + 1);
    }
  public:
    size_type _M_max_size() const {
    }
    _CharT* _M_data() const {
      return _M_dataplus._M_p;
    }
    __sso_string_base()
  : _M_dataplus(_M_local_data) {
    }
    __sso_string_base(const __sso_string_base& __rcs);
    template<typename _InputIterator>
    __sso_string_base(_InputIterator __beg, _InputIterator __end, const _Alloc& __a);
    ~__sso_string_base() {
      _M_dispose();
    }
    _CharT_alloc_type& _M_get_allocator() {
    }
  };
  template<typename _CharT, typename _Traits, typename _Alloc, template <typename, typename, typename> class _Base>
    class __versa_string
      : private _Base<_CharT, _Traits, _Alloc> {
    typedef _Base<_CharT, _Traits, _Alloc> __vstring_base;
    typedef typename __vstring_base::_CharT_alloc_type _CharT_alloc_type;
  public:
    typedef _Traits traits_type;
    typedef typename _CharT_alloc_type::size_type size_type;
    static const size_type npos = static_cast<size_type>(-1);
  public:
    __versa_string()
  : __vstring_base() {
    }
    __versa_string(const _CharT* __s, const _Alloc& __a = _Alloc())
  : __vstring_base(__s, __s ? __s + traits_type::length(__s)
                   : __s + npos, __a) {
    }
  };
}
namespace std __attribute__ ((__visibility__ ("default"))) {
  template<typename _CharT, typename _Traits, typename _Alloc, template <typename, typename, typename> class _Base>
    inline basic_ostream<_CharT, _Traits>& operator<<(basic_ostream<_CharT, _Traits>& __os, const __gnu_cxx::__versa_string<_CharT, _Traits, _Alloc, _Base>& __str) {
  }
}
template<typename _CharT, typename _Traits = std::char_traits<_CharT>, typename _Alloc = std::allocator<_CharT> >
class basic_string
  : public __gnu_cxx::__versa_string<_CharT, _Traits, _Alloc> {
public:
  typedef __gnu_cxx::__versa_string<_CharT, _Traits, _Alloc> __base;
  inline basic_string()
  : __base() {
  }
  basic_string(const _CharT* __s, const _Alloc& __a = _Alloc())
  : __base(__s, __a) {
  }
};
typedef basic_string<char> string;
namespace std __attribute__ ((__visibility__ ("default"))) {
  class locale {
    class facet;
  };
  class locale::facet {
  };
  class ios_base {
  };
  struct ctype_base {
  };
  template<typename _CharT>
    class __ctype_abstract_base
      : public locale::facet, public ctype_base {
  };
  template<typename _CharT>
    class ctype
      : public __ctype_abstract_base<_CharT> {
  public:
    typedef char char_type;
    mutable char _M_widen_ok;
    mutable char _M_widen[1 + static_cast<unsigned char>(-1)];
    char_type widen(char __c) const {
      if (_M_widen_ok) return _M_widen[static_cast<unsigned char>(__c)];
      this->_M_widen_init();
      return this->do_widen(__c);
    }
    virtual char_type do_widen(char __c) const {
    }
    void _M_widen_init() const;
  };
  template<typename _Facet>
    inline const _Facet& __check_facet(const _Facet* __f) {
    if (!__f) __throw_bad_cast();
  }
  template<typename _CharT, typename _Traits>
    class basic_ios
      : public ios_base {
  public:
    typedef _CharT char_type;
    typedef ctype<_CharT> __ctype_type;
    const __ctype_type* _M_ctype;
    bool eof() const {
    }
    char_type widen(char __c) const {
      return __check_facet(_M_ctype).widen(__c);
    }
  };
  template<typename _CharT, typename _Traits> class basic_ostream
    : virtual public basic_ios<_CharT, _Traits>
  {
  public:
    typedef _CharT char_type;
    typedef basic_ostream<_CharT, _Traits> __ostream_type;
    __ostream_type& operator<<(__ostream_type& (*__pf)(__ostream_type&)) {
    }
    __ostream_type& put(char_type __c);
  };
  template<typename _CharT, typename _Traits>
    inline basic_ostream<_CharT, _Traits>& endl(basic_ostream<_CharT, _Traits>& __os) {
    return flush(__os.put(__os.widen('\n')));
  }
  template<typename _CharT, typename _Traits>
    inline basic_ostream<_CharT, _Traits>& flush(basic_ostream<_CharT, _Traits>& __os) {
  }
}
using std::endl;
namespace std __attribute__ ((__visibility__ ("default"))) {
  template<typename _CharT, typename _Traits> class basic_istream
    : virtual public basic_ios<_CharT, _Traits>
  {
  public:
    typedef _CharT char_type;
    typedef basic_istream<_CharT, _Traits> __istream_type;
    virtual ~basic_istream() {
    }
    __istream_type& getline(char_type* __s, streamsize __n, char_type __delim);
    __istream_type& getline(char_type* __s, streamsize __n) {
      return this->getline(__s, __n, this->widen('\n'));
    }
  };
  template<typename _CharT, typename _Traits>
    class basic_iostream
      : public basic_istream<_CharT, _Traits>, public basic_ostream<_CharT, _Traits> {
  };
}
using std::ostream;
namespace std __attribute__ ((__visibility__ ("default"))) {
  template<typename _CharT, typename _Traits>
    class basic_fstream
      : public basic_iostream<_CharT, _Traits> {
  };
}
namespace FooNamespace {
  class ExceptionLocation {
  public:
    ExceptionLocation(const string& filename = string(), const string& funcName = string()) throw()
  : functionName(funcName) {
    }
  private:
    string fileName;
    string functionName;
  };
  class Exception {
  public:
    Exception() throw();
    Exception(const string& errorText, const unsigned long& errorId = 0) throw();
    Exception& addLocation(const ExceptionLocation& location) throw();
  };
  class FooError
      : public FooNamespace::Exception {
  public:
    FooError() throw()
    : FooNamespace::Exception() {
    }
    FooError(string a, unsigned long b = 0) throw()
  : FooNamespace::Exception(a, b) {
    };
  };
  class EndOfFile
    : public FooNamespace::FooError {
  public:
    EndOfFile() throw()
    : FooNamespace::FooError() {
    }
    EndOfFile(string a, unsigned long b = 0) throw()
  : FooNamespace::FooError(a, b) {
    };
  };
  class FooTextStream : public std::fstream {
  public:
    inline void Fubar(const bool expectEOF = false ) throw(EndOfFile, FooError, FooNamespace::Exception) {
      try {
        const int MAX_LINE_LENGTH = 256;
        char templine[MAX_LINE_LENGTH + 1];
        getline(templine, MAX_LINE_LENGTH);
        EndOfFile err("");
      }
      catch(std::exception &e) {
        if (expectEOF) {
          EndOfFile err("");
          err.addLocation(FooNamespace::ExceptionLocation("", ""));
          throw err;
        }
      }
    };
  };
  class BarHeader {
    virtual void dump(std::ostream& s) const {
      s << endl;
    }
    virtual void DoIt(std::fstream& s);
  };
  void BarHeader::DoIt(std::fstream& ffs) {
    FooTextStream* buz = 0;
    buz->Fubar();
  }
}
