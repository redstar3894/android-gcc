/* { dg-do compile } */
/* { dg-options "-O2" } */

/* If f3() is inlined the impossible-to-resolve situation of a cycle
   of always_inlined functions is created in the call graph.  This
   test tests whether this condition is detected and avoided.  */

inline void f1(int);
inline void f2(int);
inline void f3(int);

inline void __attribute__((__always_inline__)) f1(int a) {
  f3(a);
  f3(a);
}

inline void __attribute__((__always_inline__)) f2(int a) {
  f1(a);
}

inline void f3(int a) {
  f2(a);
}
