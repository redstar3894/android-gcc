static inline __attribute__((always_inline)) int
__pskb_trim(void)
{
  return ___pskb_trim();
}
static inline __attribute__((always_inline))
int pskb_trim(void)
{
  return __pskb_trim();
}
inline __attribute__((noinline)) int ___pskb_trim(void)
{
  pskb_trim();
  return 0;
}

