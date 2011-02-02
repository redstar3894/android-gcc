/* { dg-do compile { target {{ i?86-*-* x86_64-*-* } && lp64 } } } */
/* { dg-options "-O2  -m64 -fdump-tree-ivopts-details" } */
int inner_longest_match(char *scan, char *match, char *strend)
{
  char *start_scan = scan;
  do {
  } while (*++scan == *++match && *++scan == *++match &&
           *++scan == *++match && *++scan == *++match &&
           *++scan == *++match && *++scan == *++match &&
           *++scan == *++match && *++scan == *++match &&
           scan < strend);

  return scan - start_scan;
}

/* { dg-final { scan-tree-dump-times "Sinking" 7 "ivopts"} } */
/* { dg-final { cleanup-tree-dump "ivopts" } } */
