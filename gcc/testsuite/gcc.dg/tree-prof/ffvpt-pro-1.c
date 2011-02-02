/* { dg-options "-lm -ffvpt -ffvpt-functions=log,exp,pow,sqrt -O2 -fdump-tree-optimized -fdump-tree-tree_profile" } */

#define VAL 1.0

#include "ffvpt-pro.h"

/* { dg-final-use { scan-tree-dump-not "Invalid sum" "optimized"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(exp\\) to constant value: 1.000000 in main \\(use 2.718282\\) \\(count:1000, all:1000\\)" "tree_profile"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(pow\\) with constant argument \\(1.000000\\) optimized in main: \\(count:1000, all:1000\\)" "tree_profile"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(log\\) to constant value: 1.000000 in main \\(use 0.000000\\) \\(count:1000, all:1000\\)" "tree_profile"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(sqrt\\) to constant value: 1.000000 in main \\(use 1.000000\\) \\(count:1000, all:1000\\)" "tree_profile"} } */

/* { dg-final-use { cleanup-tree-dump "optimized" } } */
/* { dg-final-use { cleanup-tree-dump "tree_profile" } } */
