/* { dg-options "-lm -ffvpt -ffvpt-functions=log,exp,pow,sqrt -O2 -fdump-tree-optimized -fdump-tree-tree_profile" } */

#define VAL (-1.0/0.0)

#include "ffvpt-pro.h"

/* { dg-final-use { scan-tree-dump-not "Invalid sum" "optimized"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(exp\\) to constant value: -inf in main \\(use 0.000000\\) \\(count:1000, all:1000\\)" "tree_profile"} } */
/* { dg-final-use { scan-tree-dump-not "Math call \\(pow\\) with constant argument optimized" "tree_profile"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(log\\) to constant value: -inf in main \\(use -?nan\\) \\(count:1000, all:1000\\)" "tree_profile"} } */
/* { dg-final-use { scan-tree-dump "Math call \\(sqrt\\) to constant value: -inf in main \\(use -?nan\\) \\(count:1000, all:1000\\)" "tree_profile"} } */

/* { dg-final-use { cleanup-tree-dump "optimized" } } */
/* { dg-final-use { cleanup-tree-dump "tree_profile" } } */
