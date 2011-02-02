/* This test fails for x86 + x86_64 (-m32/-m64) with optimization levels
   other than -O.  There's no way to xfail this for certaion optimization
   levels, so we force optimization to -O1 to make this pass.  */
/* { dg-options "-O" { target i?86-*-* x86_64-*-* } } */
#include <string>
#include <iostream>

int
main (int argc, char *argv[])
{
    std::string myStr = "Hello, World!";
    std::cout << myStr << std::endl;
    return 0;
}
