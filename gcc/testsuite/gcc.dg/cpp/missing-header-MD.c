/* Test that missing user headers are fatal errors with -MD.  */
/* { dg-do compile } */
/* { dg-options "-MD" } */

#include "nonexistent.h" /* { dg-error "nonexistent.h" } */
