/* { dg-do compile } */
/* { dg-options "-Winline -O2" } */
inline __attribute__ ((always_inline)) void t(void); /* { dg-message "error\[^\n\]*body not available" "" } */
void
q(void)
{
  t(); 				/* { dg-message "error\[^\n\]*called from here" "" } */
}
