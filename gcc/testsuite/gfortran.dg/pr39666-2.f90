! PR middle-end/39666
! { dg-do compile }
! { dg-options "-O2 -Wuninitialized" }

FUNCTION f(n)
  INTEGER, INTENT(in) :: n
  REAL                :: f

  SELECT CASE (n)	! { dg-warning "may be used uninitialized" }
    CASE (:-1); f = -1.0
    CASE (0);   f =  0.0
    CASE (2:);  f =  1.0
  END SELECT
END FUNCTION
