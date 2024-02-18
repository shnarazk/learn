! Copyright (C) 2024 Narazaki, Shuji.
! See https://factorcode.org/license.txt for BSD license.
USING: kernel math ;
IN: leibniz

: lpi ( num-of-pairs: integer -- pi )
  0.0 0 rot
  [ [ 4.0 * [ 3.0 + ] [ 1.0 + ] bi * 2.0 swap / + ] keep 1 + ] times
  drop 4 *
;
