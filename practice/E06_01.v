Require Import P06.

Check nth_error_ext :
  forall (A : Type) (xs ys : list A),
    (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
