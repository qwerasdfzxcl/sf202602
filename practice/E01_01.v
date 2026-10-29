Require Import P01.

Check double_injective :
  forall n m : nat,
    n + n = m + m -> n = m.
