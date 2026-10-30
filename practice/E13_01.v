Require Import P13.

Check rle_gap : forall n m,
  rle n m <-> exists d, m = n + d.
