Require Import P14.

Check subseq_trans : forall (A : Type) (xs ys zs : list A),
  subseq xs ys -> subseq ys zs -> subseq xs zs.
