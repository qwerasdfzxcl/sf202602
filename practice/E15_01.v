Require Import P15.

Check subseq_app_split : forall (A : Type) (xs ys zs : list A),
  subseq xs (ys ++ zs) ->
  exists left right,
    xs = left ++ right /\ subseq left ys /\ subseq right zs.
