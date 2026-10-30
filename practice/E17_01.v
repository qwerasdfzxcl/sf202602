Require Import P17.

Check star_flatten : forall (A : Type) (s : list A) (re : reg_exp A),
  s =~ Star (Star re) <-> s =~ Star re.
