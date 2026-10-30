Require Import P16.

Check star_concat : forall (A : Type) (s1 s2 : list A) (re : reg_exp A),
  s1 =~ Star re -> s2 =~ Star re -> (s1 ++ s2) =~ Star re.
