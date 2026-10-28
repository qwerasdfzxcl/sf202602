Require Export D.

(** Exercise 1. Implement function greater_triple n m = true <-> 3n < m. Use no arithmetic of natural number**)

Fixpoint greater_triple (n m : nat) : bool :=
  match n with
  | 0 =>
    match m with
    | 0 => false
    | _ => true
    end
  | S n' => 
    match m with
    | 0 => false
    | S 0 => false
    | S (S 0) => false
    | S (S (S m')) => greater_triple n' m'
    end
  end.
