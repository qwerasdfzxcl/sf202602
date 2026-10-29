Require Import P07.

Check fold_left_app :
  forall (A B : Type) (f : B -> A -> B)
         (xs ys : list A) (z : B),
    fold_left f (xs ++ ys) z =
    fold_left f ys (fold_left f xs z).

Check fold_left_rev_acc :
  forall (A : Type) (xs acc : list A),
    fold_left (fun acc x => x :: acc) xs acc = rev xs ++ acc.
