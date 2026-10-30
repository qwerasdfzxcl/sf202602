Require Import P12.

Check ev_add_cancel : forall n m,
  ev n -> (ev (n + m) <-> ev m).
