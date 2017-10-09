Ltac des t :=
  destruct t eqn:?; simpl in *; try intuition congruence.

Ltac destr :=
  match goal with
    |- context [match ?a with _ => _ end] =>
    des a
  end.

Ltac destr_in H :=
  match type of H with
    context [match ?a with _ => _ end] =>
    des a
  end.

Ltac inv H := inversion H; try subst; clear H.

Ltac destr_in_all :=
  repeat match goal with
           H: context [match ?a with _ => _ end] |- _ =>
           des a
         | H: Some _ = Some _ |- _ => inversion H; subst; clear H
         end.
