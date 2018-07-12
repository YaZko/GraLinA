Require Import ZArith nodep NatGraph EvalGraph List.

Ltac gremember t gn :=
  generalize (Refl t); generalize t at 1 as gn;
  let Hgn := fresh "H"gn in
  intros gn Hgn;
  rewrite <- ! Hgn.

Tactic Notation "gremember" constr(t) "as" ident(i) := gremember t i.


Fixpoint copy_gen n :=
  match n with
    O => -o
  | S n => -< ∘ (-- ⊕ copy_gen n)
  end.

Lemma copy_0:
  copy_gen O == -o .
Proof.
  reflexivity.
Qed.

(* Lemma test_copy: *)
(*   copy_gen 4 == -< ∘ (-< ⊕ --) ∘ (-< ⊕ -- ⊕ --). *)
(* Proof. *)
(*   simpl. *)
(*   rewrite <- ! AssocComp. *)
(*   rewrite MFI; simpl; auto. *)
(*   rewrite (IdRightGen _ --); simpl; Simpl. 2: reflexivity. *)
(*   rewrite copy_then_discard by reflexivity. *)
(*   rewrite (IdRightGen _ (-- ⊕ --)); simpl; Simpl. 2: reflexivity. *)
(*   rewrite CoAssoc. *)
(*   rewrite CoComm at 1. *)
(*   rewrite <- AssocComp. *)
(*   generalize (twist_simpl (-< ∘ (-- ⊕ -<)) --). intro H. *)
(*   rewrite ! twister_twist in H. *)
(*   simpl gout in H. *)
(*   rewrite <- H. *)
(* Qed. *)

Definition beast a b c d :=
  (-< ⊕ -<) ∘ (-- ⊕ >< ⊕ --) ∘ (nat_graph a ⊕ nat_graph b ⊕ nat_graph c ⊕ nat_graph d) ∘ (>- ⊕ >-).

Fixpoint sumlist (gl: list Graph): Graph :=
    match gl with
      nil => ∅
    | a::r => a ⊕ sumlist r
    end.


Lemma oplus_8:
  forall a b c d e f g h,
    (((a ⊕ b) ⊕ (c ⊕ d)) ⊕ ((e ⊕ f) ⊕ (g ⊕ h))) ==
    sumlist (a::b::c::d::e::f::g::h::nil).
Proof.
  simpl.
  intros; rewrite ! AssocSum. Simpl. reflexivity.
Qed.

Ltac simpl_gin_gout :=
  rewrite ?gin_idm, ?gin_twister, ?gin_twist_aux, ?gout_idm, ?gout_twister, ?gout_twist_aux, ?gin_bizarro_gout, ?gout_bizarro_gin, ? gin_nat_graph, ? gout_nat_graph.

Ltac solve_gin_gout:=
  simpl; simpl_gin_gout; try omega.
Lemma twist_2_copy:
  >< ∘ (-< ⊕ -<) == (-< ⊕ -<) ∘ (twister 2 2).
Proof.
  rewrite <- twister_twist.
  change 1 with (gin -<) at 1 2.
  rewrite <- twist_simpl. reflexivity.
Qed.

Lemma slide_twister_inside_sum:
  forall a b c n m,
    gout b = gin (twister n m) ->
    (a ⊕ (b ∘ (twister n m) ⊕ c)) ==
    (a ⊕ (b ⊕ c)) ∘ (≡gout a≡ ⊕ ((twister n m) ⊕ ≡ gout c≡)).
Proof.
  intros.
  transitivity ((a∘≡gout a≡) ⊕ (b ∘ (twister n m) ⊕ c ∘ ≡gout c≡)).
  - rewrite ! IdRight. reflexivity.
  - rewrite MFI.
    2-3: simpl; revert H; simpl_gin_gout; rewrite ? gin_nat_graph, ? gout_nat_graph; intro; try omega.
    rewrite MFI.
    2-3: simpl; revert H; simpl_gin_gout; rewrite ? gin_nat_graph, ? gout_nat_graph; intro; try omega.
    reflexivity.      
Qed.

Lemma slide_twister_inside_sum_rev:
  forall a b c n m,
    gin b = gin (twister n m) ->
    (a ⊕ ((twister n m) ∘ b ⊕ c)) ==
    (≡gin a≡ ⊕ ((twister n m) ⊕ ≡ gin c≡)) ∘    (a ⊕ (b ⊕ c)) .
Proof.
  intros.
  transitivity ((≡gin a≡∘a) ⊕ ((twister n m) ∘ b ⊕ ≡gin c≡∘c)).
  - rewrite ! IdLeft. reflexivity.
  - rewrite MFI.
    2-3: simpl; revert H; simpl_gin_gout; rewrite ? gin_nat_graph, ? gout_nat_graph; intro; try omega.
    rewrite MFI.
    2-3: simpl; revert H; simpl_gin_gout; rewrite ? gin_nat_graph, ? gout_nat_graph; intro; try omega.
    reflexivity.      
Qed.


Lemma sumlist_app:
  forall l1 l2,
    sumlist (l1 ++ l2) == sumlist l1 ⊕ sumlist l2.
Proof.
  induction l1; simpl; intros; eauto.
  Simpl; reflexivity.
  rewrite IHl1.
  rewrite AssocSum. reflexivity.
Qed.

Lemma gin_sumlist:
  forall l,
    gin (sumlist l) = fold_right plus 0 (map gin l).
Proof.
  induction l; simpl; intros; eauto.
Qed.

Lemma eqG_gin:
  forall g1 g2,
    g1 == g2 -> gin g1 = gin g2.
Proof.
  intros.
  apply eqG_same_arity in H. intuition.
Qed.


Lemma eqG_gout:
  forall g1 g2,
    g1 == g2 -> gout g1 = gout g2.
Proof.
  intros.
  apply eqG_same_arity in H. intuition.
Qed.

Lemma simpl_sumlist_id:
  forall n1 l1 l2 g,
    n1 = gin (sumlist l1) ->
    gout g = gin (sumlist l2) ->
    (≡n1≡ ⊕ g) ∘ (sumlist (l1 ++ l2)) == (sumlist l1) ⊕ (g ∘ (sumlist l2)).
Proof.
  intros.
  rewrite sumlist_app.
  rewrite MFI. 2-3: subst; simpl_gin_gout; auto.
  rewrite H, IdLeft.
  reflexivity.
Qed.

Lemma twister_sumlist:
  forall ln lm,
    (twister (gin (sumlist lm)) (gin (sumlist ln))) ∘ (sumlist (ln ++ lm)) ==
    (sumlist (lm ++ ln)) ∘ (twister (gout (sumlist lm)) (gout (sumlist ln))).
Proof.
  intros. rewrite ! sumlist_app.
  rewrite twist_simpl. reflexivity.
Qed.

Lemma simpl_sumlist_twister:
  forall n m k ln lm lk,
    gin (sumlist ln) = n ->
    gin (sumlist lm) = m ->
    gin (sumlist lk) = k ->
    (twister m n ⊕ ≡ k ≡) ∘ (sumlist (ln ++ lm ++ lk)) == sumlist (lm ++ ln ++ lk) ∘ (twister (gout (sumlist lm)) (gout (sumlist ln)) ⊕ ≡ gout (sumlist lk) ≡).
Proof.
  intros.
  rewrite app_assoc. rewrite sumlist_app.
  rewrite MFI.
  2: simpl; simpl_gin_gout.
  2: erewrite eqG_gin. 3: apply sumlist_app. 2: simpl; omega.
  2: simpl; simpl_gin_gout; omega.
  rewrite app_assoc. rewrite (sumlist_app (lm ++ ln)).
  rewrite MFI.
  2: simpl; simpl_gin_gout.
  2: erewrite eqG_gout. 3: apply sumlist_app. 2: simpl; omega.
  2: simpl; simpl_gin_gout; omega.
  apply CongSum.
  subst. apply twister_sumlist.
  rewrite IdRight. subst. rewrite IdLeft. reflexivity.
Qed.

Lemma simpl_sumlist_twister':
  forall o n m k ln lm lk lo,
    gin (sumlist ln) = n ->
    gin (sumlist lm) = m ->
    gin (sumlist lk) = k ->
    gin (sumlist lo) = o ->
    (≡ o ≡ ⊕ (twister m n ⊕ ≡ k ≡)) ∘ (sumlist (lo ++ ln ++ lm ++ lk)) ==
    sumlist (lo ++ lm ++ ln ++ lk) ∘
            (≡ gout (sumlist lo) ≡ ⊕ twister (gout (sumlist lm)) (gout (sumlist ln)) ⊕ ≡ gout (sumlist lk) ≡).
Proof.
  intros.
  rewrite simpl_sumlist_id. 2: auto.
  2: simpl; simpl_gin_gout.
  2: erewrite eqG_gin. 3: apply sumlist_app. 2: simpl.
  2: erewrite (eqG_gin (sumlist (_ ++ _))). 3: apply sumlist_app. 2: simpl; omega.
  rewrite (sumlist_app lo).
  rewrite <- ! AssocSum.
  rewrite MFI.
  2: simpl; simpl_gin_gout; auto.
  2: simpl; simpl_gin_gout; auto.
  2: erewrite eqG_gout. 3: apply sumlist_app.
  2: simpl.
  2: erewrite (eqG_gout (sumlist (app _ _))). 3: apply sumlist_app.
  2: simpl; omega.
  rewrite IdRight.
  rewrite simpl_sumlist_twister; auto. reflexivity.
Qed.

Lemma simpl_sumlist_twister'':
  forall o n m k ln lm lk lo o' n' m' k',
    gin (sumlist ln) = n ->
    gin (sumlist lm) = m ->
    gin (sumlist lk) = k ->
    gin (sumlist lo) = o ->
    gout (sumlist ln) = n' ->
    gout (sumlist lm) = m' ->
    gout (sumlist lk) = k' ->
    gout (sumlist lo) = o' ->
    (≡ o ≡ ⊕ (twister m n ⊕ ≡ k ≡)) ∘ (sumlist (lo ++ ln ++ lm ++ lk)) ==
    sumlist (lo ++ lm ++ ln ++ lk) ∘ (≡ o' ≡ ⊕ twister m' n' ⊕ ≡ k' ≡).
Proof.
  intros.
  subst.
  apply simpl_sumlist_twister'; auto.
Qed.


Lemma sumlist_app_2_2:
  forall a b c d,
    sumlist (a ++ b ++ c ++ d) == sumlist (a++b) ⊕ sumlist (c++d).
Proof.
  intros.
  rewrite <- sumlist_app. rewrite ! app_assoc. reflexivity.
Qed.


Lemma comp_beast:
  forall a b c d e f g h,
    (beast a b c d) ∘ (beast e f g h) == beast (e*a + f*c) (e*b + f*d) (g*a+h*c) (g*b+h*d).
Proof.
  intros.
  unfold beast at 1 2.
  rewrite <- ! AssocComp.
  rewrite (AssocComp (>- ⊕ >-)).
  rewrite (MFI >- -< >- -<) by reflexivity.
  rewrite B1.

  match goal with
    |- context[ (?g ⊕ nat_graph d) ∘ ((?g1 ⊕ _) ∘ ?g2)] =>
    gremember (g ⊕ nat_graph d) as gA;
      gremember g1 as gB;
      gremember g2 as gC
  end.
  rewrite <- AssocComp in HgB.
  match type of HgB with
    _ == ?gb1 ∘ ?gb2 =>
    revert HgB;
      gremember gb1 as gB1;
      gremember gb2 as gB2
  end.
  intro.
  rewrite H.
  rewrite (AssocComp gA).
  rewrite <- (AssocSum _ (nat_graph c)) in HgA.
  rewrite HgA.
  rewrite MFI.
  2-3: simpl; rewrite (proj2 (proj2 (eqG_same_arity _ _ HgB1))); simpl;
    rewrite ? gin_nat_graph, ? gout_nat_graph; omega.
  rewrite ! (AssocComp _ gB1 gB2).
  rewrite HgB1.
  rewrite ! (MFI _ -< _ -<) by (rewrite gout_nat_graph; reflexivity).
  rewrite ! nat_copy.
  rewrite <- (MFI _ gB2 _ gB2).
  2-3: simpl; rewrite (proj2 (proj2 (eqG_same_arity _ _ HgB2))); simpl;
    rewrite ? gin_nat_graph, ? gout_nat_graph; omega.
  rewrite <- (AssocComp _ (gB2 ⊕ gB2) gC).
  rewrite AssocComp in HgC.
  rewrite MFI in HgC  by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; omega).
  rewrite <- AssocSum in HgC.
  rewrite (MFI -- _ ><) in HgC by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
  rewrite <- twister_twist in HgC.
  replace 1 with (gin (nat_graph g)) in HgC at 1 by (rewrite gin_nat_graph; auto).
  replace 1 with (gin (nat_graph f)) in HgC by (rewrite gin_nat_graph; auto).
  rewrite <- twist_simpl in HgC. rewrite ! gout_nat_graph, twister_twist in HgC.
  rewrite ! (IdLeftGen --) in HgC. 
  all: rewrite ? idm1, ? gin_nat_graph; try reflexivity.
  assert (HgC': gC == (nat_graph e ⊕ nat_graph g ⊕ nat_graph f ⊕ nat_graph h) ∘ (-- ⊕ >< ⊕ --) ∘ (>- ⊕ >-)).
  rewrite HgC.
  rewrite (MFI _ _ _ --)by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
  rewrite <- (AssocSum (nat_graph e) (nat_graph g)).
  rewrite (MFI _ _ _ ><)by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
  rewrite ! (IdRightGen _ --). reflexivity. 
  all: rewrite ? idm1, ? gin_nat_graph, ? gout_nat_graph; try reflexivity.
  clear HgC; rename HgC' into HgC.
  rewrite <- AssocComp in HgC.
  rewrite <- ! AssocSum in HgC.
  rewrite (AssocSum (_ e) (_ g)) in HgC.


  assert ((gB2 ⊕ gB2) ∘ gC == (((-- ⊕ ><) ⊕ --) ∘ ((nat_graph e ⊕ nat_graph e) ∘ >- ⊕ (nat_graph g ⊕ nat_graph g) ∘ >-)
                                                ⊕ ((-- ⊕ ><) ⊕ --) ∘ ((nat_graph f ⊕ nat_graph f) ∘ >- ⊕ (nat_graph h ⊕ nat_graph h) ∘ >-))
                                ∘ ((-- ⊕ (>< ⊕ --)) ∘ (>- ⊕ >-)) ) .
  {
    rewrite HgC.
    rewrite ! AssocComp.
    rewrite (MFI gB2 _ gB2).
    2-3: simpl; rewrite ? (proj1 (proj2 (eqG_same_arity _ _ HgB2))); simpl;
      rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
    rewrite HgB2.
    rewrite <- ! AssocComp.
    rewrite ! (MFI >- _ >-) by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
    rewrite <- ! adding.
    reflexivity.
  }
  rewrite H0.
  clear.
  rewrite ! AssocComp.


  rewrite <- (AssocComp _ ((-< ∘ (_ ⊕ _) ⊕ _) ⊕ (_ ⊕ _))).

  assert (
      forall e g,
        ((-- ⊕ ><) ⊕ --) ∘ ((nat_graph e ⊕ nat_graph e) ∘ >- ⊕ (nat_graph g ⊕ nat_graph g) ∘ >-)
        ==
        ((nat_graph e ⊕ (nat_graph g ⊕ nat_graph e) ⊕ nat_graph g) ∘ (-- ⊕ >< ⊕ --) ∘ (>- ⊕ >-))).
  {
    clear.
    intros e g.
    rewrite <- MFI.
    2-3: simpl; rewrite ! gout_nat_graph; reflexivity.
    rewrite <- ! AssocSum.
    rewrite AssocComp.
    rewrite (MFI -- (nat_graph e))  by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
    rewrite AssocSum.
    rewrite (MFI >< (nat_graph e ⊕ _))  by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
    rewrite <- twister_twist.
    replace 1 with (gin (nat_graph g)) at 1 by (rewrite gin_nat_graph; auto).
    replace 1 with (gin (nat_graph e)) by (rewrite gin_nat_graph; auto).
    rewrite <- twist_simpl. rewrite ! gout_nat_graph, twister_twist.
    rewrite ! (IdLeftGen --). 
    all: rewrite ? idm1, ? gin_nat_graph; try reflexivity.
    rewrite <- idm1.
    rewrite (MFI _ --) by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
    rewrite twister_twist.
    rewrite (AssocSum (nat_graph g) (nat_graph e)).
    rewrite (MFI _ ><)by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega).
    rewrite ! (IdRightGen _ --). reflexivity. 
    all: rewrite ? idm1, ? gin_nat_graph, ? gout_nat_graph; try reflexivity.
  }
  rewrite H.
  rewrite H.
  rewrite <- ! AssocComp.
  rewrite <- ! AssocSum.
  rewrite <- idm1.

  rewrite (AssocComp ((-< ∘ (nat_graph a ⊕ nat_graph a)) ⊕ _)).
  rewrite (AssocSum (-< ∘ (nat_graph a ⊕ nat_graph a))).
  rewrite (MFI ((-< ∘ (nat_graph a ⊕ nat_graph a)) ⊕ _)).
  2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.

  rewrite (AssocComp _ (nat_graph e ⊕ _)).
  rewrite (AssocSum (nat_graph e)).
  rewrite (MFI (-< ∘ (nat_graph a ⊕ nat_graph a))).
  2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.

  rewrite (AssocComp _ (nat_graph f ⊕ _)).
  rewrite (AssocSum (nat_graph f)).
  rewrite (MFI (-< ∘ (nat_graph c ⊕ nat_graph c))).
  2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.

  rewrite <- ! (AssocComp -<).
  rewrite ! (MFI (nat_graph _)) by (rewrite ? gin_nat_graph, ? gout_nat_graph; auto).
  rewrite ! nat_mul.
  clear. 
  rewrite <- ! (MFI -< _ -<) by solve_gin_gout.
  rewrite <- ! (AssocComp (-< ⊕ -<)).

  rewrite <- ! (MFI (-< ⊕ -<) _ (-< ⊕ -<)) by solve_gin_gout.


  rewrite (AssocComp (-- ⊕ (>< ⊕ --))).
  rewrite (AssocComp (-- ⊕ (>< ⊕ --))).
  rewrite <- ! (AssocSum -<).
  rewrite (MFI -- -<) by solve_gin_gout.

  rewrite ! (AssocSum -<).
  rewrite (MFI >< (-< ⊕ -<)) by solve_gin_gout.

  rewrite ! (IdLeftGen --).
  2: simpl; rewrite idm1; Simpl; reflexivity.


  Definition permut_type := nat -> nat.

  Record is_permut n p :=
    {
      is_permut_range: forall i, i < n -> p i < n;
      is_permut_inj: forall i j, i < j -> j < n -> p i <> p j;
      is_permut_has_antecedant: forall i, i < n -> { x: nat | x < n /\ p x = i };
      (* the latter should be provable but cumbersome to prove *)
    }.

  Fixpoint graph_permut n p (IP: is_permut n p) : Graph.
  Proof.
    destruct n.
    exact Empty.
    edestruct (is_permut_has_antecedant _ _ IP O) as (x & LT & EQ).
    omega.

    set (p' := fun i => 

    :=
    match n with
      O => Empty
    | S m =>
      
      if eq_nat_dec (p O) O
      then -- ⊕ graph_permut m (fun x => if eq_nat_dec x O then p 1 else p (x-1))
      else 
    end.

  (* nat_graph_sum: forall n m : nat, (-< ∘ (nat_graph m ⊕ nat_graph n)) ∘ >- == nat_graph (m + n) *)

  rewrite <- ! (MFI _ ((-- ⊕ (>< ⊕ --)) ∘ (>- ⊕ >-))).
  2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
  rewrite oplus_8.
  match goal with
    |- context [sumlist ?a] => remember a
  end.

  (* rewrite twist_2_copy. *)
  rewrite <- twister_twist at 1.
  rewrite slide_twister_inside_sum_rev by solve_gin_gout.
  simpl gin.
  rewrite twister_twist, <- idm1.

  rewrite !AssocComp.
  rewrite <- (AssocComp _ (sumlist _)).

  assert (l =
          (nat_graph (a*e) :: nat_graph (a*g) :: nat_graph (b*e) :: nat_graph (b*g) ::nil)
            ++ (nat_graph (c*f) :: nat_graph (c*h) :: nat_graph (d*f) :: nat_graph (d*h) ::nil)).
  subst. simpl. reflexivity. clear Heql.
  subst.
  rewrite sumlist_app.
  rewrite (MFI (sumlist _)) by solve_gin_gout.


  Lemma test:
    forall a b c d,
      (sumlist (nat_graph a :: nat_graph b :: nat_graph c :: nat_graph d :: nil))
        ∘ ((-- ⊕ (>< ⊕ --)) ∘ (>- ⊕ >-)) ==
      (-- ⊕ (>< ⊕ --)) ∘ (nat_graph a ⊕ nat_graph c ⊕ nat_graph b ⊕ nat_graph d) ∘ (>- ⊕ >-).
  Proof.
    simpl; intros. Simpl.
    rewrite AssocComp.
    rewrite (MFI (nat_graph a)) by solve_gin_gout.
    rewrite AssocSum.
    rewrite (MFI (nat_graph b ⊕ nat_graph c)) by solve_gin_gout.
    rewrite ! AssocSum.
    rewrite (MFI _ _ --) by solve_gin_gout.
    rewrite <- ! AssocSum.
    rewrite (MFI _ _ ><) by solve_gin_gout.
    generalize (twist_simpl (nat_graph b) (nat_graph c)).
    simpl_gin_gout.
    intro TS.
    rewrite twister_twist in TS.
    rewrite <- TS.
    rewrite ! (IdRightGen _ --).
    2-3: simpl_gin_gout; rewrite idm1; reflexivity.
    rewrite ! (IdLeftGen --).
    2-3: simpl_gin_gout; rewrite idm1; reflexivity.
    rewrite ! AssocSum. reflexivity.
  Qed.

  rewrite ! test.


  


  rewrite simpl_sumlist_twister'.
  2-6: simpl; rewrite ? gin_nat_graph; simpl_gin_gout; omega.
  rewrite ! sumlist_app. simpl.
  rewrite ! gout_nat_graph. simpl.
  Simpl.
  


  rewrite <- (AssocComp _ ( (≡2≡⊕ twister 2 2) ⊕ ≡2≡)).


  rewrite (AssocComp _ ((nat_graph _ ⊕ _) ⊕ _)).

  rewrite (MFI -< _ ((-< ⊕ _) ⊕ _)) by solve_gin_gout.
  rewrite AssocSum.
  rewrite (MFI (-< ⊕ _) _ -<) by solve_gin_gout.
  rewrite (MFI -< _ -<) by solve_gin_gout.


  rewrite (AssocComp _ ( (≡2≡⊕ twister 2 2) ⊕ ≡2≡)).

  assert (
      -< ∘ (nat_graph (a * e) ⊕ nat_graph (a * g))
         ⊕ ((-< ∘ (nat_graph (c * f) ⊕ nat_graph (c * h)) ⊕ -< ∘ (nat_graph (b * e) ⊕ nat_graph (b * g)))
              ⊕ -< ∘ (nat_graph (d * f) ⊕ nat_graph (d * h))) ==
      sumlist
        (((-< ∘ (nat_graph (a * e) ⊕ nat_graph (a * g)))::nil)
           ++ ((-< ∘ (nat_graph (c * f) ⊕ nat_graph (c * h))) :: nil)
           ++ ((-< ∘ (nat_graph (b * e) ⊕ nat_graph (b * g))) :: nil)
           ++ (-< ∘ (nat_graph (d * f) ⊕ nat_graph (d * h)))::nil)).
  {
    simpl. Simpl. rewrite ! AssocSum. reflexivity.
  }
  rewrite H.

  rewrite <- simpl_sumlist_twister''.
  2-9: solve_gin_gout; eauto.
  simpl plus.
  rewrite <- (AssocComp _ (sumlist _)).
  rewrite (AssocComp (sumlist _)).

  rewrite sumlist_app_2_2.

  rewrite (MFI (sumlist _) _ (sumlist _)) by solve_gin_gout.


  Lemma sumlist_twist_add:
    (sumlist ((-< ∘ (a ⊕ b) :: nil) ++ -< ∘ (c ⊕ d) :: nil)) ∘ ((-- ⊕ (>< ⊕ --)) ∘ (>- ⊕ >-)) ==
    sumlist 


      gremember (-< ⊕ (>< ∘ (-< ⊕ -<) ⊕ -<)) as g1.

    assert (g1 == (-- ⊕ (>< ⊕ --)) ∘ (-< ⊕ ((-< ⊕ -<) ⊕ -<))).
    {
      rewrite Hg1.
      rewrite (MFI -- -<) .
      2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
      rewrite (MFI >< _ --) .
      2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
      rewrite ! (IdLeftGen --).
      2: simpl; rewrite idm1; Simpl; reflexivity.
      reflexivity.
    }

    rewrite H.
    rewrite <- (AssocComp (-- ⊕ (>< ⊕ --))).

    rewrite H0.
    Opaque sumlist map.
    clear H0.

    rewrite <- (MFI (-- ⊕ (>< ⊕ --)) (>- ⊕ >-)).
    2-3: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.


    Lemma simpl_double_copy_twist:

      (-< ⊕ -<) ∘ (-- ⊕ >< ⊕ --) ∘ (-< ⊕ -< ⊕ -< ⊕ -<)


  Qed.
