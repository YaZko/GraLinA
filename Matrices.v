Require Import ZArith nodep NatGraph EvalGraph.

Ltac gremember t gn :=
  generalize (Refl t); generalize t at 1 as gn;
  let Hgn := fresh "H"gn in
  intros gn Hgn;
  rewrite <- ! Hgn.

Tactic Notation "gremember" constr(t) "as" ident(i) := gremember t i.

Definition beast a b c d :=
  (-< ⊕ -<) ∘ (-- ⊕ >< ⊕ --) ∘ (nat_graph a ⊕ nat_graph b ⊕ nat_graph c ⊕ nat_graph d) ∘ (>- ⊕ >-).

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


Qed.
