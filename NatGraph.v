Require Import List nodep Tactics EvalGraph.
Require Import ZArith.

Fixpoint nat_graph (n: nat) : Graph :=
  match n with
  | O => -o ∘ o-
  | S k => -< ∘ (nat_graph k ⊕ --) ∘ >-
  end.

Lemma nat_graph_1:
  nat_graph 1 == --.
Proof.
  simpl.
  assert (-- == -- ∘ --). rewrite idm1. symmetry; apply IdLeftGen. simpl_gin_gout. reflexivity.
  rewrite H at 1.
  rewrite <- MFI; simpl; auto.
  rewrite <- ! AssocComp.
  rewrite <- Unit.
  rewrite AssocComp.
  rewrite CoUnit. symmetry; auto.
Qed.

Lemma gin_nat_graph:
  forall n, gin (nat_graph n) = 1.
Proof.
  induction n; simpl; intros; auto.
Qed.


Lemma gout_nat_graph:
  forall n, gout (nat_graph n) = 1.
Proof.
  induction n; simpl; intros; auto.
Qed.


Lemma eval_graph_mul:
  forall n x,
    graph_eval _ plus O (x::nil) (nat_graph n) = Some (n*x::nil).
Proof.
  induction n; simpl; intros; auto.
  rewrite gin_nat_graph. simpl.
  rewrite IHn. simpl. f_equal. f_equal. omega.
Qed.

Lemma copy_then_discard:
  forall g,
    gin g = 1 ->
    -< ∘ (g ⊕ -o) == g.
Proof.
  intros. rewrite CoComm.
  rewrite <- AssocComp.
  rewrite <- twister_twist.
  rewrite <- H at 2. replace 1 with (gin -o).
  rewrite <- twist_simpl.
  simpl.
  rewrite AssocComp. rewrite IdRightGen. 2: reflexivity.
  2: reflexivity.
  transitivity (-< ∘ (-o ⊕ --) ∘ (∅ ⊕ g)).
  rewrite <- AssocComp. rewrite MFI. simpl. Simpl. rewrite (IdLeftGen -- g).
  reflexivity.
  rewrite H, idm1. reflexivity. reflexivity.
  rewrite H; reflexivity.
  rewrite CoUnit. Simpl. rewrite IdLeftGen. reflexivity.
  rewrite H, idm1; reflexivity.  
Qed.

Lemma sum_comp_distr:
  forall a b c,
    gout b = gin c ->
    a ⊕ (b ∘ c) == (a ⊕ b) ∘ (≡gout a≡ ⊕ c).
Proof.
  intros.
  rewrite MFI. rewrite IdRight. reflexivity. simpl_gin_gout. auto. auto.
Qed.

Lemma nat_graph_sum:
  forall n m,
    -< ∘ (nat_graph m ⊕ nat_graph n) ∘ >- == nat_graph (m+n).
Proof.
  induction n.
  - simpl; intros. rewrite <- ! AssocComp.
    rewrite <- (HorizontalSliding2 (nat_graph m)). simpl. Simpl.
    rewrite gout_nat_graph. simpl.
    Simpl.
    assert (-- == -- ∘ --).
    rewrite IdLeftGen; simpl; Simpl; reflexivity.
    rewrite H at 2. rewrite <- MFI.
    rewrite <- ! AssocComp.
    rewrite tropcool.
    rewrite idm1 at 3.
    rewrite IdRight.
    rewrite MFI.
    rewrite idm1. rewrite IdRight'. rewrite IdLeft'.
    all: simpl; rewrite ? gout_nat_graph; auto.
    rewrite <- plus_n_O.
    apply copy_then_discard. rewrite gin_nat_graph; auto.
  - intros.
    simpl.
    rewrite sum_comp_distr.
    rewrite gout_nat_graph, <- idm1.
    rewrite <- ! AssocComp.
    rewrite Assoc.
    rewrite <- (HorizontalSliding1 (nat_graph m)).
    2: simpl; rewrite gout_nat_graph; reflexivity.
    simpl. rewrite gin_nat_graph, gout_nat_graph.
    rewrite <- idm1.
    rewrite ! AssocComp.
    rewrite sum_comp_distr.
    rewrite ! AssocComp.
    rewrite <- CoAssoc.
    all: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
    Simpl.
    rewrite <- (AssocComp (-< ∘ _) (-- ⊕ _)).
    etransitivity.
    apply CongComp.
    2: reflexivity.
    apply CongComp.
    2: reflexivity.
    apply CongComp.
    reflexivity.
    rewrite idm1.
    rewrite <- sum_distribute.
    replace (1 + 1) with (gout (nat_graph n ⊕ ≡1≡)).
    replace 1 with (gin (nat_graph m)).
    apply HorizontalSliding1.
    rewrite gin_nat_graph; auto.
    simpl. rewrite gout_nat_graph; auto.
    rewrite gin_nat_graph.
    rewrite <- ! AssocComp.
    rewrite (AssocComp (-< ⊕ _)).
    rewrite AssocSum. rewrite <- idm1.
    rewrite MFI.
    all: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
    rewrite idm1 at 1. rewrite IdLeft'. 2: reflexivity.
    rewrite (AssocComp _ (_ ⊕ --) >-).
    rewrite <- sum_id_comp.
    all: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
    rewrite IHn.
    replace (m + S n) with (S (m + n)) by omega.
    simpl. rewrite AssocComp. reflexivity.
Qed.

Lemma any_number_discard:
  forall m,
    nat_graph m ∘ -o == -o.
Proof.
  induction m; simpl; intros; auto.
  rewrite <- AssocComp, B4. Simpl. reflexivity.
  rewrite <- AssocComp. rewrite B2.
  rewrite <- AssocComp. rewrite MFI. rewrite IHm.
  all: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
  transitivity (-< ∘ ((-o ∘ ≡0≡) ⊕ (-- ∘ -o))).
  simpl. Simpl. reflexivity.
  rewrite <- MFI.
  all: simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; try omega.
  rewrite AssocComp. rewrite CoUnit. Simpl. apply IdLeftGen. simpl. Simpl. reflexivity.
Qed.

Lemma id_comp_id:
  -- ∘ -- == --.
Proof.
  rewrite IdLeftGen; simpl; rewrite ? idm1; Simpl; reflexivity.
Qed.

Lemma nat_copy:
  forall m,
    nat_graph m ∘ -< == -< ∘ (nat_graph m ⊕ nat_graph m).
Proof.
  induction m; simpl; intros; eauto.
  - rewrite <- AssocComp. rewrite B3.
    rewrite <- MFI.
    all: try reflexivity.
    rewrite AssocComp.
    rewrite <- (HorizontalSliding2 -o -o).
    simpl. Simpl.
    rewrite AssocComp. rewrite CoUnit.
    rewrite (IdLeftGen --). reflexivity.
    rewrite idm1. reflexivity.
  - rewrite <- AssocComp, B1.
    rewrite ! AssocComp.
    rewrite <- (AssocComp -<).
    rewrite MFI by (simpl; rewrite ? gout_nat_graph; reflexivity).
    rewrite IHm.
    rewrite <- (MFI -< (_ ⊕ nat_graph m)) by (simpl; rewrite ? gout_nat_graph, ?gin_nat_graph; reflexivity).
    rewrite AssocComp. rewrite CoAssoc.
    rewrite <- ! AssocComp.
    rewrite <- AssocSum.
    rewrite (AssocComp (-- ⊕ -<)).
    rewrite (MFI -- (nat_graph m) -<)  by (simpl; rewrite ? gout_nat_graph, ?gin_nat_graph; reflexivity).
    rewrite <- (HorizontalSliding1 (nat_graph m) -<).
    rewrite gin_nat_graph. simpl. Simpl.
    rewrite (AssocComp -< (-- ⊕ -<)).
    rewrite <- CoAssoc.
    rewrite (IdLeftGen --). 2: rewrite gin_nat_graph, idm1; reflexivity.
    rewrite <- (AssocSum -- >< --).
    rewrite (AssocComp _ _ (>- ⊕ >-)).
    rewrite (MFI (nat_graph m) --)   by (simpl; rewrite ? gout_nat_graph, ?gin_nat_graph; reflexivity).
    rewrite (AssocSum _ -- --).
    rewrite <- (AssocComp _ (_ ⊕ --) (>< ⊕ --)).
    rewrite (MFI _ >< -- --)   by (simpl; rewrite ? gout_nat_graph, ?gin_nat_graph; reflexivity).
    rewrite <- twister_twist.
    replace 1 with (gout (nat_graph m)) at 1 by apply gout_nat_graph.
    rewrite twist_simpl. rewrite gin_nat_graph. rewrite twister_twist.
    rewrite ! AssocComp.
    rewrite <- (MFI >< (-- ⊕ nat_graph m) -- --)
      by (simpl; rewrite ? gout_nat_graph, ?gin_nat_graph; reflexivity).
    rewrite ! AssocComp.
    rewrite <- (AssocComp -< (-< ⊕ --)).
    rewrite (MFI -< >< -- --)
      by (simpl; rewrite ? gout_nat_graph, ?gin_nat_graph; reflexivity).
    rewrite <- CoComm.
    rewrite (IdLeftGen --). 2: rewrite <- idm1; reflexivity.
    rewrite (IdRightGen _ --). 2: rewrite gout_nat_graph. 2: rewrite <- idm1; reflexivity.
    rewrite CoAssoc.
    rewrite <- (HorizontalSliding1 (nat_graph m)).
    simpl. rewrite ? gin_nat_graph, ? gout_nat_graph.
    rewrite <- idm1.
    rewrite idm1, ! sum_idn_comp_left.
    all: simpl; rewrite ? gin_nat_graph; try omega.
    Simpl.
    rewrite MFI by (simpl; simpl_gin_gout; omega).
    rewrite id_comp_id.
    rewrite! AssocComp.
    assert ((-< ∘ (-- ⊕ -< ∘ (-- ⊕ -<))) ==
            -< ∘ (-- ⊕ -<) ∘ (-- ⊕ (-- ⊕ -<))).
    {
      rewrite <- AssocComp. rewrite MFI.
      rewrite id_comp_id. reflexivity.
      reflexivity. reflexivity.
    }
    rewrite H.
    rewrite <- CoAssoc.
    rewrite ! AssocSum.
    rewrite <- ! AssocComp.
    apply CongComp. reflexivity.
    rewrite <- ! AssocSum.
    rewrite (AssocSum (nat_graph m) --).
    rewrite MFI.
    2: simpl; rewrite ? gout_nat_graph; reflexivity.
    2: simpl; rewrite ? gout_nat_graph; reflexivity.
    rewrite (AssocSum -- -- (nat_graph m ⊕ --)).
    rewrite (AssocSum -- --).
    rewrite AssocComp.
    rewrite MFI by (simpl; rewrite ? gout_nat_graph; reflexivity).
    rewrite MFI by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; reflexivity).
    rewrite ! (IdLeftGen (-- ⊕ --)).
    2-3:simpl; rewrite ? gin_nat_graph; simpl; Simpl; reflexivity.
    rewrite MFI by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; reflexivity).
    rewrite <- AssocComp.
    rewrite ! (IdLeftGen (-- ⊕ --)).
    2:simpl; rewrite ? gin_nat_graph; simpl; Simpl; reflexivity.
    rewrite (IdLeftGen --). reflexivity.
    rewrite idm1; reflexivity.
Qed.

Lemma bizarro_nat:
  forall n,
    nat_graph n == bizarro (nat_graph n).
Proof.
  induction n; simpl; intros. reflexivity.
  rewrite <- IHn.
  rewrite AssocComp. reflexivity.
Qed.

Lemma bizarro_eq_rev:
  forall g1 g2,
    bizarro g1 == bizarro g2 ->
    g1 == g2.
Proof.
  intros g1 g2 EQ.
  apply bizarro_eq in EQ.
  rewrite ! bizarro_involutive in EQ.
  auto.
Qed.

Corollary zero_m_zero:
  forall m,
    o- ∘ (nat_graph m) == o-.
Proof.
  intros.
  apply bizarro_eq_rev.
  simpl. rewrite <- bizarro_nat.
  apply any_number_discard.
Qed.

Corollary adding : forall m, (nat_graph m ⊕ nat_graph m) ∘ >- == >- ∘ (nat_graph m).
Proof.
  intros.
  apply bizarro_eq_rev.
  simpl.
  rewrite <- ! bizarro_nat.
  symmetry; apply nat_copy.
Qed.

Lemma nat_mul:
  forall m n,
    nat_graph m ∘ (nat_graph n) == nat_graph (m*n).
Proof.
  induction m; simpl; intros.
  rewrite <- AssocComp. rewrite zero_m_zero. reflexivity.
  rewrite <- AssocComp.
  rewrite <- adding.
  rewrite <- (AssocComp -<).
  rewrite (AssocComp (_ ⊕ --)).
  rewrite MFI by (simpl; rewrite ? gin_nat_graph, ? gout_nat_graph; omega).
  rewrite IHm.
  rewrite (IdLeftGen --). 
  2: rewrite idm1, gin_nat_graph; reflexivity.
  rewrite ! AssocComp. rewrite nat_graph_sum.
  replace ( m*n+n) with (n + m*n) by omega. reflexivity.
Qed.
