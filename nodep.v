Require Import Logic.Eqdep_dec.
Require Import Coq.Program.Tactics.
Require Import Arith.
Require Import Omega.

(** The type of graphs:
    - Empty graph
    - The Zero graph o- and its dual, the Discard graph -o
    - Binary addition, merging two graphs, and its dual, the Copy graph
    - A simple wire, Id, and two wire exchanging their positions, Twist.
    - Horizontal and vertical composition of graphs.
 **)
Inductive Graph: Type :=
| Empty: Graph
| Zero: Graph
| Discard: Graph
| Add: Graph
| Copy: Graph
| Twist: Graph
| Id: Graph
| Sum:  Graph -> Graph -> Graph
| Comp: Graph -> Graph -> Graph
.

Fixpoint gin (g: Graph) : nat :=
  match g with
    Empty
  | Zero => 0
  | Discard
  | Id
  | Copy => 1
  | Add
  | Twist => 2
  | Sum g1 g2 => gin g1 + gin g2
  | Comp g1 g2 => gin g1
  end.

Fixpoint gout (g: Graph) : nat :=
  match g with
    Empty
  | Discard => 0
  | Zero
  | Id
  | Add => 1
  | Copy
  | Twist => 2
  | Sum g1 g2 => gout g1 + gout g2
  | Comp g1 g2 => gout g2
  end.

Fixpoint wf (g: Graph) : Prop :=
  match g with
    Comp g1 g2 => gout g1 = gin g2 /\ wf g1 /\ wf g2
  | Sum g1 g2 => wf g1 /\ wf g2
  | _ => True
  end.

Notation "∅" := Empty.
Notation "o-" := Zero.
Notation "-o" := Discard.
Notation ">-" := Add.
Notation "-<" := Copy.
Notation "><" := Twist.
Notation "--" := Id.
Infix "∘" := Comp (at level 10).
Infix "⊕" := Sum (at level 11).

(* The dual of  a graph *)
Require Import Relations.
Require Import Equivalence.
Require Import Classes.RelationClasses.
Require Import Setoid.

Fixpoint bizarro (g: Graph): Graph :=
  match g with
  | ∅ => ∅
  | o- => -o
  | -o => o-
  | >- => -<
  | -< => >-
  | >< => ><
  | -- => -- 
  | Sum g1 g2 => Sum (bizarro g1) (bizarro g2)
  | Comp g1 g2 => Comp (bizarro g2) (bizarro g1)
  end.

Lemma bizarro_involutive: forall (g: Graph), bizarro (bizarro g) = g.
Proof.
  induction g; (auto || cbn; try congruence).
Qed.

(* n wires stacked one on another. Correspond to n-dimentional identities *)
Fixpoint idm n: Graph :=
  match n with
  | 0 => ∅
  | S n => -- ⊕ idm n
  end.
Notation "'≡' n '≡'" := (idm n) (at level 12).

(* n wires twisted over m wires *)
Fixpoint twist_aux n: Graph :=
  match n with
  | 0 => ≡1≡
  | S n => (twist_aux n ⊕ --) ∘ (≡n≡ ⊕ ><)
  end.

Fixpoint twister n m: Graph :=
  match n with
  | 0   => ≡m≡
  | S n => (-- ⊕ twister n m) ∘ (twist_aux m ⊕ ≡n≡)
  end.

Reserved Notation "g1 == g2" (at level 50).

Inductive eqG: Graph -> Graph -> Prop :=
(** Axiomatisation of addition **)
| Comm: >< ∘ >- == >-
| Assoc: (-- ⊕ >-) ∘ >- == (>- ⊕ --) ∘ >-
| Unit: -- == (o- ⊕ --) ∘ >-

(** Axiomatisation of copy (bizarro of the previous three) **)
| CoComm: -< == -< ∘ ><
| CoAssoc: -< ∘ (-< ⊕ --) == -< ∘ (--  ⊕ -<)
| CoUnit: -< ∘ (-o ⊕ --) == --

(** Axiomatisation of addition interacting with copy **)
| B1: >- ∘ -< == (-< ⊕ -<) ∘ (-- ⊕ >< ⊕ --) ∘ (>- ⊕ >-)
| B2: >- ∘ -o == -o ⊕ -o
| B3: o- ∘ -< == o- ⊕ o-
| B4: o- ∘ -o == ∅

(** Identity idempotency **)
| IdRight: forall (G: Graph), (G ∘ ≡gout G≡) == G
| IdLeft:  forall (G: Graph), ≡gin G≡ ∘ G == G
| IdUp:    forall (G: Graph), ∅ ⊕ G == G
| IdDown:  forall (G: Graph), G ⊕ ∅ == G

(** associativity of composition **)
| AssocComp: forall (g1: Graph) (g2: Graph) (g3: Graph),
    (* gout g1 = gin g2 -> *)
    (* gout g2 = gin g3 -> *)
    g1 ∘ (g2 ∘ g3) == (g1 ∘ g2) ∘ g3
| AssocSum: forall (g1: Graph) (g2: Graph) (g3: Graph),
    g1 ⊕ (g2 ⊕ g3) == (g1 ⊕ g2) ⊕ g3

| NoTangle: >< ∘ >< == -- ⊕ --

| HorizontalSliding1:
    forall A B,
      (≡gin A≡ ⊕ B) ∘ (A ⊕ ≡gout B≡) == (A ⊕ B)

| HorizontalSliding2:
    forall A B,
      (A ⊕ ≡gin B≡) ∘ (≡gout A≡ ⊕ B) == (A ⊕ B)

| TwistySliding:
    forall A B,
      (A ⊕ B) ∘ (twister (gout A) (gout B)) ==
      (≡gin A≡ ⊕ B) ∘ (twister (gin A) (gout B)) ∘ (≡gout B≡ ⊕ A)

(** Middle Four Interchange principle **)
| MFI: forall (A: Graph) (B: Graph)
         (C: Graph) (D: Graph),
    gout A = gin B ->
    gout C = gin D ->
    (A ⊕ C) ∘ (B ⊕ D) == (A ∘ B) ⊕ (C ∘ D)

(** Congruence closure with respect to both composition and sum **)
| CongSum: forall (g1 g1': Graph) (g2 g2': Graph),
    g1 == g1' -> g2 == g2' -> g1 ⊕ g2 == g1' ⊕ g2'
| CongComp: forall (g1 g1': Graph) (g2 g2': Graph),
    (* gout g1 = gin g2 -> *)
    g1 == g1' -> g2 == g2' -> g1 ∘ g2 == g1' ∘ g2'

(** Reflexive, symmetric, transitive closure **)
| Refl: forall (g: Graph), g == g
| Sym: forall (g1: Graph) (g2: Graph), g1 == g2 -> g2 == g1
| Trans: forall (g1 g2 g3: Graph), g1 == g2 -> g2 == g3 -> g1 == g3

where "g1 == g2" := (eqG g1 g2).

Lemma gin_idm:
  forall n,
    gin (≡n≡) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma gout_idm:
  forall n,
    gout (≡n≡) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma wf_idm:
  forall n,
    wf (≡n≡).
Proof.
  induction n; simpl; auto.
Qed.


Lemma gin_twist_aux:
  forall n, gin (twist_aux n) = S n.
Proof.
  induction n; cbn; auto.
  omega. 
Qed.

Ltac Simpl := repeat rewrite ? IdUp, ? IdRight, ? IdLeft, ? IdDown.

Lemma gin_twister:
  forall n m, gin (twister n m) = n + m.
Proof.
  induction n; simpl; intros.
  rewrite gin_idm. auto.
  rewrite IHn; auto.
Qed.

Lemma gout_twist_aux:
  forall n, gout (twist_aux n) = S n.
Proof.
  induction n; simpl; intros.
  auto. 
  rewrite gout_idm. omega.
Qed.

Lemma gout_twister:
  forall n m, gout (twister n m) = n + m.
Proof.
  induction n; simpl; intros.
  rewrite gout_idm. auto.
  rewrite gout_twist_aux. rewrite gout_idm. omega.
Qed.

Lemma wf_twist_aux:
  forall n,
    wf (twist_aux n).
Proof.
  induction n; simpl; intros; eauto.
  intuition.
  rewrite gout_twist_aux. rewrite gin_idm. omega.
  apply wf_idm.
Qed.

Lemma wf_twister:
  forall n m,
    wf (twister n m).
Proof.
  induction n; simpl; intros; eauto.
  apply wf_idm.
  intuition.
  rewrite gout_twister. rewrite gin_twist_aux. rewrite gin_idm. omega.
  apply wf_twist_aux.
  apply wf_idm.
Qed.

Ltac simpl_gin_gout :=
  rewrite ? gin_idm, ? gin_twister, ? gin_twist_aux, ? gout_idm, ? gout_twister, ? gout_twist_aux.

Ltac solve_wf :=
  first [
      apply wf_idm
      || apply wf_twister
      || apply wf_twist_aux ].

Ltac check_consistency :=
  match goal with
    |- ?g1 == ?g2 =>
    assert (wf g1 /\ wf g2 /\ gout g1 = gout g2 /\ gin g1 = gin g2);
    [
      cbn; intuition; simpl_gin_gout; try omega; try solve_wf
      |
    ]
  end.


Lemma eqG_same_arity:
  forall (g1: Graph) (g2: Graph),
    g1 == g2 -> (wf g1 <-> wf g2) /\ gout g1 = gout g2 /\ gin g1 = gin g2.
Proof.
  induction 1; simpl; try tauto; simpl_gin_gout; intuition;
    try solve_wf.
Qed.

Instance PEq_equiv: Equivalence eqG.
Proof.
  split.
  intros ?; apply Refl.
  intros ? ?; apply Sym.
  intros ? ? ?; apply Trans.
Qed.

Add Parametric Morphism : Sum with
    signature (eqG ==> eqG ==> eqG) as proper_sum. 
Proof.
  intros g1 g1' eq1 g2 g2' eq2.
  constructor; auto.
Qed.

Add Parametric Morphism: Comp with
    signature (eqG ==> eqG ==> eqG) as proper_comp. 
Proof.
  intros g1 g1' eq1 g2 g2' eq2.
  constructor; auto.
Qed.

Lemma slide_left: forall (g1: Graph) (g2: Graph),
    g1 ⊕ g2 == (g1 ∘ ≡gout g1≡) ⊕ (≡gin g2≡ ∘ g2).
Proof.
  intros.
  apply CongSum.
  apply Sym; constructor; auto.
  apply Sym; constructor; auto.
Qed.
   
Lemma slide_right: forall (g1: Graph) (g2: Graph),
    g1 ⊕ g2 == (≡gin g1≡ ∘ g1) ⊕ (g2 ∘ ≡gout g2≡).
Proof.
  intros.
  apply CongSum.
  apply Sym; constructor; auto.
  apply Sym; constructor; auto.
Qed.

Lemma idm1: -- == ≡1≡.
Proof.
  unfold idm.
  apply Sym, IdDown.
Qed.

Lemma IdRight': forall m (g: Graph),
    gout g = m ->
    (g ∘ ≡m≡) == g.
Proof.
  intros.
  rewrite <- (IdRight g) at 2. subst; reflexivity. 
Qed.

Lemma IdLeft': forall m (g: Graph),
    gin g = m ->
    ≡m≡ ∘ g == g.
Proof.
  intros.
  rewrite <- (IdLeft g) at 2. subst; reflexivity.
Qed.

Lemma twister_twist: twister 1 1 == ><.
Proof.
  unfold twister.
  unfold twist_aux.
  rewrite IdUp.
  rewrite ! IdDown.
  rewrite AssocComp by reflexivity. 
  rewrite MFI by reflexivity.
  rewrite IdRight' by reflexivity.
  rewrite IdLeft' by reflexivity.
  assert ((-- ⊕ --) == ≡2≡) by (cbn; rewrite IdDown; reflexivity).
  rewrite H.
  apply IdLeft'. reflexivity.
Qed.

Lemma sum_distribute:
  forall n m,
    ≡ n + m ≡ == ≡ n ≡ ⊕ ≡ m ≡.
Proof.
  induction n; simpl; intros. symmetry; apply IdUp.
  rewrite IHn.
  rewrite AssocSum.
  reflexivity.
Qed.

(* Theorem bizarrofree: forall (g1 g2: Graph), *)
(*     g1 == g2 -> (bizarro g1) == (bizarro g2). *)
(* Proof. *)
(*   induction 1; cbn; try now (symmetry; constructor); try now constructor. *)
(*   etransitivity; [apply B1 |   symmetry; eapply AssocComp; eauto]. *)
(*   etransitivity; eauto. *)
(* Qed. *)


Lemma sum_id_comp:
  forall a b,
    gout a = gin b ->
    (a ∘ b) ⊕ -- == (a ⊕ --) ∘ (b ⊕ --).
Proof.
  intros.
  rewrite MFI; auto.
  apply CongSum. reflexivity. rewrite idm1. symmetry; apply IdLeft'. reflexivity.
Qed.

Lemma sum_idn_comp:
  forall a b n,
    gout a = gin b ->
    ((a ∘ b) ⊕ ≡n≡) == (a ⊕ ≡n≡) ∘ (b ⊕ ≡n≡).
Proof.
  intros.
  rewrite MFI; auto.
  apply CongSum. reflexivity. symmetry; apply IdLeft'. simpl_gin_gout. reflexivity.
  simpl_gin_gout. auto.
Qed.

Lemma sum_idn_comp_left:
  forall a b n,
    gout a = gin b ->
    (≡n≡ ⊕ (a ∘ b)) == (≡n≡ ⊕ a) ∘ (≡n≡ ⊕ b).
Proof.
  intros.
  rewrite MFI; auto.
  apply CongSum. 2: reflexivity. symmetry; apply IdLeft'. simpl_gin_gout. reflexivity.
  simpl_gin_gout. auto.
Qed.

Lemma idsum_reorder m:
  -- ⊕ (≡m≡) == ≡m≡ ⊕ --.
Proof.
  assert (e: 1 + m = m + 1) by omega.
  generalize (Refl (≡1+m≡)). rewrite e at 2. simpl. clear e;intro e.
  rewrite sum_distribute in e.
  rewrite e. rewrite idm1; reflexivity.
Qed.

Lemma twist_aux_subgool:
  forall n,
    (>< ⊕ (≡ n ≡)) ∘ (-- ⊕ twist_aux n) == (twist_aux n ⊕ --) ∘ ((≡ n ≡) ⊕ ><).
Proof.
  induction n; simpl; intros.
  - Simpl.
    etransitivity. symmetry. apply IdLeft.
    simpl. Simpl. reflexivity.
  - rewrite idsum_reorder.
    rewrite ! AssocSum.
    transitivity (  ((>< ⊕ (≡ n ≡)) ⊕ --) ∘ (-- ⊕ (twist_aux n ⊕ --)) ∘ (-- ⊕ ((≡ n ≡) ⊕ ><))).
    + rewrite <- AssocComp.
      apply CongComp.
      reflexivity.
      generalize (sum_idn_comp_left (twist_aux n ⊕ --) ((≡n≡) ⊕ ><) 1). rewrite <- idm1.
      intro H; apply H. simpl; simpl_gin_gout. omega.
    + rewrite <- IHn.
      clear IHn.
      rewrite sum_id_comp.
      apply CongComp.
      all: simpl; simpl_gin_gout; try omega.
      rewrite <- ! AssocSum. reflexivity.
      rewrite ! AssocSum. rewrite idsum_reorder. reflexivity.
Qed.

Lemma twist_aux_sum:
  forall n m,
    twist_aux (m + n) == (twist_aux m ⊕ ≡n≡) ∘ (≡m≡ ⊕ twist_aux n).
Proof.
  induction n; simpl; intros.
  - Simpl. rewrite <- plus_n_O.
    symmetry. etransitivity. 2: apply IdRight.
    apply CongComp. reflexivity.
    simpl_gin_gout. replace (S m) with (m + 1) by omega.
    rewrite sum_distribute. rewrite idm1. reflexivity.
  - replace (m + S n) with (S m + n) by omega.
    rewrite IHn.
    simpl.
    rewrite sum_idn_comp by (simpl; simpl_gin_gout; try omega).
    rewrite <- ! AssocSum.
    rewrite <- ! AssocComp.
    apply CongComp. reflexivity.
    rewrite (AssocSum --).
    rewrite idsum_reorder.
    rewrite <- AssocSum.
    rewrite <- sum_idn_comp_left. 2: simpl; simpl_gin_gout; omega.
    apply CongSum.
    reflexivity.
    apply twist_aux_subgool.
Qed.

Fact decomp_twist:
  forall k m n,
    twister k (m+n) == (twister k m ⊕ ≡n≡) ∘ (≡m≡ ⊕ twister k n).
Proof.
  induction k; cbn; intros.
  - rewrite <- sum_distribute.
    rewrite IdRight'. reflexivity. simpl_gin_gout. auto.
  - rewrite IHk.
    rewrite <- (IdRight --) at 1. simpl. rewrite IdDown.
    rewrite <- (MFI -- --) by (simpl; simpl_gin_gout; omega).
    
Qed.


Goal (twister 2 3) == (-- ⊕ >< ⊕ ≡2≡) ∘ (>< ⊕ >< ⊕ --) ∘ ( -- ⊕ >< ⊕ >< ) ∘ (≡2≡ ⊕ >< ⊕ --).
Proof.
  cbn. Simpl.
Qed.


Lemma slide_twist':
  forall g1 g2,
    (g1 ⊕ g2) ∘ (twister (gout g1) (gout g2)) == (≡ gin g1 ≡ ⊕ g2) ∘ (twister (gin g1) (gout g2)) ∘ (≡ gout g2 ≡ ⊕ g1).
Proof.
  intros.
  rewrite slide_twist.
Qed.

Lemma slide_test: (-- ⊕ o-) ∘ >< == (o- ⊕ --).
Proof.
  etransitivity.
  2: etransitivity.
  2: apply (slide_twist -- o-).
  - rewrite twister_twist. reflexivity.
  - rewrite twister_twist.
    rewrite <- ! idm1.

Qed.


Lemma tropcool: (-- ⊕ o-) ∘ >- == --.
Proof.
  rewrite <- Comm.
  etransitivity.
  eapply CongComp.
  reflexivity.
  apply Sym, Comm.




  

Qed.

Axiom twist_twist:
  >< ∘ >< == -- ⊕ --.

Lemma twist_simpl:
  forall g1 g2,
    gout g1 = 1 ->
    gout g2 = 1 ->
    (g1 ⊕ g2) ∘ >< == g2 ⊕ g1.
Proof.
  induction g1; cbn; intros; Simpl; try congruence.
  - revert H0. induction g2; cbn in *; intros; try congruence.
    + rewrite <- B3. rewrite <- AssocComp, <- CoComm by reflexivity. reflexivity.
    +
      


      admit.
    + admit.
    + destruct (gout g2_1).
      
      rewrite Unit at 1.
      etransitivity.
      2: etransitivity.
      2: apply MFI.
      apply CongComp. reflexivity.
      symmetry; apply IdDown.

      
Qed.

Lemma twist_spec:
  forall g2 g1,
    gout g1 = 1 ->
    (g1 ⊕ g2) ∘ (twist_aux (gout g2)) == g2 ⊕ g1.
Proof.
  induction g2; cbn; intros; Simpl.
  - rewrite idm1. rewrite IdRight'; auto. reflexivity.
  - rewrite AssocComp by (simpl; omega).
    rewrite MFI by (simpl; omega).
    rewrite idm1. rewrite IdRight.
    rewrite IdRight.
Qed.


Lemma slide_twist: forall (g1: Graph) (g2: Graph),
    (g1 ⊕ g2) ∘ (twister (gout g1) (gout g2)) == (twister (gin g1) (gin g2)) ∘ (g2 ⊕ g1).
Proof.
  induction g1; cbn; intros g2.
  - rewrite IdUp. rewrite IdRight. rewrite IdDown. rewrite IdLeft. reflexivity.
  - rewrite IdDown.
    rewrite (IdLeft'). 2: simpl; omega.
    assert ( -- ⊕ (≡ gout g2≡) == ≡ gin (twist_aux (gout g2)) ≡).
    rewrite gin_twist_aux. simpl. reflexivity.
    rewrite H. rewrite IdLeft.
    
    induction n; cbn; intros m p q g1 g2.
  - intros; subst.
    rewrite IdLeft'. 2: simpl; rewrite H; omega.
    
    etransitivity. 2: apply IdRight.
    apply CongComp. reflexivity.
    simpl.
    destruct m; cbn.
    + apply IdRight.
    + etransitivity. 2: apply IdRight.
      apply CongComp. reflexivity.
      cbn.
      apply EqRect2'.
      rewrite EqRect1.
      eapply Trans.
      refine (@EqRect2' _ _ _ _ _). (S m+q) (S (q+m)) _ _ (twister_obligation_2 q m)).
      change (fun H => Graph (S (m+q))) with (Graph (S (m+q))). rewrite EqRect2.
      generalize (twister_obligation_1 q m).
      generalize (twister_obligation_2 q m).
      generalize (q + m).
      cbn.
      intros.
      rewrite bloup.


      rewrite sum_distribute.
      rewrite AssocSum.
      clean.
      apply bloup. cbn.
      clean. 
      rewrite cong_transport_r.
  -
    
    rewrite IHn.
    generalize (twister_obligation_1 q m).
    generalize (twister_obligation_2 q m).
    generalize (Nat.add_comm m q).
    intro C.
    generalize (f_equal S C). intro D.
    cbn in *.
    intros. rewrite cong_transport_r.
    
    generalize (Nat.add_comm m q).
    intro C.
    generalize (f_equal S C). intro D.
    rewrite Nat.add_comm.
    rewrite <- eq_rect_eq_dec.


Qed.

(* Lemma tropcool: (-- ⊕ o-) ∘ >- == --. *)
(* Proof. *)
(*   etransitivity. *)
(*   eapply CongComp. *)
(*   reflexivity. *)
(*   apply Sym, Comm. *)
  

