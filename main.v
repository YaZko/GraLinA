(** The type of graphs:
    - Empty graph
    - The Zero graph o- and its dual, the Discard graph -o
    - Binary addition, merging two graphs, and its dual, the Copy graph
    - A simple wire, Id, and two wire exchanging their positions, Twist.
    - Horizontal and vertical composition of graphs.
 **)
Inductive Graph: nat -> nat -> Type :=
| Empty: Graph 0 0
| Zero: Graph 0 1
| Discard: Graph 1 0
| Add: Graph 2 1
| Copy: Graph 1 2
| Twist: Graph 2 2
| Id: Graph 1 1
| Sum:  forall {n m p q}, Graph n m -> Graph p q -> Graph (n + p) (m + q)
| Comp: forall {n m p}, Graph n m -> Graph m p -> Graph n p
.

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
Fixpoint bizarro {n m} (g: Graph n m): Graph m n :=
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

Lemma bizarro_involutif: forall {n m} (g: Graph n m), bizarro (bizarro g) = g.
Proof.
  induction g; (auto || cbn; congruence).
Qed. 

(* n wires stacked one on another. Correspond to n-dimentional identities *)
Fixpoint idm n: Graph n n :=
  match n with
  | 0 => ∅
  | S n => -- ⊕ idm n
  end.
Notation "'≡' n '≡'" := (idm n) (at level 12).

Require Import Logic.Eqdep_dec.
Require Import Coq.Program.Tactics.
Require Import Arith.
Require Import Omega.


Definition transport_Graph_eq
        {a b c d: nat} (eac : a = c) (ebd: b = d) (G: Graph a b):
  Graph c d.
Proof.
  intros.
  eapply eq_rect. 2: exact ebd.
  apply (eq_rect _ (fun n => Graph n b) G). exact eac.
Defined.

(* n wires twisted over m wires *)
Program Fixpoint twist_aux n: Graph (S n) (S n) :=
  match n with
  | 0 => ≡1≡
  | S n => (twist_aux n ⊕ --) ∘ (≡n≡ ⊕ ><)
  end.
Next Obligation.
  omega.
Qed.
Next Obligation.
  omega.
Qed.

Program Fixpoint twister n m: Graph (n + m) (n + m) :=
  match n with
  | 0   => ≡m≡
  | S n => (-- ⊕ twister n m) ∘ (twist_aux m ⊕ ≡n≡)
  end.
Next Obligation.
  omega.
Qed.
Next Obligation.
  omega.
Qed.

(* Notation "'>' n '•' m '<'" := (twister n m) (at level 13, n at next level). *)

Require Import Relations.
Require Import Equivalence.

Reserved Notation "g1 == g2" (at level 50).


Program Definition transport_Graph_assoc
        {a b c d e f: nat} (G: Graph (a + b + c) (d + e + f)):
  Graph (a + (b + c)) (d + (e + f)).
Proof.
  eapply transport_Graph_eq. 3: apply G.
  all: auto with arith.
Defined.

Lemma plus_n_0:
  forall (n: nat), n + 0 = n.
Proof.
  induction n; simpl; intros.
  reflexivity.
  rewrite IHn. reflexivity.
Defined.

Program Definition transport_Graph_plus0
        {a b: nat} (G: Graph (a + 0) (b + 0)):
  Graph a b.
Proof.
  eapply transport_Graph_eq. 3: apply G.
  all: apply plus_n_0.
Defined.

Program Definition transport_Graph_plus0'
        {a b: nat} (G: Graph a b):
  Graph (a + 0) (b + 0).
Proof.
  eapply transport_Graph_eq. 3: apply G.
  all: symmetry; apply plus_n_0. 
Defined.

Inductive eqG: forall {n m: nat}, relation (Graph n m) :=
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
| IdRight: forall {n m} (G: Graph n m), (G ∘ ≡m≡) == G
| IdLeft:  forall {n m} (G: Graph n m), ≡n≡ ∘ G == G
| IdUp:    forall {n m} (G: Graph n m), ∅ ⊕ G == G
| IdDown:    forall {n m} (G: Graph n m), G ⊕ ∅ == transport_Graph_plus0' G

(** associativity of composition **)
| AssocComp: forall {n m p q: nat} (g1: Graph n m) (g2: Graph m p) (g3: Graph p q),
    g1 ∘ (g2 ∘ g3) == (g1 ∘ g2) ∘ g3
| AssocSum: forall {n m p q r s: nat} (g1: Graph n m) (g2: Graph p q) (g3: Graph r s),
    g1 ⊕ (g2 ⊕ g3) == transport_Graph_assoc ((g1 ⊕ g2) ⊕ g3)

(** Middle Four Interchange principle **)
| MFI: forall {a b c n m p}
         (A: Graph n m) (B: Graph m p)
         (C: Graph a b) (D: Graph b c),
    (A ⊕ C) ∘ (B ⊕ D) == (A ∘ B) ⊕ (C ∘ D)

(** Congruence closure with respect to both composition and sum **)
| CongSum: forall {n m p q: nat} (g1 g1': Graph n m) (g2 g2': Graph p q),
    g1 == g1' -> g2 == g2' -> g1 ⊕ g2 == g1' ⊕ g2'
| CongComp: forall {n m p: nat} (g1 g1': Graph n m) (g2 g2': Graph m p),
    g1 == g1' -> g2 == g2' -> g1 ∘ g2 == g1' ∘ g2'

(** Reflexive, symmetric, transitive closure **)
| Refl: forall {n m} (g: Graph n m), g == g
| Sym: forall {n m} (g1: Graph n m) g2, g1 == g2 -> g2 == g1
| Trans: forall {n m} (g1 g2 g3: Graph n m), g1 == g2 -> g2 == g3 -> g1 == g3
where "g1 == g2" := (eqG g1 g2).

Require Import Classes.RelationClasses.

Instance PEq_equiv (n m: nat): @Equivalence (Graph n m) (@eqG n m).
Proof.
  split.
  intros ?; apply Refl.
  intros ? ?; apply Sym.
  intros ? ? ?; apply Trans.
Qed.
   
Lemma slide_left: forall {n m p q} (g1: Graph n m) (g2: Graph p q),
    g1 ⊕ g2 == (g1 ∘ ≡m≡) ⊕ (≡p≡ ∘ g2).
Proof.
  intros.
  apply CongSum.
  symmetry; constructor.
  symmetry; constructor.
Qed.
   
Lemma slide_right: forall {n m p q} (g1: Graph n m) (g2: Graph p q),
    g1 ⊕ g2 == (≡n≡ ∘ g1) ⊕ (g2 ∘ ≡q≡).
Proof.
  intros.
  apply CongSum.
  symmetry; constructor.
  symmetry; constructor.
Qed.

Require Import Setoid.

Add Parametric Morphism n m p q: Sum with
signature (@eqG n m ==> @eqG p q ==> @eqG (n + p) (m + q)) as proper_sum. 
intros g1 g1' eq1 g2 g2' eq2.
constructor; auto.
Qed.

Add Parametric Morphism n m p: Comp with
signature (@eqG n m ==> @eqG m p ==> @eqG n p) as proper_comp. 
intros g1 g1' eq1 g2 g2' eq2.
constructor; auto.
Qed.

Lemma cong_transport:
  forall n m p q (eq1: n = p) (eq2: m = q) (g1 g2: Graph n m),
    g1 == g2 ->
    transport_Graph_eq eq1 eq2 g1 == transport_Graph_eq eq1 eq2 g2.
Proof.
  unfold transport_Graph_eq.
  intros. subst.
  rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); auto.
Qed.

Lemma cong_transport_l:
  forall n m p (eq1: n = p) (g1 g2: Graph n m),
    g1 == g2 ->
    eq_rect _ (fun k => Graph k m) g1 _ eq1 == eq_rect _ (fun k => Graph k m) g2 _ eq1.
Proof.
  intros. subst.
  rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); auto.
Qed.

Lemma cong_transport_r:
  forall n m q (eq2: m = q) (g1 g2: Graph n m),
    g1 == g2 ->
    eq_rect _ _ g1 _ eq2 == eq_rect _ _ g2 _ eq2.
Proof.
  intros. subst.
  rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); auto.
Qed.

Lemma transport_cancel:
  forall n m p q (eq1: n = p) (eq2: m = q) (g1: Graph p q),
    transport_Graph_eq eq1 eq2 (transport_Graph_eq (eq_sym eq1) (eq_sym eq2) g1) == g1.
Proof.
  unfold transport_Graph_eq.
  intros. subst.
  rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); reflexivity.
Qed.

Ltac clean :=
  unfold transport_Graph_assoc, transport_Graph_plus0,transport_Graph_plus0', transport_Graph_eq;
  repeat (rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec)).

Ltac rrewrite H :=
  rewrite H; clean.

Lemma eq_rect_cancel:
  forall n p (eq1: n = p) (T: nat -> Type) (x: T p),
    eq_rect n T (eq_rect _ _ x n (eq_sym eq1)) _ eq1 = x.
Proof.
  intros. subst.
  clean. reflexivity.
Qed.

Lemma IdDown': forall {n m} (G: Graph n m),
    transport_Graph_plus0 (G ⊕ ∅) == G.
Proof.
  intros n m G.
  unfold transport_Graph_plus0.
  etransitivity.
  apply cong_transport.
  apply IdDown.
  unfold transport_Graph_plus0'.
  apply transport_cancel.
Qed.

Lemma idm1: -- == ≡1≡.
Proof.
  unfold idm.
  rewrite IdDown; clean.
  reflexivity.
Qed.

Lemma IdRight': forall {n} (g: Graph n 1),
    g ∘ -- == g.
Proof.
  intros.
  rewrite idm1, IdRight; reflexivity.
Qed.

Lemma twister_twist: twister 1 1 == ><.
Proof.
  cbn; clean.
  rewrite IdUp.
  rewrite IdDown; clean. 
  rewrite IdDown; clean. 
  rewrite AssocComp.
  rewrite (@MFI 1 1 1 1 1 1).
  rewrite IdRight'.
  assert ((-- ⊕ --) == ≡2≡) by (cbn; rewrite IdDown; clean; reflexivity).
  rewrite H, IdLeft.
  reflexivity.
Qed.

Lemma slide_twist: forall n m (g1 g2: Graph n m),
    n = 1 -> m = 1 ->
    (g1 ⊕ g2) ∘ (twister m m) == (twister n n) ∘ (g1 ⊕  g2).
Proof.
  intros n m g1.
  induction g1; intros; subst; try congruence.
  - clear H H0.
    rewrite twister_twist.
Abort.

Lemma sum_distribute:
  forall n m,
    ≡ n + m ≡ == ≡ n ≡ ⊕ ≡ m ≡.
Proof.
  induction n; simpl; intros. symmetry; apply IdUp.
  rewrite IHn.
  rewrite AssocSum.
  unfold transport_Graph_assoc, transport_Graph_eq.
  clean. reflexivity.
Qed.

(* Theorem bizarrofree: forall {n m: nat} (g1 g2: Graph n m), *)
(*     g1 == g2 -> (bizarro g1) == (bizarro g2). *)
(* Proof. *)
(*   induction 1; cbn; try now (symmetry; constructor); try now constructor. *)
(*   etransitivity; [apply B1 |   symmetry; eapply AssocComp; eauto]. *)
(*   etransitivity; eauto. *)
(* Qed. *)


Lemma slide_twist: forall {n m p q} (g1: Graph n m) (g2: Graph p q),
    (g1 ⊕ g2) ∘ (twister m q) == (twister n p) ∘ (g1 ⊕  g2).
Proof.

  induction n; cbn; intros m p q g1 g2.
  -  rewrite IdLeft.
    destruct m; cbn.
    + apply IdRight.
    + etransitivity. 2: apply IdRight.
      apply CongComp. reflexivity.
      cbn.
      rewrite sum_distribute.
      rewrite AssocSum.
      clean.

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
  

