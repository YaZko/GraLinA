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

Fixpoint idm n: Graph n n :=
  match n with
  | 0 => ∅
  | S n => -- ⊕ idm n
  end.

Notation "'≡' n '≡'" := (idm n) (at level 12).

Require Import Relations.
Require Import Equivalence.

Reserved Notation "g1 == g2" (at level 50).

Require Import Arith.

Program Definition transport_Graph {a b c d e f: nat} (G: Graph (a + b + c) (d + e + f)): Graph (a + (b + c)) (d + (e + f)).
Proof.
  apply eq_rect with (x := d + e + f); [| auto with arith].
  apply (eq_rect _ (fun n => Graph n (d + e + f)) G); auto with arith.  
Qed.

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

(** associativity of composition **)
| AssocComp: forall {n m p q: nat} (g1: Graph n m) (g2: Graph m p) (g3: Graph p q),
    g1 ∘ (g2 ∘ g3) == (g1 ∘ g2) ∘ g3
| AssocSum: forall {n m p q r s: nat} (g1: Graph n m) (g2: Graph p q) (g3: Graph r s),
    g1 ⊕ (g2 ⊕ g3) == transport_Graph ((g1 ⊕ g2) ⊕ g3)

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


Lemma tropcool: (-- ⊕ o-) ∘ >- == --.
Proof.
  etransitivity.
  eapply CongComp.
  reflexivity.
  apply Sym, Comm.
  

Theorem bizarrofree: forall {n m: nat} (g1 g2: Graph n m),
    g1 == g2 -> (bizarro g1) == (bizarro g2).
Proof.
  induction 1; cbn; try now (symmetry; constructor); try now constructor.
  etransitivity; [apply B1 |   symmetry; eapply AssocComp; eauto].
  etransitivity; eauto.
Qed.

