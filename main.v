(*
* L'algèbre sous-jacente:

 - ≡n≡ est élément neutre de ∘ pour tout n
 - ∅ élément neutre de ⊕
 - ∘ est associative
 - ⊕ est associative
 - Le MFI  

* Les règles structurelles des diagrammes

 (Wires don't tangle)
 - >< ∘ >< == -- ⊕ --
 (Horizontal sliding, pour toutes les tailles possibles de A et B)
 - (≡ ⊕ B) ∘ (A ⊕ ≡) == A ⊕ B == (A ⊕ ≡) ∘ (≡ ⊕ B) 
 (Twisty sliding, pour toutes les tailles possibles de A et B, >< étant un twister adapté)
 - (A ⊕ B) >< = (≡ ⊕ B) >< (A ⊕ ≡)
 (Les diagrammes sont compositionnels)
 - Obtenue par nos deux règles de congruence  

* Les générateurs et leur axiomatisation

 (Axiomatisation de l'addition )
 - Comm: >< ∘ >- ==  >-
 - Assoc: (-- ⊕ >-) ∘ >- == (>- ⊕ --) ∘ >-
 - Unit: -- == (o- ⊕ --) ∘ >-

 (Axiomatisation de copy (bizarro des précédents))
 - CoComm: -< == -< ∘ ><
 - CoAssoc: -< ∘ (-< ⊕ --) == -< ∘ (--  ⊕ -<)
 - CoUnit: -< ∘ (-o ⊕ --) == --

 (Axiomatisation de l'interaction des deux mondes)
 - B1: >- ∘ -< == (-< ⊕ -<) ∘ (-- ⊕ >< ⊕ --) ∘ (>- ⊕ >-)
 - B2: >- ∘ -o == -o ⊕ -o
 - B3: o- ∘ -< == o- ⊕ o-
 - B4: o- ∘ -o == ∅

*)

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
Require Import Nat Arith.
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

Inductive eqG: forall {n m p q: nat}, Graph n m -> Graph p q -> Prop :=
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
| IdDown:  forall {n m} (G: Graph n m), G ⊕ ∅ == G

(** associativity of composition **)
| AssocComp: forall {n m p q: nat} (g1: Graph n m) (g2: Graph m p) (g3: Graph p q),
    g1 ∘ (g2 ∘ g3) == (g1 ∘ g2) ∘ g3
| AssocSum: forall {n m p q r s: nat} (g1: Graph n m) (g2: Graph p q) (g3: Graph r s),
    g1 ⊕ (g2 ⊕ g3) == (g1 ⊕ g2) ⊕ g3

(** Wires don't tangle **)
| NoTangle: >< ∘ >< == -- ⊕ --

(** Middle Four Interchange principle **)
| MFI: forall {a b c n m p}
         (A: Graph n m) (B: Graph m p)
         (C: Graph a b) (D: Graph b c),
    (A ⊕ C) ∘ (B ⊕ D) == (A ∘ B) ⊕ (C ∘ D)

(** Congruence closure with respect to both composition and sum **)
| CongSum: forall {n1 m1 n1' m1' n2 m2 n2' m2': nat}
             (g1: Graph n1 m1) (g1': Graph n1' m1')
             (g2: Graph n2 m2) (g2': Graph n2' m2'),
    g1 == g1' -> g2 == g2' -> g1 ⊕ g2 == g1' ⊕ g2'
| CongComp: forall {n m p n' m' p': nat}
              (g1: Graph n m) (g1': Graph n' m')
              (g2: Graph m p) (g2': Graph m' p'),
    g1 == g1' -> g2 == g2' -> g1 ∘ g2 == g1' ∘ g2'

(** Reflexive, symmetric, transitive closure **)
| Refl: forall {n m} (g: Graph n m), g == g
| Sym: forall {n m p q} (g1: Graph n m) (g2: Graph p q), g1 == g2 -> g2 == g1
| Trans: forall {n1 m1 n2 m2 n3 m3}
           (g1: Graph n1 m1) (g2: Graph n2 m2) (g3: Graph n3 m3),
    g1 == g2 -> g2 == g3 -> g1 == g3

| Transport: forall {n m p q} (g: Graph n m) (eq1: n = p) (eq2: m = q),
    g == eq_rect _ (Graph p) (eq_rect _ (fun n => Graph n m) g _ eq1) _ eq2
where "g1 == g2" := (eqG g1 g2).

Require Import Classes.RelationClasses.

Instance PEq_equiv (n m: nat): @Equivalence (Graph n m) (@eqG n m n m).
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
signature (@eqG n m n m ==> @eqG p q p q ==> @eqG (n + p) (m + q) (n + p) (m + q)) as proper_sum. 
intros g1 g1' eq1 g2 g2' eq2.
constructor; auto.
Qed.

(* Add Parametric Morphism n m n' m' p q p' q': Sum with *)
(*     signature (@eqG n m n' m' ==> *)
(*                @eqG p q p' q' ==> *)
(*                @eqG (n + p) (m + q) (n' + p') (m' + q')) as proper_sum. *)
(* intros g1 g1' eq1 g2 g2' eq2. *)
(* constructor; auto. *)
(* Qed. *)

Add Parametric Morphism n m p: Comp with
signature (@eqG n m n m ==> @eqG m p m p ==> @eqG n p n p) as proper_comp. 
intros g1 g1' eq1 g2 g2' eq2.
constructor; auto.
Qed.

Lemma cong_transport:
  forall n m p q (eq1 eq1': n = p) (eq2 eq2': m = q) (g1 g2: Graph n m),
    g1 == g2 ->
    transport_Graph_eq eq1 eq2 g1 == transport_Graph_eq eq1' eq2' g2.
Proof.
  unfold transport_Graph_eq.
  intros. subst.
  rewrite <-! eq_rect_eq_dec by (apply Nat.eq_dec); auto.
Qed.

Lemma cong_transport_l:
  forall n m p (eq1 eq2: n = p) (g1 g2: Graph n m),
    g1 == g2 ->
    eq_rect _ (fun k => Graph k m) g1 _ eq1 == eq_rect _ (fun k => Graph k m) g2 _ eq2.
Proof.
  intros. subst.
  do 2 rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); auto.
Qed.

Lemma cong_transport_r:
  forall n m q (eq1 eq2: m = q) (g1 g2: Graph n m),
    g1 == g2 ->
    eq_rect _ _ g1 _ eq1 == eq_rect _ _ g2 _ eq2.
Proof.
  intros. subst.
  do 2 rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); auto.
Qed.

Lemma transport_cancel:
  forall n m p q (eq1: n = p) (eq2: m = q) (g1: Graph p q),
    transport_Graph_eq eq1 eq2 (transport_Graph_eq (eq_sym eq1) (eq_sym eq2) g1) == g1.
Proof.
  unfold transport_Graph_eq.
  intros. subst.
  rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec); reflexivity.
Qed.

Ltac clean_aux :=
  unfold transport_Graph_assoc, transport_Graph_plus0,transport_Graph_plus0', transport_Graph_eq;
  repeat (rewrite <- eq_rect_eq_dec by (apply Nat.eq_dec)).

Ltac sym := apply Sym.
Ltac trans H := apply Trans with H.
Ltac etrans := eapply Trans.
Ltac refl := eapply Refl.

(** Currently clean eq_rect introduced by twister, and then remove emptyset from the left side member **)
Ltac clean :=
  clean_aux;
  try rewrite IdUp;
  match goal with
  | |- ?G1 ∘ ?G2 == _ =>
    refine (Trans _ (_ ∘ _) _ (CongComp _ _ _ _ _ _) _);
    [clean | clean |]
  | |- ?G1 ⊕ ?G2 == _ =>
    match G2 with
    | ∅ => refine (IdDown G1)
    | _ =>
      refine (Trans _ (_ ⊕ _) _ (CongSum G1 _ G2 _ _ _) _);
      [clean | clean |]
    end
  | _ => idtac
  end;
  try refl.

Ltac rew_assocsum :=
match goal with
| |- (?G1 ⊕ ?G2) ⊕ ?G3 == _ =>
  refine (Trans _ (G1 ⊕ (G2 ⊕ G3)) _ _ _);
    [sym; refine (AssocSum _ _ _) |]
| |- ?G1 ⊕ (?G2 ⊕ ?G3) == _ =>
  refine (Trans _ ((G1 ⊕ G2) ⊕ G3) _ (AssocSum _ _ _) _)
end.

Lemma idm1: -- == ≡1≡.
Proof.
  sym.
  exact (IdDown --).
Qed.

Lemma idm2: -- ⊕ -- == ≡2≡.
Proof.
  cbn.
  sym; clean.
Qed.

Lemma IdRight': forall {n} (g: Graph n 1),
    g ∘ -- == g.
Proof.
  intros.
  rewrite idm1, IdRight; reflexivity.
Qed.

Lemma IdLeft': forall {n} (g: Graph 1 n),
     -- ∘ g == g.
Proof.
  intros.
  rewrite idm1, IdLeft; reflexivity.
Qed.

Lemma stack_wires:
  forall {n m}, (≡n≡ ⊕ ≡m≡) == ≡n+m≡.
Proof.
  induction n as [|n IH]; intros m; cbn.
  clean.
  rewrite <- IH.
  rew_assocsum; refl.
Qed.

Lemma twister_twist: twister 1 1 == ><.
Proof.
  cbn; repeat clean.
  rewrite AssocComp, MFI.
  rewrite idm1, IdRight.
  rewrite stack_wires, IdLeft.
  refl.
Qed.

Lemma Transport_left:
  forall {n m p} (g: Graph n m) (eq: n = p),
    g == eq_rect n (fun x => Graph x m) g p eq.
Proof.
  intros.
  refine (Trans _ _ _ (Transport g eq eq_refl) _).
  rewrite <- eq_rect_eq_dec by auto with arith.
  refl.
Qed.

Lemma Transport_right:
  forall {n m q} (g: Graph n m) (eq: m = q),
    g == eq_rect m (Graph n) g q eq.
Proof.
  intros.
  refine (Trans _ _ _ (Transport g eq_refl eq) _).
  rewrite <- eq_rect_eq_dec by auto with arith.
  refl.
Qed.

Lemma twister_p_0: forall p, twister p 0 == ≡p≡.
Proof.
  induction p as [| p IH]; clean.
  cbn.
  (** TODO: hide with tac **)
  refine (Trans _ _ _ _ _).
  sym; refine (Transport_right _ _).
  refine (Trans _ (_ ∘ _) _ (CongComp _ _ _ _ _ _) _).
  refine (Trans _ (_ ⊕ _) _ (CongSum -- _ _ _ _ _) _).
  refl.
  exact IH.
  rewrite idm1, stack_wires; refl.
  sym; apply Transport_left.
  cbn; clean.
  rewrite idm1, stack_wires.
  rewrite IdRight.
  refl.
Qed.

Definition transport_add_left:
  forall {n m p} (g: Graph (n + m) p), Graph (m + n) p.
Proof.
  intros.
  refine (eq_rect _ (fun x => Graph x p) g _ (Nat.add_comm _ _)). 
Defined.

Definition transport_add_right:
  forall {n m p} (g: Graph p (n + m)), Graph p (m + n).
Proof.
  intros.
  refine (eq_rect _ (Graph p) g _ (Nat.add_comm _ _)). 
Defined.

(** Can we have something of this taste? **)
(* Coercion transport_add_left {n m p}: (Graph (n + m) p) >-> (Graph (m + n) p). *)

Ltac smp :=
  repeat (match goal with
          | H: existT _ _ _ = existT _ _ _ |- _ =>
            apply (inj_pair2_eq_dec _ Nat.eq_dec) in H end); try subst.

Lemma no_twist_gen:
  forall {n m}, (twister n m) ∘ (transport_add_left (twister m n)) == ≡n≡ ⊕ ≡m≡.
Proof.
  induction n as [| n IH]; intros m.
  - cbn.
    refine (Trans _ _ _ (IdLeft _) _).
    refine (Trans _ _ _ _ (Sym _ _ (IdUp _))).
    (** to hide **)
    unfold transport_add_left; refine (Trans _ _ _ (Sym _ _ (Transport_left _ _)) _).
    apply twister_p_0.
  - (** This ride is quite wild **)
    
(*     simpl twister. *)
(*     refine (Trans _ (_ ∘ _) _ (CongComp _ _ _ _ _ _) _). *)
(*     sym; refine (Transport_right _ _). *)
(*     unfold transport_add_left; refine (Trans _ _ _ (Sym _ _ (Transport_left _ _)) _). *)
(*     refine (Transport_left _ _); auto with arith. *)
(* remember ((eq_rect (S (m + n)) (fun H : nat => Graph H (S (m + n))) (twist_aux m ⊕ (≡ n ≡)) (S (n + m)) *)
(*                    (twister_obligation_1 m n))) as g2. *)
(* remember ((eq_rect (m + S n) (fun x : nat => Graph x (m + S n)) (twister m (S n)) (S (m + n)) (eq_sym (plus_n_Sm m n)))) as g1. *)

(* refine (Trans _ _ _ (Sym _ _ (AssocComp _ _ _)) _). *)

(* sym. cbn. *)
(* refine (Trans _ _ _ _ _). *)
(* sym. *)
(* apply AssocSum. *)
(* refine (Sym _ _ (AssocSum _ _ _)) _). *)

(* refine (Trans _ (_ ⊕ _) _ (CongSum _ _ _ _ _ _) _). *)
(* cbn. *)

    (* Lemma inv_empty: forall {n m} (g: Graph n m), *)
    (*     g == ∅ -> n = 0 /\ m = 0. *)
    (* Proof. *)
    (*   induction g; intros eq. *)
    (*   - auto. *)
    (*   - inversion eq. subst; smp. *)

    (*   intros n m g eq; remember ∅ as g'; revert Heqg'. dependent induction eq. *)
    (*   induction 1. auto. *)
    (*   - inversion eq; subst; clear eq. *)
    (*     smp. *)
    (*     induction *)


    (* Lemma eqg_entry: forall {n m p q} (g1: Graph n m) (g2: Graph p q), *)
    (*     g1 == g2 -> n = p. *)
    (* Proof. *)
    (*   induction g1; intros g2 eq; cbn. *)
    (*   - inversion g2; subst; auto. *)
        

    (* refine (Trans _ (_ ∘ _) _ _ _). *)

    (* refine (@Trans _ _ (m + (S n)) _ _  _ (_ ∘ (twister m (S n))) _ _ _). *)
    (* refine (CongComp _ _ _ _ _ _). *)
    (* refl. *)
    (* refine (Trans _ _ _ _ _). *)
    (* refl. *)
    
    (* refine (Trans _ ((twister (S n) m) ∘ (twister m (S n))) _ (CongComp _ _ _ _ _ _) _). *)
    (* refl. *)
    (* unfold transport_add_left; refine (Trans _ _ _ (Sym _ _ (Transport_left _ _)) _). *)
    

    (* sym. *)
    (* simpl idm; rew_assocsum. *)
    (* rewrite <- (IH m). *)

    (* cbn. *)
    (* refine (Trans _ _ _ _ _). *)
    (* sym; refine (Transport_right _ _). *)
Admitted. 

(* Lemma twister_p_1: forall {p n m} (g1: Graph p n) (g2: Graph 1 m), *)
(*     (twister p 1) ∘ (g1 ⊕ g2) == (g2 ⊕ g1). *)
(* Proof. *)
(*   induction p as [| p IH]; intros n m g1 g2. *)
(*   cbn; clean; refine (Trans _ _ _ (IdLeft' _) _). *)


Lemma slide_twist: forall {m n p q} (g1: Graph n m) (g2: Graph p q),
    (g1 ⊕ g2) ∘ (twister m q) == (twister p n) ∘ (g2 ⊕ g1).
Proof.
  induction g1; intros g2.
  - clean; cbn.
    sym.
    refine (Trans ((twister p 0) ∘ (g2 ⊕ ∅)) (≡p≡ ∘ g2) _ _ _).
    apply CongComp; [apply twister_p_0 | apply IdDown].
    rewrite IdLeft, IdRight.
    refl.
  - admit.
  - cbn. 
    refine (Trans _ _ _ (IdRight _) _).
Admitted.
  
(* Lemma tropcool: (-- ⊕ o-) ∘ >- == --. *)
(* Proof. *)
  (* etransitivity. *)
  (* eapply CongComp. *)
  (* refl. *)
  (* apply Sym, Comm. *)
 
(* Theorem bizarrofree: forall {n m: nat} (g1 g2: Graph n m), *)
(*     g1 == g2 -> (bizarro g1) == (bizarro g2). *)
(* Proof. *)
(*   induction 1; cbn; try now (symmetry; constructor); try now constructor. *)
(*   etransitivity; [apply B1 |   symmetry; eapply AssocComp; eauto]. *)
(*   etransitivity; eauto. *)
(* Qed. *)

