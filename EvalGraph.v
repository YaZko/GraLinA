Require Import nodep Tactics.
Require Import List.
Require Import ZArith.

(*** Partitions.  *)
(** The partition function splits a list into two subparts. [partition l n1 n2]
return the pair of lists [(l1,l2)] of lengths respectively [n1] and [n2], such
that [l = l1 ++ l2]. It fails when the length of [l] is not exactly the sum of
[n1] and [n2]. *)

Section PARTITION.
  Context {A: Type}.

  Fixpoint partition (l: list A) n1 n2 {struct n1} :=
    match n1 with
      O => if eq_nat_dec (length l) n2 then Some (nil,l) else None
    | S n1 =>
      match l with
        nil => None
      | a::l =>
        match partition l n1 n2 with
          None => None
        | Some (l1,l2) => Some (a::l1,l2)
        end
      end
    end.

  Lemma partition_succeeds:
    forall  n1 n2 (l: list A),
      length l = n1 + n2 ->
      exists l1 l2, partition l n1 n2 = Some (l1,l2) /\ l = l1 ++ l2.
  Proof.
    induction n1; simpl; intros; eauto.
    - subst.
      destruct (Nat.eq_dec); try congruence. eauto.
    - destruct l. simpl in H. congruence.
      simpl in H. injection H. clear H; intro L.
      specialize (IHn1 _ _ L).
      destruct IHn1 as (l1 & l2 & EQ & EQ2).
      rewrite EQ. repeat econstructor; eauto.  subst.  simpl. reflexivity.
  Qed.

  Lemma partition_lengths:
    forall n1 n2 (l: list A) l1 l2,
      partition l n1 n2 = Some (l1,l2) ->
      length l1 = n1 /\ length l2 = n2.
  Proof.
    induction n1; simpl; intros; eauto.
    - destruct (Nat.eq_dec); try congruence. inversion H. subst. tauto. 
    - destruct l. congruence.
      destruct (partition l n1 n2) eqn:Part; try congruence. destruct p.
      inversion H; subst.
      apply IHn1 in Part. destruct Part; split; simpl; auto.
  Qed.

  Lemma partition_0:
    forall n (l:list A) l1 l2,
      partition l n 0 = Some (l1,l2) ->
      l1 = l /\ l2 = nil.
  Proof.
    induction n; simpl; intros; destr_in_all.
    des l2.
    apply IHn in Heqo. intuition; subst; auto.
  Qed.

  Lemma partition_with_exact_lengths:
    forall (l1 l2: list A),
      partition (l1 ++ l2) (length l1) (length l2) = Some (l1,l2).
  Proof.
    induction l1; simpl; intros; eauto.
    destr.
    rewrite IHl1. auto.
  Qed.

  Lemma partition_with_exact_lengths':
    forall (l1 l2: list A) n1 n2,
      n1 = length l1 -> n2 = length l2 ->
      partition (l1 ++ l2) n1 n2 = Some (l1,l2).
  Proof.
    intros; subst.
    eapply partition_with_exact_lengths; eauto.
  Qed.

  Lemma partition_length_left:
    forall n m (l1 l2 l1' l2': list A),
      partition (l1 ++ l2) n m = Some (l1',l2') ->
      n = length l1 ->
      l1' = l1 /\ l2' = l2.
  Proof.
    induction n; simpl; intros; eauto.
    - destr_in_all. des l1.
    - des l1. destr_in H. des p.
      apply IHn in Heqo; auto. destruct Heqo. subst. split. congruence. inv H. auto.
  Qed.

  Lemma partition_length_eq:
    forall n m (l l1 l2: list A),
      partition l n m = Some (l1,l2) ->
      (n + m)%nat = length l.
  Proof.
    induction n; simpl; intros; destr_in_all; eauto.
  Qed.

  Lemma partition_length_right:
    forall n m (l1 l2 l1' l2': list A),
      partition (l1 ++ l2) n m = Some (l1',l2') ->
      m= length l2 ->
      l1' = l1 /\ l2' = l2.
  Proof.
    intros.
    eapply partition_length_left. eauto.
    generalize (partition_lengths _ _ _ _ _ H). intros (? & ?). subst.
    apply partition_length_eq in H. rewrite app_length in H. omega.
  Qed.

  Lemma partition_assoc:
    forall n1 n2 n3 (l: list A) l1 l23,
      partition l n1 (n2 + n3) = Some (l1,l23) ->
      exists l12 l2 l3,
        partition l (n1 + n2) n3 = Some (l12,l3) /\
        partition l12 n1 n2 = Some (l1,l2) /\
        partition l23 n2 n3 = Some (l2, l3).
  Proof.
    induction n1; simpl; intros.
    - destr_in H. inv H.
      edestruct (partition_succeeds _ _ _ e) as (l2 & l2' & eq & eq23).
      rewrite eq. do 3 eexists. split; eauto.
      split; eauto.
      apply partition_lengths in eq. destruct eq; subst.
      destr.
    - des l. destr_in H.
      des p. inv H.
      generalize Heqo. intro P.
      apply IHn1 in Heqo.
      destruct Heqo as (l12 & l3 & l4 & parteq1 & parteq2 & parteq3).
      rewrite parteq1. rewrite parteq3.
      exists (a:: l12), l3, l4.
      repeat split. rewrite parteq2. auto.
  Qed.

  Lemma partition_app:
    forall n1 n2 (l l1 l2: list A),
      partition l n1 n2 = Some (l1,l2) ->
      l = l1 ++ l2.
  Proof.
    induction n1; simpl; intros; eauto.
    destr_in H. inv H. reflexivity.
    destr_in_all. simpl. f_equal. eauto.
  Qed.

End PARTITION.

Definition option_map {A B} (oa: option A) (f: A -> option B): option B :=
  match oa with
    Some a => f a
  | None => None
  end.

Section EVAL.

  (** We define the evaluation of a graph by giving a list of values as input,
  corresponding to the dangling wires on the left of the graph, and returning
  the list of outputs, i.e. the elements on the right-dangling wires. The
  evaluation succeeds only when the correct amount of inputs are given. *)

  Variable A: Type.
  Variable Aadd: A -> A -> A.
  Variable Azero: A.

  Hypothesis Aadd_commut: forall a b, Aadd a b = Aadd b a.
  Hypothesis Aadd_assoc: forall a b c, Aadd a (Aadd b c) = Aadd (Aadd a b) c.
  Hypothesis Aadd_unit: forall a, Aadd Azero a = a.

  Fixpoint graph_eval (l: list A) (g: Graph): option (list A) :=
    match g with
      Empty => match l with nil => Some nil | _ => None end
    | Zero => match l with nil => Some (Azero::nil) | _ => None end
    | Discard => match l with a::nil => Some nil | _ => None end
    | Addition => match l with
                   a::b::nil => Some ((Aadd a b)::nil)
                 | _ => None
                 end
    | Copy => match l with
               a::nil => Some (a::a::nil)
             | _ => None
             end
    | Twist => match l with
                a::b::nil => Some (b::a::nil)
              | _ => None
              end
    | Id => match l with
             a::nil => Some (a::nil)
           | _ => None
           end
    | Sum g1 g2 =>
      match partition l (gin g1) (gin g2) with
        None => None
      | Some (l1,l2) => option_map (graph_eval l1 g1)
                                  (fun r1 =>
                                     option_map (graph_eval l2 g2)
                                                (fun r2 => Some (r1 ++ r2)))
      end
    | Comp g1 g2 =>
      option_map (graph_eval l g1) (fun r1 => graph_eval r1 g2)
    end.

  (** The output has the appropriate length. *)
  Lemma graph_eval_length:
    forall g l r,
      graph_eval l g = Some r ->
      length r = gout g.
  Proof.
    induction g; simpl; intros;
    repeat match goal with
      H: context [match ?l : list A with _ => _ end] |- _ =>
      destruct l; simpl in *; eauto; try congruence
    | H: Some _ = Some _ |- _ => inversion H; subst; clear H
           end; try reflexivity.
    - destruct (graph_eval l0 g1) eqn:GE; simpl in *; try congruence.
      destruct (graph_eval l1 g2) eqn:GE2; simpl in *; try congruence.
      inversion H; subst; clear H.
      rewrite app_length. apply IHg1 in GE. apply IHg2 in GE2. congruence.
    - destruct (graph_eval l g1) eqn:GE; simpl in *; try congruence. eauto.
  Qed.

  (* Given a well-formed graph and input, the evaluation succeeds. *)
  Lemma graph_eval_succeeds:
    forall g l,
      wf g ->
      length l = gin g ->
      exists r,
        graph_eval l g = Some r.
  Proof.
    induction g; simpl; intros.
    - destruct l; simpl in *; eauto; congruence.
    - destruct l; simpl in *; eauto; congruence.
    - destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
    - destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
    - destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
    - destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
    - destruct l; simpl in *; eauto; try congruence.
      destruct l; simpl in *; eauto; try congruence.
    - edestruct (partition_succeeds (gin g1) (gin g2) l) as (l1 & l2 & eq & eq2). auto.
      rewrite eq.
      generalize (partition_lengths _ _ _ _ _ eq). intros (L1 & L2).
      destruct H as (wf1 & wf2).
      edestruct (IHg1 l1 wf1 L1) as (r1 & e1).
      edestruct (IHg2 l2 wf2 L2) as (r2 & e2).
      rewrite e1, e2. simpl. eauto.
    - destruct H as (geq & wf1 & wf2).
      edestruct (IHg1 l wf1 H0) as (r1 & e1). rewrite e1. simpl.
      apply IHg2. auto. rewrite <- geq.
      eapply graph_eval_length; eauto.
  Qed.

  (** The evaluation of identity graphs outputs the same list. *)
  Lemma graph_eval_id:
    forall n l r,
      graph_eval l (≡n≡) = Some r ->
      l = r.
  Proof.
    induction n; simpl; intros; eauto; destr_in_all. subst.
    des (graph_eval l1 (≡n≡)).
    apply IHn in Heqo. congruence.
  Qed.

  Lemma graph_eval_id':
    forall l n,
      n = length l ->
      graph_eval l (≡n≡) = Some l.
  Proof.
    intros; subst.
    induction l; simpl; intros; simpl_gin_gout; repeat destr; destr_in_all;auto.
    rewrite IHl. simpl. auto.
  Qed.

  (** The evaluation of twisting one wire under n other wires has the expected
  effect on lists. *)
  Lemma graph_eval_twist_aux:
    forall n l a,
      n = length l ->
      graph_eval (a::l) (twist_aux n) = Some (l ++ a :: nil).
  Proof.
    induction n; simpl; intros; eauto.
    - rewrite <- H. simpl. des l.
    - des l. inv H.
      simpl_gin_gout. simpl.
      destruct (partition_succeeds (length l0) 1 (a0 :: l0)) as (l1 & l2 & eq & eq2).
      simpl. omega.
      generalize (partition_lengths _ _ _ _ _ eq). intuition. 
      rewrite eq.
      rewrite IHn. simpl. 
      des l2. des l.          
      rewrite <- app_assoc.
      rewrite partition_with_exact_lengths'.
      rewrite graph_eval_id'. simpl.
      f_equal.
      transitivity ((a0::l0)++(a::nil)).
      rewrite eq2. rewrite <- app_assoc. reflexivity.
      simpl. reflexivity.
      auto.  auto. reflexivity. 
      auto.
  Qed.

  (** The evaluation of a more general twister where [length l1] wires go under
  [length l2]. *)
  Lemma graph_eval_twister:
    forall (l1 l2: list A),
      graph_eval (l1 ++ l2) (twister (length l1) (length l2)) =
      Some (l2 ++ l1).
  Proof.
    induction l1; simpl; intros; eauto.
    rewrite graph_eval_id'. rewrite app_nil_r. auto. auto. simpl_gin_gout.
    rewrite app_length.
    des (Nat.eq_dec).
    rewrite IHl1. simpl.
    rewrite partition_with_exact_lengths. simpl.
    rewrite graph_eval_twist_aux; simpl; auto.
    rewrite graph_eval_id'; simpl; auto.
    rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma graph_eval_twister':
    forall (l1 l2: list A) n1 n2,
      n1 = length l1 ->
      n2 = length l2 ->
      graph_eval (l1 ++ l2) (twister n1 n2) =
      Some (l2 ++ l1).
  Proof.
    intros; subst; eapply graph_eval_twister; eauto.
  Qed.

  (** A useful tactic that rewrites common terms and helps automating repetitive tasks.  *)
  Ltac doitall :=
    repeat match goal with
           | H: context [gin (≡_≡)] |- _ => rewrite gin_idm in H
           | H: context [gout (≡_≡)] |- _ => rewrite gout_idm in H
           | |- context [gin (≡_≡)] => rewrite gin_idm
           | |- context [gout (≡_≡)] => rewrite gout_idm
           | H: context[match ?a with _ => _ end] |- _ => des a; try subst
           | H: Some _ = Some _ |- _ => inv H
           | H: option_map ?x ?f = Some _ |- _ => des x
           | H: graph_eval ?l (≡_≡) = _ |- _ => apply graph_eval_id in H; subst
           | H: graph_eval _ _ = _ |- _ => rewrite H
           | H: graph_eval _ ?a = Some ?l,
                Hpart: partition (?l ++ _) (gout ?a) _ = Some _ |- _ =>
             generalize (partition_length_left _ _ _ _ _ _ Hpart (eq_sym (graph_eval_length _ _ _ H)));
             intros (? & ?); subst; revert H Hpart
           end.

  (** If the evaluation succeeds, then the input was good for the graph and the
  graph was well-formed. *)
  Lemma graph_eval_inv:
    forall g l r,
      graph_eval l g = Some r ->
      length l = gin g /\ wf g.
  Proof.
    induction g; simpl; intros; eauto; doitall.
    apply IHg1 in Heqo0.
    apply IHg2 in Heqo1. intuition.
    apply partition_length_eq in Heqo. omega.
    generalize Heqo H.
    apply IHg1 in Heqo.
    apply IHg2 in H. intuition.
    apply graph_eval_length in Heqo0. omega.
  Qed.


  (** Given two equivalent graphs, the evaluation behaves the same. *)
  Lemma eqG_same_eval:
    forall g1 g2,
      g1 == g2 ->
      forall l r,
        graph_eval l g1 = Some r ->
        graph_eval l g2 = Some r.
  Proof.
    induction 1; simpl; intros. 
    - repeat destr.
    - repeat destr; destr_in_all.
    - repeat destr; destr_in_all.
    - repeat destr.
    - repeat destr; destr_in_all.
    - repeat destr; destr_in_all.
    - repeat destr; destr_in_all.
    - repeat destr; destr_in_all.
    - repeat destr; destr_in_all.
    - repeat destr; destr_in_all.
    - des (graph_eval l G). apply graph_eval_id in H. congruence. 
    - des (graph_eval l (≡gin G≡)).
      apply graph_eval_id in Heqo. congruence.
    - destr_in_all. des (graph_eval l1 G).
    - destr_in H. des p.
      apply partition_0 in Heqo.
      intuition subst.
      des (graph_eval l G). inv H.
      rewrite app_nil_r. auto.
    - des (graph_eval l g1).
    - destr_in H. des p. 
      des (graph_eval l0 g1).
      destr_in H. des p0.
      destruct (partition_assoc _ _ _ _ _ _ Heqo) as (l12 & l2' & l3' & parteq1 & parteq2 & parteq3).
      rewrite parteq1, parteq2.
      rewrite Heqo0. simpl.
      rewrite Heqo1 in parteq3. inv parteq3.
      des (graph_eval l2' g2).
      des (graph_eval l3' g3). rewrite <- app_assoc. congruence.
    - repeat destr; destr_in_all.
    - revert H; simpl_gin_gout. repeat destr; destr_in_all.
      intros.
      des (graph_eval l0 (≡ gin A0 ≡)).
      apply graph_eval_id in Heqo0. subst.
      des (graph_eval l1 B).
      destr_in H. des p.
      generalize (partition_lengths _ _ _ _ _ Heqo).
      intros (L2 & L1).
      generalize (partition_length_left _ _ _ _ _ _ Heqo1 (eq_sym L2)). intros (? & ?); subst.
      des (graph_eval l2 A0).
      des (graph_eval l0 (≡gout B≡)).
      apply graph_eval_id in Heqo3. subst.
      congruence.
    - doitall.
      simpl. auto.
    - doitall.
      destruct (partition_lengths _ _ _ _ _ Heqo) as (L1 & L2).
      rewrite graph_eval_id'; auto. simpl.
      generalize (graph_eval_length _ _ _ Heqo2); intro L4.
      rewrite graph_eval_twister' in H; auto.
      rewrite graph_eval_twister'; auto. simpl.
      rewrite partition_with_exact_lengths'; auto.
      rewrite graph_eval_id'; auto. simpl.
      rewrite Heqo1. simpl.
      auto.
      symmetry; eapply graph_eval_length; eauto.
    - doitall.
      destruct (partition_lengths _ _ _ _ _ Heqo) as (L1 & L2).
      rewrite graph_eval_id'; auto. simpl.
      generalize (graph_eval_length _ _ _ Heqo2); intro L4.
      generalize (graph_eval_length _ _ _ Heqo1); intro L3. 
      rewrite graph_eval_twister' in H; auto.
      rewrite graph_eval_twister'; auto. simpl.
      rewrite partition_with_exact_lengths'; auto.
      rewrite graph_eval_id'; auto. simpl.
      rewrite Heqo2. simpl.
      auto.
    - destr. des p. doitall.
      generalize (graph_eval_length _ _ _ Heqo4); intro L4.
      generalize (graph_eval_length _ _ _ Heqo5); intro L3. 
      rewrite partition_with_exact_lengths' in Heqo1; auto.
      inv Heqo1. doitall. simpl. auto.
      congruence. congruence.
    - destruct (eqG_same_arity _ _ H) as (w1 & gout1 & gin1).
      destruct (eqG_same_arity _ _ H0) as (w2 & gout2 & gin2).
      rewrite <- gin1, <- gin2. destr. des p.
      doitall. erewrite IHeqG1; eauto.
      simpl. erewrite IHeqG2; eauto.
      simpl. auto.
    - doitall.
      erewrite IHeqG1; eauto.
    - auto.
    - destruct (graph_eval_inv _ _ _ H0) as (L & W).
      generalize (eqG_same_arity _ _ H). intuition.
      rewrite <- H4 in L.
      destruct (graph_eval_succeeds _ _ H2 L) as (r' & eq).
      rewrite eq.
      apply IHeqG in eq. congruence.
    - eauto.
  Qed.

  Lemma eqG_same_eval':
    forall g1 g2 l,
      g1 == g2 ->
      graph_eval l g1 = graph_eval l g2.
  Proof.
    intros.
    des (graph_eval l g1).
    symmetry; eapply eqG_same_eval; eauto.
    des (graph_eval l g2).
    symmetry in H.
    eapply eqG_same_eval in H; eauto. congruence.
  Qed.

End EVAL.
