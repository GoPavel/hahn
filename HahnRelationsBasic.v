Require Import HahnBase HahnList.
Require Export HahnRelationsBasicDef.

Require Import HahnKat.

Set Implicit Arguments.

Notation "a ≡ b" := (same_relation a b)  (at level 60).
Notation "a ^+" := (clos_trans a) (at level 1, only parsing).
Notation "a ^*" := (clos_refl_trans a) (at level 1, only parsing).

(******************************************************************************)
(** ** Very basic properties *)
(******************************************************************************)

Lemma r_refl A (r: relation A) x : r^? x x.
Proof.
  assert (refl_top ⊆ r^?).
  { kat'. }
  apply H; constructor.
Qed.

Lemma r_step A (r: relation A) x y : r x y -> r^? x y.
Proof.
  assert (r ⊆ r^?).
  { kat'. }
  exact (H x y).
Qed.

Hint Immediate r_refl r_step.

Section BasicProperties.

Variables A B : Type.
Variable dom : A -> Prop.
Variable f: A -> B.
Variables r r' r'' : relation A.

Lemma immediateE : immediate r ≡ r \ (r ⨾ r).
Proof.
  unfold immediate, seq, minus_rel.
  repeat split; try red; ins; desf; eauto.
Qed.

Lemma clos_trans_mon a b :
  r⁺ a b ->
  (forall a b, r a b -> r' a b) ->
  r'⁺ a b.
Proof.
  induction 1; ins; eauto using clos_trans.
Qed.

Lemma clos_refl_trans_mon a b :
  r＊ a b ->
  (forall a b, r a b -> r' a b) ->
  r'＊ a b.
Proof.
  induction 1; ins; eauto using clos_refl_trans.
Qed.

Lemma clos_refl_transE a b :  r＊ a b <-> a = b \/ r⁺ a b.
Proof.
  split; ins; desf; vauto; induction H; desf; vauto.
Qed.

Lemma clos_trans_in_rt a b : r⁺ a b -> r＊ a b.
Proof.
  induction 1; vauto.
Qed.

Lemma rt_t_trans a b c : r＊ a b -> r⁺ b c -> r⁺ a c.
Proof.
  ins; induction H; eauto using clos_trans.
Qed.

Lemma t_rt_trans a b c : r⁺ a b -> r＊ b c -> r⁺ a c.
Proof.
  ins; induction H0; eauto using clos_trans.
Qed.

Lemma t_step_rt x y : r⁺ x y <-> (exists z, r x z /\ r＊ z y).
Proof.
  split; ins; desf.
    by apply clos_trans_tn1 in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma t_rt_step x y : r⁺ x y <-> (exists z, r＊ x z /\ r z y).
Proof.
  split; ins; desf.
    by apply clos_trans_t1n in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma clos_trans_of_transitiveD (T: transitive r) x y :
  r⁺ x y -> r x y.
Proof.
  induction 1; eauto.
Qed.

Lemma clos_trans_of_transitive (T: transitive r) x y :
  r⁺ x y <-> r x y.
Proof.
  by split; ins; eauto using t_step; eapply clos_trans_of_transitiveD.
Qed.

Lemma clos_refl_trans_of_transitive (T: transitive r) x y :
  r＊ x y <-> r^? x y.
Proof.
  by ins; rewrite clos_refl_transE, clos_trans_of_transitive; ins.
Qed.

Lemma clos_trans_eq :
  forall B (f : A -> B)
    (H: forall a b (SB: r a b), f a = f b) a b
    (C: r⁺ a b),
  f a = f b.
Proof.
  ins; induction C; eauto; congruence.
Qed.

Lemma trans_irr_acyclic :
  irreflexive r -> transitive r -> acyclic r.
Proof.
  eby repeat red; ins; eapply H, clos_trans_of_transitiveD.
Qed.

Lemma is_total_restr :
  is_total dom r ->
  is_total dom (restr_rel dom r).
Proof.
  red; ins; eapply H in NEQ; eauto; desf; vauto.
Qed.

Lemma clos_trans_restrD x y :
  clos_trans (restr_rel dom r) x y -> dom x /\ dom y.
Proof.
  unfold restr_rel; induction 1; ins; desf.
Qed.

Lemma clos_trans_restr_eqD x y :
  clos_trans (restr_eq_rel f r) x y -> f x = f y.
Proof.
  unfold restr_eq_rel; induction 1; ins; desf; congruence.
Qed.

Lemma acyclic_antisymmetric :
  acyclic r -> antisymmetric r.
Proof.
  clear; autounfold with unfolderDb; intuition.
  exfalso; eauto using clos_trans.
Qed.

Lemma trans_irr_antisymmetric :
  irreflexive r -> transitive r -> antisymmetric r.
Proof.
  auto using acyclic_antisymmetric, trans_irr_acyclic.
Qed.

Lemma strict_partial_order_antisymmetric :
  strict_partial_order r -> antisymmetric r.
Proof.
  unfold strict_partial_order; ins; desc. 
  auto using trans_irr_antisymmetric.
Qed.

Lemma irreflexive_inclusion:
  r ⊆ r' ->
  irreflexive r' ->
  irreflexive r.
Proof.
  unfold irreflexive, inclusion; eauto.
Qed.

Lemma irreflexive_union :
  irreflexive (r ∪ r') <-> irreflexive r /\ irreflexive r'.
Proof.
  unfold irreflexive, union; repeat split;
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_seqC :
  irreflexive (r ⨾ r') <-> irreflexive (r' ⨾ r).
Proof.
  unfold irreflexive, seq; repeat split;
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_restr :
  irreflexive r -> irreflexive (restr_rel dom r).
Proof.
  unfold irreflexive, restr_rel; ins; desf; eauto.
Qed.

Lemma inclusion_acyclic :
  r ⊆ r' ->
  acyclic r' ->
  acyclic r.
Proof.
  repeat red; ins; eapply H0, clos_trans_mon; eauto.
Qed.

Lemma transitive_cr : transitive r -> transitive r^?.
Proof.
  unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma transitive_restr : transitive r -> transitive (restr_rel dom r).
Proof.
  unfold restr_rel; red; ins; desf; eauto.
Qed.

Lemma transitive_ct : transitive r⁺.
Proof. kat'. Qed.

Lemma transitive_rt : transitive r＊.
Proof. kat'. Qed.

Ltac lift_reflexive := repeat rewrite -> reflexive_iff_kat in *.

Lemma reflexive_rt : reflexive r＊.
Proof. kat'. Qed.

Lemma reflexive_cr : reflexive r^?.
Proof. kat'. Qed.

Lemma reflexive_seq : reflexive r -> reflexive r' -> reflexive (r ⨾ r').
Proof. vauto. Qed.

Lemma reflexive_union_l : reflexive r -> reflexive (r ∪ r').
Proof. vauto. Qed.

Lemma reflexive_union_r : reflexive r' -> reflexive (r ∪ r').
Proof. vauto. Qed.

Lemma reflexive_inter : reflexive r -> reflexive r' -> reflexive (r ∩ r').
Proof. vauto. Qed.

Lemma restr_eq_trans :
  transitive r -> transitive (restr_eq_rel f r).
Proof.
  unfold transitive, restr_eq_rel; ins; desf; split; eauto; congruence.
Qed.

Lemma irreflexive_restr_eq :
  irreflexive (restr_eq_rel f r) <-> irreflexive r.
Proof.
  unfold irreflexive, restr_eq_rel; split; ins; desf; eauto.
Qed.

Lemma upward_closed_seq P :
  upward_closed r P ->
  upward_closed r' P ->
  upward_closed (r ⨾ r') P.
Proof.
  hkat'.
Qed.

Lemma upward_closed_ct P :
  upward_closed r P -> upward_closed r⁺ P.
Proof.
  hkat'.
Qed.

Lemma upward_closed_rt P :
  upward_closed r P -> upward_closed r＊ P.
Proof.
  hkat'.
Qed.

(** Lemmas about inclusion *)
(******************************************************************************)

Lemma eq_in_l : r ≡ r' -> r ⊆ r'.
Proof. by destruct 1. Qed.

Lemma eq_in_r : r ≡ r' -> r' ⊆ r.
Proof. by destruct 1. Qed.

Lemma inclusion_refl : reflexive (@inclusion A).
Proof. repeat red; ins. Qed.

Lemma inclusion_trans : transitive (@inclusion A).
Proof. repeat red; eauto. Qed.

Lemma inclusion_refl2 : r ⊆ r.
Proof. kat'. Qed.

Lemma same_relation_refl2 : r ≡ r.
Proof. kat'. Qed.

Lemma inclusion_inter_l1 : r ∩ r' ⊆ r.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_l2 : r ∩ r' ⊆ r'.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_l1_search : r ⊆ r'' -> r ∩ r' ⊆ r''.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_l2_search : r' ⊆ r'' -> r ∩ r' ⊆ r''.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_r : r ⊆ r' -> r ⊆ r'' -> r ⊆ r' ∩ r''.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_mon s s' : r ⊆ r' -> s ⊆ s' -> r ∩ s ⊆ r' ∩ s'.
Proof. clear; firstorder. Qed.

Lemma inclusion_union_r1 : r ⊆ r ∪ r'.
Proof. kat'. Qed.

Lemma inclusion_union_r2 : r' ⊆ r ∪ r'.
Proof. kat'. Qed.

Lemma inclusion_union_l : r ⊆ r'' -> r' ⊆ r'' -> r ∪ r' ⊆ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r1_search : r ⊆ r' -> r ⊆ r' ∪ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r2_search : r ⊆ r'' -> r ⊆ r' ∪ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r :
  r ⊆ r' \/ r ⊆ r'' -> r ⊆ r' ∪ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_mon s s' :
  r ⊆ r' -> s ⊆ s' -> r ∪ s ⊆ r' ∪ s'.
Proof.
  unfold inclusion, union; ins; desf; eauto.
Qed.

Lemma inclusion_bunion_l (P : B -> Prop) (rr : B -> relation A) :
  (forall x, P x -> rr x ⊆ r') -> bunion P rr ⊆ r'.
Proof.
  clear; firstorder.
Qed.

Lemma inclusion_bunion_r (x: B) (P : B -> Prop) (rr : B -> relation A) : 
  P x -> r ⊆ rr x -> r ⊆ bunion P rr.
Proof.
  clear; firstorder.
Qed.

Lemma inclusion_seq_mon s s' : r ⊆ r' -> s ⊆ s' -> r ⨾ s ⊆ r' ⨾ s'.
Proof.
  unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma inclusion_seq_refl :
  r ⊆ r'' -> r' ⊆ r'' -> transitive r'' -> r ⨾ r'^? ⊆ r''.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma inclusion_restr : restr_rel dom r ⊆ r.
Proof.
  kat'.
Qed.

Lemma inclusion_restr_rel_l : r ⊆ r' -> restr_rel dom r ⊆ r'.
Proof.
  unfold inclusion, seq, restr_rel; ins; desf; eauto.
Qed.

Lemma inclusion_restr_eq : restr_eq_rel f r ⊆ r.
Proof.
  unfold restr_eq_rel, inclusion; ins; desf.
Qed.

Lemma inclusion_restr_eq_l : r ⊆ r' -> restr_eq_rel f r ⊆ r'.
Proof.
  unfold inclusion, seq, restr_eq_rel; ins; desf; eauto.
Qed.

Lemma inclusion_minus_rel : r \ r' ⊆ r.
Proof.
  unfold minus_rel, inclusion; ins; desf; auto.
Qed.

Lemma inclusion_minus_mon s s' : r ⊆ r' -> s' ⊆ s -> r \ s ⊆ r' \ s'.
Proof.
  unfold minus_rel, inclusion, not; ins; desf; eauto.
Qed.

Lemma inclusion_minus_l s : r \ r' ⊆ s <-> r ⊆ r' ∪ s.
Proof.
  unfold minus_rel, union, inclusion; split; ins; desf.
    2: by eapply H in H0; desf; eauto.
  by destruct (classic (r' x y)); eauto.
Qed.

Lemma inclusion_union_minus : r ⊆ (r \ r') ∪ r'.
Proof.
  by unfold minus_rel, union, inclusion; clear; intros; tauto.
Qed.

Lemma inclusion_eqv_rel_true : ⦗dom⦘  ⊆ ⦗fun _ => True⦘.
Proof.
  kat'.
Qed.

(** Inclusions involving reflexive closure. *)

Lemma inclusion_id_cr : ⦗fun _ => True⦘ ⊆ r^?.
Proof.
  kat'.
Qed.

Lemma inclusion_eqv_cr : ⦗dom⦘ ⊆ r^?.
Proof.
  kat'.
Qed.

Lemma inclusion_step_cr : r ⊆ r' -> r ⊆ r'^?.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto.
Qed.

Lemma inclusion_r_cr : r ⊆ r' -> r^? ⊆ r'^?.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto.
Qed.

Lemma inclusion_cr_ind :
  reflexive r' -> r ⊆ r' -> r^? ⊆ r'.
Proof.
  unfold clos_refl; ins; red; ins; desf; eauto.
Qed.

(** Inclusions involving transitive closure. *)

Lemma inclusion_step_t : r ⊆ r' -> r ⊆ r'⁺.
Proof.
  unfold seq; red; ins; desf; eauto using t_step.
Qed.

Lemma inclusion_t_rt : r⁺ ⊆  r＊.
Proof.
  kat'.
Qed.

Lemma inclusion_t_t : r ⊆ r' -> r⁺ ⊆ r'⁺.
Proof.
  by red; ins; eapply clos_trans_mon.
Qed.

Lemma inclusion_t_t2 : r ⊆ r'⁺ -> r⁺ ⊆ r'⁺.
Proof.
  induction 2; eauto using clos_trans.
Qed.

Lemma inclusion_t_ind : r ⊆ r' -> transitive r' -> r⁺ ⊆ r'.
Proof. unfold seq; induction 3; eauto. Qed.

Lemma inclusion_t_ind_left : r ⊆ r' -> r⨾ r' ⊆ r' -> r⁺ ⊆ r'.
Proof.
  unfold seq, inclusion; ins.
  apply clos_trans_t1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_t_ind_right : r ⊆ r' -> r'⨾ r ⊆ r' -> r⁺ ⊆ r'.
Proof.
  unfold seq, inclusion; ins.
  apply clos_trans_tn1 in H1; induction H1; eauto.
Qed.

(** Inclusions involving reflexive-transitive closure. *)

Lemma inclusion_id_rt : ⦗fun _ => True⦘ ⊆ r'＊.
Proof.
  kat'.
Qed.

Lemma inclusion_eqv_rt : ⦗dom⦘ ⊆ r'＊.
Proof.
  kat'.
Qed.

Lemma inclusion_step_rt : r ⊆ r' -> r ⊆ r'＊.
Proof.
  unfold seq; red; ins; desf; eauto using rt_step.
Qed.

Lemma inclusion_r_rt : r ⊆ r' -> r^? ⊆ r'＊.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto using rt_step, rt_refl.
Qed.

Lemma inclusion_rt_rt : r ⊆ r' -> r＊ ⊆ r'＊.
Proof.
  red; ins; eapply clos_refl_trans_mon; eauto.
Qed.

Lemma inclusion_rt_rt2 : r ⊆ r'＊ -> r＊ ⊆ r'＊.
Proof.
  induction 2; eauto using clos_refl_trans.
Qed.

Lemma inclusion_rt_ind :
  reflexive r' -> r ⊆ r' -> transitive r' -> r＊ ⊆ r'.
Proof. unfold seq, eqv_rel; induction 4; eauto. Qed.

Lemma inclusion_rt_ind_left :
  reflexive r' -> r⨾ r' ⊆ r' -> r＊ ⊆ r'.
Proof.
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rt1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_rt_ind_right :
  reflexive r' -> r'⨾ r ⊆ r' -> r＊ ⊆ r'.
Proof.
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rtn1 in H1; induction H1; eauto.
Qed.

Lemma inclusion_seq_trans t :
  transitive t -> r ⊆ t -> r' ⊆ t -> r⨾ r' ⊆ t.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma inclusion_seq_rt :
  r ⊆ r''＊ -> r' ⊆ r''＊ -> r⨾ r' ⊆ r''＊.
Proof.
  apply inclusion_seq_trans; vauto.
Qed.

Lemma inclusion_seq_l :
  r ⊆ r' -> reflexive r'' -> r ⊆ r' ⨾ r''.
Proof.
  unfold seq, eqv_rel, inclusion; ins; eauto 8.
Qed.

Lemma inclusion_seq_r :
  reflexive r' -> r ⊆ r'' -> r ⊆ r' ⨾ r''.
Proof.
  unfold seq, eqv_rel, inclusion; ins; eauto 8.
Qed.

(** Lemmas about functional relations *)
(******************************************************************************)

Lemma functional_alt :
  functional r <-> r⁻¹ ⨾ r ⊆ ⦗fun _ => True⦘.
Proof.
  unfold functional, seq, transp, eqv_rel, inclusion.
  split; ins; desf; [|apply H]; eauto.
Qed.

Lemma functional_eqv_rel : functional ⦗dom⦘.
Proof.
  unfold functional, eqv_rel; ins; desf.
Qed.

Lemma functional_seq  :
  functional r -> functional r' -> functional (r ⨾ r').
Proof.
  unfold functional, seq; ins; desf.
  assert (z0 = z1); subst; eauto.
Qed.

Lemma functional_union  :
  functional r -> functional r' ->
  (forall x, dom_rel r x -> dom_rel r' x -> False) ->
  functional (r ∪ r').
Proof.
  unfold functional, union, dom_rel; ins; desf; eauto;
    try solve [exfalso; eauto].
Qed.

Lemma functional_inter_l : functional r -> functional (r ∩ r').
Proof. clear; firstorder. Qed.

Lemma functional_inter_r : functional r' -> functional (r ∩ r').
Proof. clear; firstorder. Qed.

Lemma functional_minus : functional r -> functional (r \ r').
Proof. clear; firstorder. Qed.

Lemma functional_restr : functional r -> functional (restr_rel dom r).
Proof. clear; firstorder. Qed.

Lemma functionalE : functional r -> exists f, forall x y, r x y <-> f x = Some y.
Proof.
  clear; unfold functional; ins.
  forward apply unique_choice 
    with (R := fun x y => y = None /\ ~ (exists m, r x m) \/
                          exists m, y = Some m /\ r x m) as X; ins; desf.
    by tertium_non_datur (exists m, r x m); desc; [exists (Some m)| exists None]; 
       split; ins; desf; try f_equal; eauto; try solve [exfalso; eauto].
  exists f; ins; specialize (X x); split; ins; desf; try solve [exfalso; eauto].
  rewrite X; f_equal; eauto.
Qed.

End BasicProperties.

(** Declare several of the above lemmas as hints for [(e)auto]. *)

Hint Resolve same_relation_refl2.

Hint Resolve
     reflexive_seq reflexive_rt reflexive_cr
     reflexive_union_l reflexive_union_r reflexive_inter
     transitive_rt transitive_ct
  : hahn.

Hint Resolve
     inclusion_refl2 same_relation_refl2
     inclusion_inter_l1_search inclusion_inter_l2_search inclusion_inter_r
     inclusion_union_r1 inclusion_union_r2
     inclusion_union_r1_search inclusion_union_r2_search inclusion_union_l
     inclusion_seq_mon inclusion_minus_mon
     inclusion_restr_eq_l inclusion_restr_rel_l
  : hahn.

Hint Resolve trans_irr_antisymmetric strict_partial_order_antisymmetric : hahn.

Hint Resolve
     inclusion_step_t inclusion_t_t inclusion_t_ind inclusion_rt_rt
     inclusion_r_rt inclusion_step_rt inclusion_step_cr inclusion_r_cr : hahn.

Hint Immediate inclusion_acyclic : hahn.

Hint Immediate inclusion_t_rt : hahn.
Hint Immediate inclusion_eqv_rt inclusion_eqv_cr : hahn.

Lemma clos_trans_of_clos_trans A (r : relation A) x y :
  r⁺⁺ x y <-> r⁺ x y.
Proof.
  generalize x y; kat'.
Qed.

Lemma clos_trans_of_clos_trans1 A (r r' : relation A) x y :
  (fun a b => r⁺ a b \/ r' a b)⁺ x y <->
  (fun a b => r a b \/ r' a b)⁺ x y.
Proof.
  assert ((r⁺ ∪ r')⁺ ≡ (r ∪ r')⁺).
  { kat'. }
  destruct H as [H1 H2].
  split; [> apply H1 | apply H2].
Qed.
