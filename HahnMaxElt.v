(******************************************************************************)
(** * Maximal elements of relations *)
(******************************************************************************)

Require Import HahnBase HahnList HahnSets HahnRelationsBasic.
Require Import HahnEquational HahnRewrite.
Require Import NPeano Omega Setoid.

Require Import HahnKat.

Set Implicit Arguments.

Definition max_elt A (r: relation A) (a : A) :=
  forall b (REL: r a b), False.

Definition wmax_elt A (r: relation A) (a : A) :=
  forall b (REL: r a b), a = b.

Require Import RelationAlgebra.lattice.

Lemma max_elt_iff_kat1: forall (A: Type) (a: A) r, max_elt r a <-> ⦗fun b => a = b⦘ ;; r ⊆ bot.
Proof. intros. unfold max_elt. split.
       - intro. unfold inclusion, bot, seq, eqv_rel; simpl.
         intros x y [z [[H1 H2] H3]].
         rewrite <- H1 in H3; rewrite <- H2 in H3.
         apply H in H3. assumption.
       - unfold inclusion, bot, seq, eqv_rel. simpl.
         intros. apply H with (x:=a)(y:=b).
         exists a. auto.
Qed.

Lemma max_elt_iff_kat2: forall (A: Type) (a: A) r, max_elt r a <-> ⦗fun b => b = a⦘ ;; r ⊆ bot.
Proof. intros. unfold max_elt. split.
       - intro. unfold inclusion, bot, seq, eqv_rel; simpl.
         intros x y [z [[H1 H2] H3]].
         rewrite <- H1 in H3; rewrite -> H2 in H3.
         apply H in H3. assumption.
       - unfold inclusion, bot, seq, eqv_rel. simpl.
         intros. apply H with (x:=a)(y:=b).
         exists a. auto.
Qed.

Ltac lift_max_elt1 := repeat rewrite max_elt_iff_kat1 in *.
Ltac lift_max_elt2 := repeat rewrite max_elt_iff_kat2 in *.

Local Axiom LEM: forall (A: Type) (a b: A), (a = b) \/ (not (a = b)). (* TODO *)

Lemma wmax_elt_iff_kat1 (A: Type) (a: A) r:
    wmax_elt r a <-> ⦗fun b => a = b⦘ ;; r ;; ⦗(@neg dset')(fun b => (a = b))⦘ ⊆ bot.
Proof.
  intros. unfold wmax_elt, inclusion, bot, seq, eqv_rel. simpl.
  split.
  - intros H x y [z [[H0 H1] [z0 [H3 [H4 H5]]]]].
    apply H5.
    rewrite H4 in *; clear H4 z0.
    rewrite <- H0 in *; clear H0 z.
    rewrite <- H1 in H3; clear H1. apply H in H3. assumption.
  - intros.
    assert (a <> b -> False).
    { intro. specialize (H a b).
      apply H. exists a. split; [> split; reflexivity | exists b].
      split; [> apply REL | split; [> reflexivity | intro; apply H0; assumption]].
    }
    remember (LEM a b) as lem. clear Heqlem.
    destruct lem.
    + assumption.
    + apply H0 in H1. destruct H1.
Qed.

Lemma wmax_elt_iff_kat2 (A: Type) (a: A) r:
    wmax_elt r a <-> ⦗fun b => b = a⦘ ;; r ;; ⦗(@neg dset') (fun b => (b = a))⦘ ⊆ bot.
Proof.
  rewrite wmax_elt_iff_kat1.
  assert (@weq dset' (fun b : A => b = a) (fun b : A => a = b)).
  { simpl; intro; split; auto. }
  assert (⦗fun b : A => b = a⦘ ;; r ;; ⦗(@neg dset')(fun b : A => b = a)⦘
      <--> ⦗fun b : A => a = b⦘ ;; r ;; ⦗(@neg dset')(fun b : A => a = b)⦘).
  { hkat'. }
  rewrite H0. reflexivity.
Qed.

Ltac lift_wmax_elt1 := repeat rewrite -> wmax_elt_iff_kat1 in *.
Ltac lift_wmax_elt2 := repeat rewrite -> wmax_elt_iff_kat2 in *.

Local Notation "a <--> b" := (same_relation a b)  (at level 60).

Section BasicProperties.

Variable A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma set_subset_max_elt (S: r' ⊆ r) : max_elt r ⊆₁ max_elt r'.
Proof. unfold max_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_subset_wmax_elt (S: r' ⊆ r) : wmax_elt r ⊆₁ wmax_elt r'.
Proof. unfold wmax_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_max_elt (S: r <--> r') : max_elt r ≡₁ max_elt r'.
Proof. unfold max_elt, same_relation, set_equiv, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_wmax_elt (S: r <--> r') : wmax_elt r ≡₁ wmax_elt r'.
Proof. unfold wmax_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma max_elt_weaken : max_elt r a -> wmax_elt r a.
Proof.
  lift_max_elt1; lift_wmax_elt1; hkat'.
Qed.

Lemma max_elt_union : max_elt r a -> max_elt r' a -> max_elt (r +++ r') a.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma wmax_elt_union : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r +++ r') a.
Proof.
  lift_wmax_elt1; hkat'.
Qed.

Lemma max_elt_t : max_elt r a -> max_elt (r⁺) a.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma wmax_elt_rt : wmax_elt r a -> wmax_elt (r＊) a.
Proof.
  lift_wmax_elt1; hkat'.
Qed.

Lemma wmax_elt_t : wmax_elt r a -> wmax_elt (r⁺) a.
Proof.
  lift_wmax_elt1; hkat'.
Qed.

Lemma wmax_elt_eqv (f: A -> Prop) : wmax_elt (eqv_rel f) a.
Proof.
  unfold eqv_rel; red; ins; desf.
Qed.

Lemma wmax_elt_restr_eq B (f: A -> B) :
  wmax_elt r a -> wmax_elt (restr_eq_rel f r) a.
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma max_elt_restr_eq B (f: A -> B) :
  max_elt r a -> max_elt (restr_eq_rel f r) a.
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma wmax_elt_r :
  wmax_elt r a -> wmax_elt (r^?) a.
Proof.
  lift_wmax_elt1; hkat'.
Qed.

Lemma max_elt_seq1 : max_elt r a -> max_elt (r ⨾ r') a.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma wmax_elt_seq2 : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r ⨾ r') a.
Proof.
  lift_wmax_elt1; hkat'.
Qed.

Lemma wmax_elt_seq1 : max_elt r a -> wmax_elt (r ⨾ r') a.
Proof.
  lift_max_elt1; lift_wmax_elt1; hkat'.
Qed.

Lemma max_elt_seq2 : wmax_elt r a -> max_elt r' a -> max_elt (r ⨾ r') a.
Proof.
  lift_max_elt1; lift_wmax_elt1; hkat'.
Qed.

End BasicProperties.

Hint Immediate max_elt_weaken : hahn.
Hint Resolve wmax_elt_union max_elt_union : hahn.
Hint Resolve wmax_elt_t wmax_elt_r wmax_elt_rt max_elt_t : hahn.
Hint Resolve max_elt_restr_eq wmax_elt_restr_eq : hahn.
Hint Resolve max_elt_seq1 max_elt_seq2 wmax_elt_seq1 wmax_elt_seq2 : hahn.

Lemma cod_to_kat (A: Type) (r: relation A) (b: A): (forall x y, r x y -> y = b) -> (r <--> r ;; ⦗fun a => (a = b)⦘).
Proof. 
  unfold_all. firstorder. rewrite <- H1; assumption.
Qed.

Ltac elim_cod COD := apply cod_to_kat in COD; rewrite COD in *; clear COD.

Section MoreProperties.

Variable A : Type.
Implicit Type r : relation A.

Lemma seq_max r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r' <--> ∅₂.
Proof.
  elim_cod COD; lift_max_elt2; hkat'.
Qed.

Lemma seq_max_t r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ⁺ <--> ∅₂.
Proof.
  elim_cod COD; lift_max_elt2; hkat'.
Qed.

Lemma seq_max_rt r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r'＊ <--> r.
Proof.
  elim_cod COD; lift_max_elt2; hkat'.
Qed.

Lemma seq_max_r r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r'^? <--> r.
Proof.
  elim_cod COD; lift_max_elt2; hkat'.
Qed.

Lemma seq_eq_max r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r <--> ∅₂.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma seq_eq_max_t r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r⁺ <--> ∅₂.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma seq_eq_max_rt r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r＊ <--> ⦗eq b⦘.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma seq_eq_max_r r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r^? <--> ⦗eq b⦘.
Proof.
  lift_max_elt1; hkat'.
Qed.

Lemma seq_singl_max r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r <--> ∅₂.
Proof.
  lift_max_elt2; hkat'.
Qed.

Lemma seq_singl_max_t r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r⁺ <--> ∅₂.
Proof.
  lift_max_elt2; hkat'.
Qed.

Lemma seq_singl_max_rt r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r＊ <--> singl_rel a b.
Proof.
  lift_max_elt2; hkat'.
Qed.

Lemma seq_singl_max_r r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r^? <--> singl_rel a b.
Proof.
  lift_max_elt2; hkat'.
Qed.

Lemma max_elt_test r: ⦗max_elt r⦘ ;; r ⊆ bot.
Proof. basic_solver. Qed.

Lemma seq_eqv_max r : 
  ⦗max_elt r⦘ ⨾ r <--> (∅₂).
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma seq_eqv_max_t r :
  ⦗max_elt r⦘ ⨾ r⁺ <--> (∅₂).
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma seq_eqv_max_rt r :
  ⦗max_elt r⦘ ⨾ r＊ <--> ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma seq_eqv_max_r r :
  ⦗max_elt r⦘ ⨾ r^? <--> ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma max_elt_test_dual r: r⁻¹ ⨾ ⦗max_elt r⦘ ⊆ (∅₂).
Proof.
  basic_solver.
Qed.

Lemma transp_seq_eqv_max r : 
  r⁻¹ ⨾ ⦗max_elt r⦘ <--> (∅₂).
Proof.
  pose (@max_elt_test_dual r). hkat'.
Qed.

Lemma transp_seq_eqv_max_t r :
  (r⁻¹)⁺ ⨾ ⦗max_elt r⦘ <--> (∅₂).
Proof.
  pose (@max_elt_test_dual r); hkat'.
Qed.

Lemma transp_seq_eqv_max_rt r :
  (r⁻¹)＊ ⨾ ⦗max_elt r⦘  <--> ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test_dual r); hkat'.
Qed.

Lemma transp_seq_eqv_max_r r :
  (r⁻¹)^? ⨾ ⦗max_elt r⦘ <--> ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test_dual r); hkat'.
Qed.

Lemma wmax_elt_iff_kat3: forall (a: A) r,
    wmax_elt r a <-> ⦗fun b => a = b⦘ ;; r ⊆ ⦗fun b => a = b⦘.
Proof.
  split; unfold_all; unfold wmax_elt.
  - intros H x y [z [[H1 H2] H3]].
    rewrite <- H1 in *; clear H1 z.
    rewrite -> H2 in *; clear H2 a.
    split; [> apply H; apply H3 | reflexivity].
  - intros.
    specialize (H a b). firstorder.
Qed.

Lemma wmax_elt_iff_kat4: forall (a: A) r,
    wmax_elt r a <-> ⦗fun b => b = a⦘ ;; r <--> ⦗fun b => b = a⦘ ;; r ;; ⦗fun b => b = a⦘.
Proof.
  split; unfold_all; unfold wmax_elt.
  - firstorder. exists x0. firstorder. exists y. firstorder. symmetry. apply H.
    rewrite <- H2. rewrite H0. assumption.
    exists x. firstorder. rewrite H0; rewrite <- H3; assumption.
  - intros [H1 H2] y H.
    specialize (H1 a y).
    assert (exists z : A, (a = z /\ a = a) /\ r z y). exists a. firstorder.
    apply H1 in H0.
    destruct H0 as [z [H11 [z0 [_ [H12 H13]]]]].
    rewrite <- H12. symmetry. assumption.
Qed.

(* Require Import RelationAlgebra.kat. *)
(* Require Import RelationAlgebra.prop. *)
(* Require Import RelationAlgebra.kat_tac. *)
(* Require Import RelationAlgebra.kat_reification. *)

(* Ltac aggregate_hoare_hypotheses''' := *)
(*   repeat  *)
(*     match goal with *)
(*       | H: _ ≡ _ |- _ =>  *)
(*         apply (ab_to_hoare (n:=tt)) in H ||  *)
(*         (rewrite (cp_c tt tt H); clear H) ||  *)
(*         (rewrite (pc_c tt tt H); clear H) ||  *)
(*         apply weq_spec in H as [? ?] *)
(*     end; *)
(*   repeat *)
(*     match goal with *)
(*       (* | H: _ ≦ _ |- _ =>  *) *)
(*       (*   apply (ab'_to_hoare (n:=tt)) in H ||  *) *)
(*       (*   apply (bpqc_to_hoare (n:=tt) (m:=tt)) in H ||  *) *)
(*       (*   apply (pbcq_to_hoare (n:=tt) (m:=tt) ) in H ||  *) *)
(*       (*   apply (qcp_to_hoare  (n:=tt) (m:=tt) ) in H || *) *)
(*       (*   apply (qpc_to_hoare  (n:=tt) (m:=tt) ) in H *) *)
(*       | H: _ ≦ bot,  H': _ ≦ bot |- _ =>  *)
(*         apply (join_leq _ _ _ H') in H; clear H' *)
(*     end. *)

Lemma seq_assoc r r' r'': ((r ;; r') ;; r'') <--> (r ;; (r' ;; r'')).
Proof. kat'. Qed.

Lemma eq_elim r b: ⦗fun a : A => a = b⦘ ⨾ r ⨾ ⦗fun a : A => a = b⦘ ⊆ refl_top.
Proof.
    intros.
    unfold eqv_rel. unfold_all. firstorder. rewrite H1. rewrite <- H3. rewrite H2; constructor.
Qed.

(* Result: failed

I don't know why kat can't solve that.

*)
Lemma seq_wmax r r' b
      (MAX: wmax_elt r' b)
      (COD: forall x y, r x y -> y = b)
      (* (COD': r <--> r ;; ⦗fun a => (a = b)⦘) *)
      (* (TEST: t = fun a => (a = b)) *)
      (* (MAX'': ⦗fun a => a = b⦘ ;; r' ;; neg ⦗fun a => a = b⦘ ⊆ bot ) *)
      (* (MAX': ⦗fun a => a = b⦘ ;; r' <-->  ⦗fun a => a = b⦘ ;; r' ;; ⦗fun a => a = b ⦘) *)
  :
    r⨾ r' ⊆ r.
Proof.
  (* rewrite <- TEST in *. *)
  (* clear MAX'. *)
  apply cod_to_kat in COD.
  rewrite wmax_elt_iff_kat4 in MAX.
  rewrite COD at 1. clear COD. 
  rewrite seq_assoc.
  rewrite MAX.
  rewrite eq_elim.
  kat'.
  (* lift_to_kat_all. clear - MAX''. *)
  (* aggregate_hoare_hypotheses'''. *)
  (* (* apply (join_leq _ _ _ COD''') in MAX''. *) *)
  (* rewrite ?leq_iff_cup. *)
  (* (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure"); *)
  (* let L := fresh "L" in intro L; *)
  (* let u := fresh "u" in *)
  (* ra_get_kat_alphabet; intro u. *)
  (* eapply (elim_hoare_hypotheses_weq (u^* ) (u^* )). *)
  (* eassumption. *)
  (* (* || fail "typed hkat is not supported yet"); *) *)
  (* (* assert (forall r1 r2, r1 ⊔ r2 = r1 + r2). *) *)
  (* subst u; revert L; pre_dec true. *)
Qed.

Lemma seq_wmax_t r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ⁺ ⊆ r.
Proof.
  eauto using seq_wmax with hahn.
Qed.

Lemma seq_wmax_rt r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ＊ <--> r.
Proof.
  (* lift_wmax_elt2. elim_cod COD. hkat'. TODO FAIL *)
  rewrite rtE; split; relsf; rewrite seq_wmax_t; relsf.
Qed.

Lemma seq_wmax_r r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ^? <--> r.
Proof.
  rewrite crE; split; relsf; rewrite seq_wmax; relsf.
Qed.

Lemma seq_eq_wmax r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ⊆ ⦗eq b⦘.
Proof.
  eapply seq_wmax; unfold eqv_rel; ins; desf.
Qed.

Lemma seq_eq_wmax_t r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ⁺ ⊆ ⦗eq b⦘.
Proof.
  eauto using seq_eq_wmax with hahn.
Qed.

Lemma seq_eq_wmax_rt r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ＊ <--> ⦗eq b⦘.
Proof.
  rewrite rtE; split; relsf; rewrite seq_eq_wmax_t; relsf.
Qed.

Lemma seq_eq_wmax_r r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ^? <--> ⦗eq b⦘.
Proof.
  rewrite crE; split; relsf; rewrite seq_eq_wmax; relsf.
Qed.

Lemma seq_singl_wmax r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ⊆ singl_rel a b.
Proof.
  (* lift_wmax_elt1. rewrite -> singl_rel_iff_kat. hkat'. TODO FAIL *)
  unfold singl_rel, seq; red; ins; desf; eauto.
  apply MAX in H0; desf.
Qed.

Lemma seq_singl_wmax_t r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ⁺ ⊆ singl_rel a b.
Proof.
  eauto using seq_singl_wmax with hahn.
Qed.

Lemma seq_singl_wmax_rt r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ＊ <--> singl_rel a b.
Proof.
  rewrite rtE; split; relsf; rewrite seq_singl_wmax_t; relsf.
Qed.

Lemma seq_singl_wmax_r r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ^? <--> singl_rel a b.
Proof.
  rewrite crE; split; relsf; rewrite seq_singl_wmax; relsf.
Qed.

End MoreProperties.

Hint Unfold max_elt wmax_elt : unfolderDb.

Require Import Morphisms.

Instance max_elt_Proper A : Proper (_ --> _) _ := set_subset_max_elt (A:=A).
Instance wmax_elt_Proper A : Proper (_ --> _) _ := set_subset_wmax_elt (A:=A).
Instance max_elt_Propere A : Proper (_ ==> _) _ := set_equiv_max_elt (A:=A).
Instance wmax_elt_Propere A : Proper (_ ==> _) _ := set_equiv_wmax_elt (A:=A).


Add Parametric Morphism A : (@max_elt A) with signature
  inclusion --> eq ==> Basics.impl as max_elt_mori.
Proof.
  unfold inclusion, max_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@wmax_elt A) with signature
  inclusion --> eq ==> Basics.impl as wmax_elt_mori.
Proof.
  unfold inclusion, wmax_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@max_elt A) with signature
  same_relation --> eq ==> iff as max_elt_more.
Proof.
  unfold same_relation, inclusion, max_elt; firstorder.
Qed.

Add Parametric Morphism A : (@wmax_elt A) with signature
  same_relation --> eq ==> iff as wmax_elt_more.
Proof.
  unfold same_relation, inclusion, wmax_elt; firstorder.
Qed.

