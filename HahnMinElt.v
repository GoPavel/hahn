(******************************************************************************)
(** * Minimal elements of relations *)
(******************************************************************************)

Require Import HahnBase HahnList HahnSets HahnRelationsBasic.
Require Import HahnEquational HahnRewrite HahnMaxElt.
Require Import NPeano Omega Setoid.

Require Import HahnKat.
Require Import RelationAlgebra.lattice.

Set Implicit Arguments.

Local Notation "a <--> b" := (same_relation a b)  (at level 60).

Definition min_elt A (r: relation A) (a : A) :=
  forall b (REL: r b a), False.

Definition wmin_elt A (r: relation A) (a : A) :=
  forall b (REL: r b a), a = b.


Lemma min_elt_iff_kat1 A (r: relation A) (a: A):
  min_elt r a <-> r ;; ⦗fun b => a = b⦘ ⊆ bot.
Proof.
  unfold_all. unfold min_elt.
  firstorder.
  - apply (H x). rewrite H2; assumption.
  - apply (H b a). exists a. auto.
Qed.

Lemma min_elt_iff_kat2 A (r: relation A) (a: A):
  min_elt r a <-> r ;; ⦗fun b => b = a⦘ ⊆ bot.
Proof.
  unfold_all. unfold min_elt.
  firstorder.
  - apply (H x); rewrite <- H2; assumption.
  - apply (H b a). exists a; auto.
Qed.

Ltac lift_min_elt1 := repeat rewrite min_elt_iff_kat1 in *.
Ltac lift_min_elt2 := repeat rewrite min_elt_iff_kat2 in *.

Local Axiom LEM: forall (A: Type) (a b: A), (a = b) \/ (not (a = b)). (* TODO *)

Lemma wmin_elt_iff_kat1 A (r: relation A) (a: A):
  wmin_elt r a <-> ⦗(@neg dset') (fun b => (a = b))⦘ ;; r ;; ⦗fun b => a = b⦘ ⊆ bot.
Proof.
  unfold_all; unfold wmin_elt.
  split.
  - intros H x y [z [[H0 H1] [z0 [H2 [H3 H4]]]]].
    rewrite <- H4 in *; clear H4 H3.
    apply H in H2. rewrite <- H2 in *. symmetry in H0. apply H1; apply H0.
  - intros.
    assert (a <> b -> False).
    {
      specialize (H b a). intro.
      apply H. exists b. split; [> split; [> reflexivity | assumption] | exists a; auto].
    }
    pose (lem := LEM a b).
    destruct lem.
    + assumption.
    + apply H0 in H1. destruct H1.
Qed.

Lemma wmin_elt_iff_kat2 A (r: relation A) (a: A):
  wmin_elt r a <-> ⦗(@neg dset') (fun b => (b = a))⦘ ;; r ;; ⦗fun b => b = a⦘ ⊆ bot.
Proof.
  rewrite wmin_elt_iff_kat1.
  assert (@weq dset' (fun b : A => b = a) (fun b : A => a = b)).
  { simpl; intro; split; auto. }
  assert (⦗(@neg dset')(fun b : A => b = a)⦘ ⨾ r ⨾ ⦗fun b : A => b = a⦘ <--> ⦗(@neg dset')(fun b : A => a = b)⦘ ⨾ r ⨾ ⦗fun b : A => a = b⦘).
  { hkat'. }
  rewrite H0. reflexivity.
Qed.

Ltac lift_wmin_elt1 := repeat rewrite wmin_elt_iff_kat1 in *.
Ltac lift_wmin_elt2 := repeat rewrite wmin_elt_iff_kat2 in *.

Section BasicProperties.

Variable A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma min_transp : min_elt r⁻¹ ≡₁ max_elt r.
Proof.
  split; unfold min_elt, max_elt, transp, set_subset; ins; desf.  
Qed.

Lemma max_transp : max_elt r⁻¹ ≡₁ min_elt r.
Proof.
  split; unfold min_elt, max_elt, transp, set_subset; ins; desf.  
Qed.

Lemma set_subset_min_elt (S: r' ⊆ r) : min_elt r ⊆₁ min_elt r'.
Proof. unfold min_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_subset_wmin_elt (S: r' ⊆ r) : wmin_elt r ⊆₁ wmin_elt r'.
Proof. unfold wmin_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_min_elt (S: r <--> r') : min_elt r ≡₁ min_elt r'.
Proof. unfold min_elt, same_relation, set_equiv, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_wmin_elt (S: r <--> r') : wmin_elt r ≡₁ wmin_elt r'.
Proof. unfold wmin_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma min_elt_weaken : min_elt r a -> wmin_elt r a.
Proof.
  lift_min_elt1. lift_wmin_elt1. hkat'.
Qed.

Lemma min_elt_union : min_elt r a -> min_elt r' a -> min_elt (r +++ r') a.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma wmin_elt_union : wmin_elt r a -> wmin_elt r' a -> wmin_elt (r +++ r') a.
Proof.
  lift_min_elt1. lift_wmin_elt1. hkat'.
Qed.

Lemma min_elt_t : min_elt r a -> min_elt (r⁺) a.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma wmin_elt_rt : wmin_elt r a -> wmin_elt (r＊) a.
Proof.
  red; ins; apply clos_rt_rt1n in REL; induction REL; intuition; desf; eauto.
Qed.

Lemma wmin_elt_t : wmin_elt r a -> wmin_elt (r⁺) a.
Proof.
  lift_wmin_elt1. hkat'.
Qed.

Lemma wmin_elt_eqv (f: A -> Prop) : wmin_elt (eqv_rel f) a.
Proof.
  unfold eqv_rel; red; ins; desf.
Qed.

Lemma wmin_elt_restr_eq B (f: A -> B) :
  wmin_elt r a -> wmin_elt (restr_eq_rel f r) a.
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma min_elt_restr_eq B (f: A -> B) :
  min_elt r a -> min_elt (restr_eq_rel f r) a.
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma wmin_elt_r :
  wmin_elt r a -> wmin_elt (r^?) a.
Proof.
  lift_wmin_elt1; hkat'.
Qed.

Lemma min_elt_seq1 : min_elt r' a -> min_elt (r ⨾ r') a.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma wmin_elt_seq2 : wmin_elt r a -> wmin_elt r' a -> wmin_elt (r ⨾ r') a.
Proof.
  lift_wmin_elt1; hkat'.
Qed.

Lemma wmin_elt_seq1 : min_elt r' a -> wmin_elt (r ⨾ r') a.
Proof.
  lift_min_elt1; lift_wmin_elt1; hkat'.
Qed.

Lemma min_elt_seq2 : min_elt r a -> wmin_elt r' a -> min_elt (r ⨾ r') a.
Proof.
  lift_min_elt1; lift_wmin_elt1; hkat'.
Qed.

End BasicProperties.

Hint Immediate min_elt_weaken : hahn.
Hint Resolve wmin_elt_union min_elt_union : hahn.
Hint Resolve wmin_elt_t wmin_elt_r wmin_elt_rt min_elt_t : hahn.
Hint Resolve min_elt_restr_eq wmin_elt_restr_eq : hahn.
Hint Resolve min_elt_seq1 min_elt_seq2 wmin_elt_seq1 wmin_elt_seq2 : hahn.

Section MoreProperties.

Variable A : Type.
Implicit Type r : relation A.

Lemma dom_to_kat r b: (forall x y, r x y -> x = b) -> (r <--> ⦗fun x => x = b⦘ ;; r).
Proof.
  unfold_all. firstorder. rewrite <- H0 in H1. assumption.
Qed.

Ltac elim_dom DOM := apply dom_to_kat in DOM; rewrite DOM in *; clear DOM.

Lemma seq_min r r' b
      (MAX: min_elt r b) (DOM: forall x y, r' x y -> x = b) :
  r ⨾ r' <--> ∅₂.
Proof.
  elim_dom DOM; lift_min_elt2. hkat'.
Qed.

Lemma seq_min_t r r' b
      (MAX: min_elt r b) (DOM: forall x y, r' x y -> x = b) :
  r ⁺ ⨾ r'  <--> ∅₂.
Proof.
  elim_dom DOM; lift_min_elt2; hkat'.
Qed.

Lemma seq_min_rt r r' b
      (MAX: min_elt r b) (COD: forall x y, r' x y -> x = b) :
  r ＊ ⨾ r' <--> r'.
Proof.
  elim_dom COD; lift_min_elt2; hkat'.
Qed.

Lemma seq_min_r r r' b
      (MAX: min_elt r b) (COD: forall x y, r' x y -> x = b) :
  r ^? ⨾ r' <--> r'.
Proof.
  elim_dom COD; lift_min_elt2; hkat'.
Qed.

Lemma seq_min_eq r b (MAX: min_elt r b) :
  r ⨾⦗eq b⦘ <--> ∅₂.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma seq_min_t_eq r b (MAX: min_elt r b) :
  r⁺ ⨾⦗eq b⦘ <--> ∅₂.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma seq_min_rt_eq r b (MAX: min_elt r b) :
  r＊ ⨾⦗eq b⦘ <--> ⦗eq b⦘.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma seq_min_r_eq r b (MAX: min_elt r b) :
  r^? ⨾⦗eq b⦘ <--> ⦗eq b⦘.
Proof.
  lift_min_elt1; hkat'.
Qed.

Lemma seq_min_singl r a b (MAX: min_elt r a) :
  r ⨾ singl_rel a b <--> ∅₂.
Proof.
  lift_min_elt2; hkat'.
Qed.

Lemma seq_min_t_singl r a b (MAX: min_elt r a) :
  r⁺ ⨾ singl_rel a b <--> ∅₂.
Proof.
  lift_min_elt2; hkat'.
Qed.

Lemma seq_min_rt_singl r a b (MAX: min_elt r a) :
  r＊ ⨾ singl_rel a b <--> singl_rel a b.
Proof.
  lift_min_elt2; hkat'.
Qed.

Lemma seq_min_r_singl r a b (MAX: min_elt r a) :
  r^? ⨾ singl_rel a b <--> singl_rel a b.
Proof.
  lift_min_elt2; hkat'.
Qed.

Lemma min_elt_test r: r ;; ⦗min_elt r⦘ ⊆ bot.
Proof. basic_solver. Qed.

Lemma seq_eqv_min r : 
  r ⨾ ⦗min_elt r⦘ <--> ∅₂.
Proof.
  pose (@min_elt_test r); hkat'.
Qed.

Lemma seq_t_eqv_minasd  r :
  r⁺ ⨾ ⦗min_elt r⦘ <--> ∅₂.
Proof.
  pose (@min_elt_test r); hkat'.
Qed.

Lemma seq_rt_eqv_min r :
  r＊ ⨾ ⦗min_elt r⦘ <--> ⦗min_elt r⦘.
Proof.
  pose (@min_elt_test r); hkat'.
Qed.

Lemma seq_r_eqv_min r :
  r^? ⨾ ⦗min_elt r⦘ <--> ⦗min_elt r⦘.
Proof.
  pose (@min_elt_test r); hkat'.
Qed.

(* Require Import RelationAlgebra.kat. *)

(* FAIL I can't use [dual min_elt_test_dual] *)
Lemma min_elt_test_dual r: ⦗min_elt r⦘ ⨾ r⁻¹ ⊆ ∅₂.
Proof.
  basic_solver.
Qed.

Lemma seq_eqv_min_transp r : 
  ⦗min_elt r⦘ ⨾ r⁻¹  <--> ∅₂.
Proof.
  pose (@min_elt_test_dual r); hkat'.
Qed.

Lemma seq_eqv_min_transp_t r :
  ⦗min_elt r⦘ ⨾ (r⁻¹)⁺ <--> ∅₂.
Proof.
  pose (@min_elt_test_dual r); hkat'.
Qed.

Lemma seq_eqv_min_transp_rt r :
  ⦗min_elt r⦘ ⨾ (r⁻¹)＊  <--> ⦗min_elt r⦘.
Proof.
  pose (@min_elt_test_dual r); hkat'.
Qed.

Lemma seq_eqv_min_transp_r r :
  ⦗min_elt r⦘ ⨾ (r⁻¹)^?  <--> ⦗min_elt r⦘.
Proof.
  pose (@min_elt_test_dual r); hkat'.
Qed.

Lemma seq_wmin r r' b
      (MAX: wmin_elt r b) (D: forall x y, r' x y -> x = b) :
    r⨾ r' ⊆ r'.
Proof.
  unfold seq; red; ins; desf; eauto.
  specialize (D _ _ H0); desf; apply MAX in H; desf.
Qed.

Lemma seq_wmin_t r r' b
      (MAX: wmin_elt r b) (D: forall x y, r' x y -> x = b) :
  r ⁺⨾ r' ⊆ r'.
Proof.
  eauto using seq_wmin with hahn.
Qed.

Lemma seq_wmin_rt r r' b
      (MAX: wmin_elt r b) (COD: forall x y, r' x y -> x = b) :
  r ＊⨾ r' <--> r'.
Proof.
  rewrite rtE; split; relsf; rewrite seq_wmin_t; relsf.
Qed.

Lemma seq_wmin_r r r' b
      (MAX: wmin_elt r b) (COD: forall x y, r' x y -> x = b) :
  r ^?⨾ r' <--> r'.
Proof.
  rewrite crE; split; relsf; rewrite seq_wmin; relsf.
Qed.

Lemma seq_wmin_eq r b (MAX: wmin_elt r b) :
  r ⨾ ⦗eq b⦘ ⊆ ⦗eq b⦘.
Proof.
  eapply seq_wmin; unfold eqv_rel; ins; desf.
Qed.

Lemma seq_wmin_t_eq r b (MAX: wmin_elt r b) :
  r ⁺ ⨾ ⦗eq b⦘ ⊆ ⦗eq b⦘.
Proof.
  eauto using seq_wmin_eq with hahn.
Qed.

Lemma seq_wmin_rt_eq r b (MAX: wmin_elt r b) :
  r ＊ ⨾ ⦗eq b⦘ <--> ⦗eq b⦘.
Proof.
  rewrite rtE; split; relsf; rewrite seq_wmin_t_eq; relsf.
Qed.

Lemma seq_wmin_r_eq r b (MAX: wmin_elt r b) :
  r ^? ⨾ ⦗eq b⦘ <--> ⦗eq b⦘.
Proof.
  rewrite crE; split; relsf; rewrite seq_wmin_eq; relsf.
Qed.

Lemma seq_wmin_singl r a b (MAX: wmin_elt r a) :
  r ⨾ singl_rel a b ⊆ singl_rel a b.
Proof.
  unfold singl_rel, seq; red; ins; desf; eauto.
  apply MAX in H; desf.
Qed.

Lemma seq_wmin_t_singl r a b (MAX: wmin_elt r a) :
  r ⁺ ⨾ singl_rel a b ⊆ singl_rel a b.
Proof.
  eauto using seq_wmin_singl with hahn.
Qed.

Lemma seq_wmin_rt_singl r a b (MAX: wmin_elt r a) :
  r ＊ ⨾ singl_rel a b <--> singl_rel a b.
Proof.
  rewrite rtE; split; relsf; rewrite seq_wmin_t_singl; relsf.
Qed.

Lemma seq_wmin_r_singl r a b (MAX: wmin_elt r a) :
  r ^? ⨾ singl_rel a b <--> singl_rel a b.
Proof.
  rewrite crE; split; relsf; rewrite seq_wmin_singl; relsf.
Qed.

End MoreProperties.

Hint Unfold min_elt wmin_elt : unfolderDb.

Require Import Morphisms.

Instance min_elt_Proper A : Proper (inclusion --> set_subset) _ := set_subset_min_elt (A:=A).
Instance wmin_elt_Proper A : Proper (inclusion --> set_subset) _ := set_subset_wmin_elt (A:=A).
Instance min_elt_Propere A : Proper (same_relation ==> set_equiv) _ := set_equiv_min_elt (A:=A).
Instance wmin_elt_Propere A : Proper (same_relation ==> set_equiv) _ := set_equiv_wmin_elt (A:=A).

Add Parametric Morphism A : (@min_elt A) with signature
  inclusion --> eq ==> Basics.impl as min_elt_mori.
Proof.
  unfold inclusion, min_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@wmin_elt A) with signature
  inclusion --> eq ==> Basics.impl as wmin_elt_mori.
Proof.
  unfold inclusion, wmin_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@min_elt A) with signature
  same_relation --> eq ==> iff as min_elt_more.
Proof.
  unfold same_relation, inclusion, min_elt; firstorder.
Qed.

Add Parametric Morphism A : (@wmin_elt A) with signature
  same_relation --> eq ==> iff as wmin_elt_more.
Proof.
  unfold same_relation, inclusion, wmin_elt; firstorder.
Qed.

