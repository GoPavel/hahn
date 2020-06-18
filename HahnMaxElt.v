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

Local Lemma sym A: forall (x y: A), x = y <-> y = x.
Proof. firstorder. Qed.

Lemma max_elt_iff_kat (A: Type) (a: A) r:
  max_elt r a <-> ⦗eq a⦘ ;; r ⊆ ∅₂.
Proof.
  unfold_all; unfold max_elt; firstorder.
  - eapply H. rewrite H2, H0. apply H1.
  - eapply H. esplits; eauto.
Qed.

Lemma wmax_elt_iff_kat (A: Type) (a: A) r:
    wmax_elt r a <-> ⦗eq a⦘ ;; r ;; ⦗set_compl (eq a)⦘ ⊆ ∅₂.
Proof.
  unfold_all; unfold wmax_elt; firstorder.
  - apply H4. apply H. congruence.
  - assert (a <> b -> False).
    { intro; eapply H; esplits; eauto. }
    destruct (classic (a = b)).
    + assumption.
    + apply H0 in H1. destruct H1.
Qed.

Hint Rewrite max_elt_iff_kat wmax_elt_iff_kat: redefDb.

Section BasicProperties.

Variable A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma set_subset_max_elt (S: r' ⊆ r) : max_elt r ⊆₁ max_elt r'.
Proof. unfold max_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_subset_wmax_elt (S: r' ⊆ r) : wmax_elt r ⊆₁ wmax_elt r'.
Proof. unfold wmax_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_max_elt (S: r ≡ r') : max_elt r ≡₁ max_elt r'.
Proof. unfold max_elt, same_relation, set_equiv, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_wmax_elt (S: r ≡ r') : wmax_elt r ≡₁ wmax_elt r'.
Proof. unfold wmax_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma max_elt_weaken : max_elt r a -> wmax_elt r a.
Proof. hkat'. Qed.

Lemma max_elt_union : max_elt r a -> max_elt r' a -> max_elt (r +++ r') a.
Proof. hkat'. Qed.

Lemma wmax_elt_union : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r +++ r') a.
Proof. hkat'. Qed.

Lemma max_elt_t : max_elt r a -> max_elt (r⁺) a.
Proof. hkat'. Qed.

Lemma wmax_elt_rt : wmax_elt r a -> wmax_elt (r＊) a.
Proof. hkat'. Qed.

Lemma wmax_elt_t : wmax_elt r a -> wmax_elt (r⁺) a.
Proof. hkat'. Qed.

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
Proof. hkat'. Qed.

Lemma max_elt_seq1 : max_elt r a -> max_elt (r ⨾ r') a.
Proof. hkat'. Qed.

Lemma wmax_elt_seq2 : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r ⨾ r') a.
Proof. hkat'. Qed.

Lemma wmax_elt_seq1 : max_elt r a -> wmax_elt (r ⨾ r') a.
Proof. hkat'. Qed.

Lemma max_elt_seq2 : wmax_elt r a -> max_elt r' a -> max_elt (r ⨾ r') a.
Proof. hkat'. Qed.

End BasicProperties.

Hint Immediate max_elt_weaken : hahn.
Hint Resolve wmax_elt_union max_elt_union : hahn.
Hint Resolve wmax_elt_t wmax_elt_r wmax_elt_rt max_elt_t : hahn.
Hint Resolve max_elt_restr_eq wmax_elt_restr_eq : hahn.
Hint Resolve max_elt_seq1 max_elt_seq2 wmax_elt_seq1 wmax_elt_seq2 : hahn.

Section MoreProperties.

Variable A : Type.
Implicit Type r : relation A.

Lemma cod_iff_kat r b:
  (forall x y, r x y -> y = b) <-> r ;; ⦗set_compl (eq b)⦘ ⊆ ∅₂.
Proof.
  unfold_all; firstorder.
  destruct (classic (y = b)); try assumption.
  exfalso; eapply H; esplits; eauto.
Qed.

Hint Rewrite cod_iff_kat: redefDb.

Lemma seq_max r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r' ≡ ∅₂.
Proof. hkat'. Qed.

Lemma seq_max_t r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ⁺ ≡ ∅₂.
Proof. hkat'. Qed.

Lemma seq_max_rt r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r'＊ ≡ r.
Proof. hkat'. Qed.

Lemma seq_max_r r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r'^? ≡ r.
Proof. hkat'. Qed.

Lemma seq_eq_max r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r ≡ ∅₂.
Proof. hkat'. Qed.

Lemma seq_eq_max_t r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r⁺ ≡ ∅₂.
Proof. hkat'. Qed.

Lemma seq_eq_max_rt r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r＊ ≡ ⦗eq b⦘.
Proof. hkat'. Qed.

Lemma seq_eq_max_r r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r^? ≡ ⦗eq b⦘.
Proof. hkat'. Qed.

Lemma seq_singl_max r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r ≡ ∅₂.
Proof. hkat'. Qed.

Lemma seq_singl_max_t r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r⁺ ≡ ∅₂.
Proof. hkat'. Qed.

Lemma seq_singl_max_rt r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r＊ ≡ singl_rel a b.
Proof. hkat'. Qed.

Lemma seq_singl_max_r r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r^? ≡ singl_rel a b.
Proof. hkat'. Qed.

Lemma max_elt_test r: ⦗max_elt r⦘ ;; r ⊆ ∅₂.
Proof. basic_solver. Qed.

Lemma seq_eqv_max r : 
  ⦗max_elt r⦘ ⨾ r ≡ (∅₂).
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma seq_eqv_max_t r :
  ⦗max_elt r⦘ ⨾ r⁺ ≡ (∅₂).
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma seq_eqv_max_rt r :
  ⦗max_elt r⦘ ⨾ r＊ ≡ ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma seq_eqv_max_r r :
  ⦗max_elt r⦘ ⨾ r^? ≡ ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test r). hkat'.
Qed.

Lemma max_elt_test_dual r: r⁻¹ ⨾ ⦗max_elt r⦘ ⊆ (∅₂).
Proof.
  basic_solver.
Qed.

Lemma transp_seq_eqv_max r : 
  r⁻¹ ⨾ ⦗max_elt r⦘ ≡ (∅₂).
Proof.
  pose (@max_elt_test_dual r). hkat'.
Qed.

Lemma transp_seq_eqv_max_t r :
  (r⁻¹)⁺ ⨾ ⦗max_elt r⦘ ≡ (∅₂).
Proof.
  pose (@max_elt_test_dual r); hkat'.
Qed.

Lemma transp_seq_eqv_max_rt r :
  (r⁻¹)＊ ⨾ ⦗max_elt r⦘  ≡ ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test_dual r); hkat'.
Qed.

Lemma transp_seq_eqv_max_r r :
  (r⁻¹)^? ⨾ ⦗max_elt r⦘ ≡ ⦗max_elt r⦘.
Proof.
  pose (@max_elt_test_dual r); hkat'.
Qed.

Lemma seq_wmax r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
    r⨾ r' ⊆ r.
Proof.
  unfold seq; red; ins; desf; eauto.
  specialize (COD _ _ H); desf; apply MAX in H0; desf.
Qed.

Lemma seq_wmax_t r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ⁺ ⊆ r.
Proof.
  eauto using seq_wmax with hahn.
Qed.

Lemma seq_wmax_rt r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ＊ ≡ r.
Proof.
  rewrite rtE; split; relsf; rewrite seq_wmax_t; relsf.
Qed.

Lemma seq_wmax_r r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ^? ≡ r.
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
  ⦗eq b⦘⨾ r ＊ ≡ ⦗eq b⦘.
Proof.
  rewrite rtE; split; relsf; rewrite seq_eq_wmax_t; relsf.
Qed.

Lemma seq_eq_wmax_r r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ^? ≡ ⦗eq b⦘.
Proof.
  rewrite crE; split; relsf; rewrite seq_eq_wmax; relsf.
Qed.

Lemma seq_singl_wmax r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ⊆ singl_rel a b.
Proof.
  unfold singl_rel, seq; red; ins; desf; eauto.
  apply MAX in H0; desf.
Qed.

Lemma seq_singl_wmax_t r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ⁺ ⊆ singl_rel a b.
Proof.
  eauto using seq_singl_wmax with hahn.
Qed.

Lemma seq_singl_wmax_rt r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ＊ ≡ singl_rel a b.
Proof.
  rewrite rtE; split; relsf; rewrite seq_singl_wmax_t; relsf.
Qed.

Lemma seq_singl_wmax_r r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ^? ≡ singl_rel a b.
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

