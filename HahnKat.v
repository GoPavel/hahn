(******************************************************************************)
(** * Define KAT instance and canonical structures *)
(******************************************************************************)

Require Import RelationAlgebra.kat_tac.
Require Import RelationAlgebra.lattice.
Require Import RelationAlgebra.monoid.
Require Import RelationAlgebra.kat.

Require Import HahnSets HahnRelationsBasicDef HahnBase.

(* Fix unnecessary simplification, that RelationAlgebra brought *)
Require Export Setoid Morphisms.
Arguments Proper {_} _ _ : simpl never.
Arguments respectful {_ _} _ _ _ _: simpl never.

Set Implicit Arguments.

Definition refl_top {A: Type}: relation A := fun x y => x = y.
Definition top_rel {A: Type}: relation A := fun x y => True.
Definition bot_rel {A: Type}: relation A := ∅₂.

Hint Unfold refl_top top_rel bot_rel : unfolderDb.

Arguments union {A}.
Arguments inter_rel {A}.

(* utility for get first-order proposition  *)
Ltac unfold_all := repeat (autounfold with unfolderDb; simpl).

Canonical Structure rel_lattice_ops {A: Type}: lattice.ops :=
  {| car := relation A;
     leq := inclusion;
     weq := same_relation;
     cup := union;
     cap := inter_rel;
     neg := assert_false (fun a => a);
     bot := bot_rel;
     top := top_rel;
  |}.

Instance rel_lattice_laws {A: Type}:
  lattice.laws (BDL+CKA) (@rel_lattice_ops A).
Proof.
  apply lattice.Build_laws; simpl; (discriminate_levels || firstorder).
Qed.

Canonical Structure rel_monoid_ops {A: Type}: monoid.ops :=
  {| ob := unit;
     mor n m := @rel_lattice_ops A;
     dot n m p := @seq A;
     one n := refl_top;
     itr n := @clos_trans A;
     str n := @clos_refl_trans A;
     cnv n m := @transp A;
     ldv n m p := assert_false (fun _ a => a);
     rdv n m p := assert_false (fun _ a => a);
  |}.

Local Lemma clos_refl_transE {A: Type} {r: relation A} a b :  r＊ a b <-> a = b \/ r⁺ a b.
Proof.
  split; ins; desf; vauto; induction H; desf; vauto.
Qed.

Instance rel_monoid_laws {A: Type}: monoid.laws (BDL+CKA) (@rel_monoid_ops A).
Proof.
  apply monoid.Build_laws; simpl; try (discriminate_levels || firstorder);
    unfold_all; intros.
  - apply lower_lattice_laws.
  - firstorder. rewrite H; assumption.
  - rewrite H0. apply rt_refl.
  - destruct H0 as [z [H1 H2]]. apply rt_trans with (y:=z).
    + apply rt_step; assumption.
    + assumption.
  - destruct H1 as [z1 [H1 H2]]; rewrite clos_refl_transE in H1; destruct H1.
    + rewrite H1; apply H2.
    + apply H0; induction H1.
      * exists y0. split; assumption.
      * apply IHclos_trans1; apply H0; apply IHclos_trans2; apply H2.
  - firstorder. apply clos_trans_tn1 in H0; induction H0.
    + exists y; split; [> apply H0 | apply rt_refl].
    + destruct IHclos_trans_n1 as [z0 [H2 H3]].
      destruct H1; (exists z0; split; try assumption); eapply rt_trans; eauto using rt_step.
    + rewrite clos_refl_transE in H1. destruct H1.
      * rewrite <- H1. constructor; apply H0.
      * eauto using clos_trans.
Qed.

Definition dset {A: Type} := A -> Prop.

Canonical Structure dset_ops {A: Type}: lattice.ops :=
  {| car := @dset A;
     leq := @set_subset A;
     weq := @set_equiv A;
     cup := @set_union A;
     cap := @set_inter A;
     neg := @set_compl A;
     top := @set_full A;
     bot := @set_empty A;
  |}.


Hint Unfold dset : unfolderDb.

Instance dset_lattice_laws {A: Type}: lattice.laws BL (@dset_ops A).
Proof.
  constructor; try (unfold_all; firstorder).
  exact (classic (x x0)).
Qed.

Canonical Structure rel_kat_ops {A: Type}: kat.ops :=
  {| kat.kar := @rel_monoid_ops A;
     kat.tst n := @dset_ops A;
     kat.inj n := @eqv_rel A;
  |}.

Instance rel_kat_laws {A: Type}: kat.laws (@rel_kat_ops A).
Proof.
  constructor; simpl; intros.
  - apply lower_laws.
  - exact dset_lattice_laws.
  - constructor; try discriminate; unfold_all; firstorder.
  - unfold_all; firstorder.
  - unfold_all.
    firstorder; rewrite H0 in *; rewrite <- H in *; trivial.
Qed.

(* Notation for debug *)
Notation " [ p ]ₖₐₜ " := (inj (n:=tt) p).
Notation "a ;;ₖₐₜ b" := (monoid.dot tt tt tt a b) (left associativity, at level 25).
Notation "a ≦ₖₐₜ b" := (lattice.leq a b) (at level 79).
Notation "a ≡ₖₐₜ b" := (lattice.weq a b) (at level 79).
Notation "!ₖₐₜ x" := (neg x) (right associativity, at level 20, format "!ₖₐₜ x").
Notation "a ⊔ₖₐₜ b" := (lattice.cup a b) (left associativity, at level 50).
Notation "a ⊓ₖₐₜ b" := (lattice.cap a b) (left associativity, at level 40).
Notation "1ₖₐₜ" := (refl_top).
Notation "0ₖₐₜ" := (bot).
Notation "itrₖₐₜ x" := (itr tt x) (left associativity, at level 5, format "itrₖₐₜ x").
Notation "strₖₐₜ x" := (str tt x) (left associativity, at level 5, format "strₖₐₜ x").

(******************************************************************************)
(** Lemmas for lifting basic definitions to KAT *)
(******************************************************************************)
Section Lifting.

Variable A : Type.
Variables r r1 r2: relation A.
Variable d d1 d2: @dset A.
Local Notation " [ p ] " := (inj (n:=tt) p): ra_terms.

Lemma same_rel_iff_weq: same_relation r1 r2 <-> r1 ≡ r2.
Proof. reflexivity. Qed.

Lemma iff_rel_iff_weq: (forall x y, r1 x y <-> r2 x y) <-> r1 ≡ r2.
Proof. unfold_all. firstorder. Qed.

Lemma inclusion_iff_leq: r1 ⊆ r2 <-> r1 ≦ r2.
Proof. reflexivity.  Qed.

Lemma impl_rel_iff_leq: (forall x y, r1 x y -> r2 x y) <-> r1 ≦ r2.
Proof. unfold_all. firstorder. Qed.

Lemma inter_rel_iff_cap: inter_rel r1 r2 = cap r1 r2.
Proof. reflexivity. Qed.

Lemma union_rel_iff_cup: union r1 r2 = cup r1 r2.
Proof. reflexivity. Qed.

Lemma empty_rel_iff_bot: (∅₂ : relation A) = @bot (mor tt tt).
Proof. reflexivity. Qed.

Lemma clos_refl_trans_iff_str: clos_refl_trans r = @str _ tt r.
Proof. reflexivity. Qed.

Lemma clos_trans_iff_itr: clos_trans r = @itr _ tt r.
Proof. reflexivity. Qed.

Lemma seq_iff_dot: r1 ;; r2 = @dot _ tt tt tt r1 r2.
Proof. reflexivity. Qed.

Lemma transp_iff_cnv: transp r = @cnv _ tt tt r.
Proof. reflexivity. Qed.

Lemma dom_iff_test: forall (dom: A -> Prop), ⦗dom⦘ = [dom].
Proof. reflexivity. Qed.

(* NOTE: We assume that relation is decidable *)
Local Axiom prop_ext: forall (P Q: Prop), (P <-> Q) -> P = Q.

Ltac rel_ext :=
  apply functional_extensionality; intro x;
  apply functional_extensionality; intro y;
  apply prop_ext.

Lemma restr_rel_iff_kat: restr_rel d r = ([d]⋅r⋅[d]).
Proof. rel_ext; unfold_all; firstorder; congruence. Qed.

Lemma lift_clos_refl: r^? = (refl_top ⊔ r).
Proof. unfold_all; reflexivity. Qed.

Lemma set_empty_iff_kat: @set_empty A = @bot dset_ops.
Proof. reflexivity. Qed.

Lemma set_subset_iff_kat: d1 ⊆₁ d2 = leq d1 d2.
Proof. reflexivity. Qed.

Lemma set_equiv_iff_kat: d1 ≡₁ d2 = weq d1 d2.
Proof. reflexivity. Qed.

Lemma set_union_iff_kat: @set_union A = cup.
Proof. reflexivity. Qed.

Lemma set_inter_iff_kat: @set_inter A = cap.
Proof. reflexivity. Qed.

Lemma set_subset_iff_kat: @set_subset A = leq.
Proof. reflexivity. Qed.

Lemma set_equiv_iff_kat: @set_equiv A = weq.
Proof. rel_ext. firstorder. Qed.

Lemma reflexive_iff_kat: reflexive r <-> refl_top ≦ r.
Proof.
  unfold_all; firstorder.
  rewrite H0; apply H.
Qed.

Lemma transitive_iff_kat: transitive r <-> (@dot _ tt tt tt) r r ≦ r.
Proof. unfold_all; firstorder. Qed.

Lemma upward_closed_iff_kat: upward_closed r d <-> [@neg dset_ops d]⋅r⋅[d] ≦ bot.
Proof.
  unfold_all. firstorder.
  - eapply H4, H; [> rewrite H0; apply H3 | assumption].
  - specialize (H x y).
    assert (not (d x) -> False). { intro; apply H; exists y. esplits; auto. }
    destruct (classic (d x)); [> assumption | apply H0 in H1; destruct H1].
Qed.

(** not supported by KAT *)

Lemma singl_rel_iff_kat: forall {a b: A}, singl_rel a b = [eq a]⋅top⋅[eq b].
Proof.
  unfold_all; intros; rel_ext; firstorder.
  - esplits; eauto.
  - rewrite H1, H0; reflexivity.
Qed.

Lemma acyclic_iff_kat: acyclic r <-> 1 ⊓ (itr tt r) ≡ 0.
Proof.
  unfold_all; firstorder.
  apply H with (x:=x); rewrite H0 at 2; apply H1.
Qed.

Lemma irreflexive_iff_kat: irreflexive r <-> cap (one tt) r ≦ bot.
Proof.
  unfold_all; firstorder.
  rewrite H0 in H1; eapply H, H1.
Qed.

Lemma cross_rel_iff_kat: cross_rel d1 d2 = [d1]⋅top⋅[d2].
Proof.
  unfold_all; rel_ext; firstorder; [esplits; auto |congruence].
Qed.

End Lifting.

(* NOTE: We shouldn't rewrite general operation, we should relay on unification.
         But matching in (h)kat expected weq\leq operations *)
Hint Rewrite same_rel_iff_weq iff_rel_iff_weq inclusion_iff_leq impl_rel_iff_leq : redefDb.
Hint Rewrite inter_rel_iff_cap union_rel_iff_cup seq_iff_dot empty_rel_iff_bot
     clos_refl_trans_iff_str clos_trans_iff_itr lift_clos_refl dom_iff_test : redefDb.
Hint Rewrite restr_rel_iff_kat acyclic_iff_kat irreflexive_iff_kat cross_rel_iff_kat
     set_empty_iff_kat set_full_iff_kat set_compl_iff_kat set_union_iff_kat set_inter_iff_kat
     set_subset_iff_kat set_equiv_iff_kat singl_rel_iff_kat reflexive_iff_kat
     transitive_iff_kat upward_closed_iff_kat : redefDb.

Ltac lift_to_kat_all := repeat autorewrite with redefDb in *.

(******************************************************************************)
(** Redefine hkat/kat tactic *)
(******************************************************************************)

Import RelationAlgebra.kat_reification.

(* Support new hypothesis as combination of old *)
Lemma qapb_to_hoare `{L: laws} {n m} (a: tst n) (b: tst m) (p q: X n m): 
  q ≦ [a]⋅(p⋅[b])-> [!a]⋅q ≦ 0 /\ q⋅[!b] ≦ 0.
Proof. intro H. split; rewrite H; kat. Qed.

Ltac hahn_kat :=
  lift_to_kat_all;
  intros; rewrite ?leq_iff_cup;
    (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
    pre_dec true.

(* NOTE: matching reordered for speed up a bit *)
Ltac aggregate_hoare_hypotheses_fixed :=
  repeat
    match goal with
      | H: _ ≡ _ |- _ =>
        apply (ab_to_hoare (n:=tt)) in H ||
        (rewrite (cp_c (n:=tt) _ _ H); clear H) ||
        (rewrite (pc_c (n:=tt) _ _ H); clear H) ||
        (rewrite weq_spec in H; destruct H)
    end;
  repeat
    match goal with
      | H: _ ≦ 0,  H': _ ≦ 0 |- _     => fail
      | H: _ ≦ _ |- _ =>
        apply (ab'_to_hoare (n:=tt)) in H ||
        apply (bpqc_to_hoare (n:=tt) (m:=tt)) in H ||
        apply (pbcq_to_hoare (n:=tt) (m:=tt) ) in H ||
        (apply (qapb_to_hoare (n:=tt) (m:=tt) ) in H; destruct H) ||
        apply (qcp_to_hoare  (n:=tt) (m:=tt) ) in H ||
        apply (qpc_to_hoare  (n:=tt) (m:=tt) ) in H
    end;
  repeat
    match goal with
      | H: _ ≦ 0,  H': _ ≦ 0 |- _ =>
        apply (join_leq _ _ _ H') in H; clear H'
    end.

(* NOTE: bug with using pc_c cp_c fixed.
     There was an issue is [hkat] has waited for at least one hypothesis [r ≤ 0].
     And matching allows saving error message. *)
Ltac hahn_hkat :=
  lift_to_kat_all;
  intros; aggregate_hoare_hypotheses_fixed; rewrite ?leq_iff_cup;
  (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
  match goal with
    | H: _ ≦ 0 |- _    =>
      let L := fresh "L" in intro L;
      let u := fresh "u" in
      ((ra_get_kat_alphabet; intro u;
        eapply (elim_hoare_hypotheses_weq (u^*) (u^*)); [eassumption|])
                || fail "typed hkat is not supported yet");
        subst u; revert L; pre_dec true
    | _ => pre_dec true
  end.

