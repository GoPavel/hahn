(** * Define KAT instance and canonical stractures *)

Add LoadPath "../relation-algebra-1.7.1".
Require Import RelationAlgebra.kat_tac.
Require Import RelationAlgebra.lattice.
Require Import RelationAlgebra.monoid.
Require Import RelationAlgebra.prop.
Require Import RelationAlgebra.kat.

Require Import HahnRelationsBasic.

Require Import Coq.Logic.FunctionalExtensionality.

Set Printing Coercions.
Set Implicit Arguments.

Axiom LEM : forall (p: Prop), p \/ not p.

Instance Prop_lattice_laws: lattice.laws (BL+STR+CNV+DIV) Prop_lattice_ops.
Proof.
  constructor; (try apply Build_PreOrder); simpl;
    repeat intro; try (discriminate || tauto).
Qed.

Inductive refl_top {A: Type}: relation A :=
  mk_refl_top: forall (a: A), refl_top a a.

Canonical Structure rel_lattice_ops {A: Type}: lattice.ops :=
  {| car := relation A;
     (* leq := pwr (pwr impl); *)
     (* weq := pwr (pwr iff); *)
     (* cup := pw2 (pw2 or); *)
     (* cap := pw2 (pw2 and); *)
     (* neg := pw1 (pw1 not); *)
     (* bot := pw0 (pw0 False); *)
     (* top := pw0 (pw0 True) *)
     leq := leq;
     weq := weq;
     cup := cup;
     cap := cap;
     neg := neg;
     bot := bot;
     top := top
  |}.
(* Print Canonical Projections. *)

Instance rel_lattice_laws {A: Type}:
  lattice.laws (BL+STR+CNV+DIV) (@rel_lattice_ops A) := pw_laws  _.

Definition rel_monoid_ops {A: Type}: monoid.ops :=
  {| ob := unit;
     mor n m := @rel_lattice_ops A;
     dot n m p := @seq A;
     one n := refl_top;
     itr n := @clos_trans A;
     str n := @clos_refl_trans A;
     cnv n m := @transp A; (* TODO: not used *)
     ldv n m p := assert_false (fun _ a => a);
     rdv n m p := assert_false (fun _ a => a);
  |}.

Canonical Structure rel_monoid_ops.

Instance rel_monoid_laws {A: Type}: monoid.laws (BL+CKA) (@rel_monoid_ops A).
Proof.
  apply monoid.Build_laws; intros; simpl;
    try ((right; left; solve_lower) || (left; solve_lower) || right);
    try discriminate_levels;
    (firstorder || idtac).
    (* try (unfold transp, inter_rel, seq, inclusion; firstorder) *)
  - apply lower_lattice_laws.
  - destruct H; assumption.
  - now exists a.
  - inversion H0; apply rt_refl.
  - apply rt_trans with (y:=x0); [> apply rt_step; assumption | assumption].
  - simpl in H0. induction H1.
    + apply H0. exists y. split; assumption.
    + assumption.
    + apply IHclos_refl_trans1, IHclos_refl_trans2; assumption.
  - apply t_step_rt; assumption.
  - apply t_step_rt. exists x0. split; assumption.
Qed.

Definition eqv_rel' : forall {A: Type} {cond: A -> Prop}, relation A
  := fun _ (cond: _) x y =>  x = y /\ cond x.

Print Coercions.

(* Set Printing Universes. *)
(* Check fun (A: Type@{lattice.pw}) => ob (@rel_monoid_ops A). *)
Definition dset' {A: Type}: lattice.ops := pw_ops Prop_lattice_ops A.

Definition inj' {A: Type} (cond: (@dset' A)): relation A
  := fun x y => x = y /\ cond x.

Canonical Structure rel_kat_ops {A: Type}: kat.ops :=
  {| kat.kar := @rel_monoid_ops A;
     kat.tst n := @dset' A;
     kat.inj n := @inj' A
  |}.

Ltac unfold_all :=
  unfold eqv_rel, inj', union, is_true, inter_rel, seq, same_relation, inclusion; simpl.

Instance rel_kat_laws {A: Type}: kat.laws (@rel_kat_ops A).
Proof.
  assert (inj_leq: Proper (leq ==> leq) (@inj' A)). {
      intros x y XleY x0 y0 H. destruct H as [H0 H1].
      split; [>apply H0 |apply XleY, H1].
    }
  constructor; simpl; intros.
  - apply lower_laws.
  - apply (pw_laws (H:=lower_lattice_laws)).
  - constructor; try discriminate; intros; simpl; unfold_all; intros; try tauto.
    + destruct H0 as [H0 H1]. split; [> assumption | apply H; apply H1].
    + split; intros; inversion 0; split; try (now apply H) || assumption.
  - unfold_all. split; intros H.
    + destruct H as [H _]; rewrite H; constructor.
    + destruct H. constructor; constructor.
  - unfold_all. 
    split; intros.
    + exists a. now trivial.
    + destruct H as [z [[H1 H2] [H3 H4]]]. rewrite H1, H3 in *; easy.
Qed.

(* Definition coer: forall {A: Type}, (relation A) -> hrel A A *)
(*   := fun _ r x y => r x y. *)
(* Coercion coer: relation >-> hrel. *)
(* Definition coer': forall {A: Type}, hrel A A -> relation A *)
(*   := fun _ r x y => r x y. *)
(* Coercion coer': hrel >-> relation. *)

(* Check (fun (r: relation A) => let r r). *)

(* Definition rel_lattice_ops' {A: Type}: lattice.ops := *)
(*   {| car := relation A; *)
(*      leq := @inclusion A; *)
(*      weq := @same_relation A; *)
(*      cup := @union A; *)
(*      cap := @inter_rel A; *)
(*      neg := complement; *)
(*      bot := bot; *)
(*      top := top *)
(*   |}. *)
(* Canonical Structure rel_lattice_ops'. *)

Section Lifting.

Variable A : Type.
Variables r r1 r2: relation A.
Variable d d1 d2: A -> Prop.

Lemma same_rel_iff_weq: same_relation r1 r2 <-> r1 ≡ r2.
Proof. simpl. unfold same_relation. firstorder. Qed.

Lemma inclusion_iff_leq: r1 ⊆ r2 <-> r1 ≦ r2.
Proof. simpl. firstorder. Qed.

Lemma inter_rel_iff_cap: inter_rel r1 r2 = cap r1 r2.
Proof. reflexivity. Qed.

Lemma union_rel_iff_cup: union r1 r2 = cup r1 r2.
Proof. reflexivity. Qed.

Lemma clos_refl_trans_iff_str: clos_refl_trans r = @str _ tt r.
Proof. reflexivity. Qed.

Lemma close_trans_iff_itr: clos_trans r = @itr _ tt r.
Proof. reflexivity. Qed.

Local Notation " [ p ] " := (inj (n:=tt) p): ra_terms. 

Lemma dom_iff_test: forall (dom: A -> Prop), ⦗dom⦘ = [dom].
Proof. reflexivity. Qed.

(* ASK *)
Axiom prop_ext: forall (P Q: Prop), (P <-> Q) -> P = Q.

Ltac rel_ext :=
  apply functional_extensionality; intro x;
  apply functional_extensionality; intro y;
  apply prop_ext.

Lemma restr_rel_iff_kat: restr_rel d r = ([d]⋅r⋅[d]).
Proof.
  rel_ext.
  unfold restr_rel; simpl; unfold inj', seq; split.
  - intros [H1 [H2 H3]].
    exists y. split; try exists x; auto.
  - intros. destruct H as [z [[z0 [[H1 H2] H3]] [H4 H5]]].
    rewrite <- H1 in H3; rewrite -> H4 in *.
    split; [apply H3 | split; [apply H2 | apply H5]].
Qed.

Lemma lift_clos_refl: r^? = (refl_top ⊔ r).
Proof.
  rel_ext.
  intros. unfold clos_refl. simpl. split; intro; destruct H; try rewrite H in *; try auto.
  - left; constructor.
  - destruct H; left; reflexivity.
Qed. (* TODO: redefine refl_top *)


Notation "x ^+" := (itr tt x)   (left associativity, at level 5, format "x ^+"): ra_terms.

Lemma acyclic_iff_kat: acyclic r <-> 1 ⊓ (r^+) ≡ 0.
Proof.
  unfold acyclic, irreflexive; simpl.
  split; intros.
  - split.
    + intros [H1 H2]. inversion H1. rewrite H3 in *. apply H in H2; apply H2.
    + intros [].
  - apply (H x x). split; [constructor | assumption].
Qed.


Lemma irreflexive_iff_kat1: irreflexive r <-> r ⊆ @neg rel_lattice_ops (one tt).
Proof.
  unfold irreflexive. simpl. unfold pw1, inclusion. simpl. unfold not.
  split; intros.
  - destruct H1; apply H with (x:=a); assumption.
  - apply H with (x:=x) (y:=x). assumption. constructor.
Qed.

Lemma irreflexive_iff_kat2: irreflexive r <-> cap (one tt) r ⊆ bot.
Proof.
  unfold irreflexive. simpl. hnf. repeat (unfold pw2, pw0; simpl).
  unfold inclusion.
  firstorder.
  - inversion H0. apply H with (x:=x); rewrite -> H3 at 2; apply H1.
  - apply H with (x:=x)(y:=x). split; [> constructor | assumption ].
Qed.

Lemma cross_rel_iff_kat: cross_rel d1 d2 = [d1]⋅top⋅[d2].
Proof.
  rel_ext.
  unfold cross_rel.
  do 2 rewrite <- dom_iff_test.
  simpl. unfold seq, eqv_rel.
  split.
     - intros [H1 H2]. exists y. split. exists x. split; try auto. constructor. auto.
     - intros [z [[z0 [[H01 H02] H03]] [H1 H2]]].
       rewrite H01 in *. rewrite H1 in *.
       split; assumption.
Qed.

Import hahn.HahnSets.

Ltac pred_ext :=
  apply functional_extensionality; intro x;
  apply prop_ext.

Lemma set_empty_iff_kat: @set_empty A = bot.
Proof. reflexivity. Qed.

Lemma set_full_iff_kat: @set_full A = top.
Proof. reflexivity. Qed.

Lemma set_compl_iff_kat: @set_compl A = neg.
Proof. reflexivity. Qed.

Lemma set_union_iff_kat: @set_union A = cup.
Proof. reflexivity. Qed.

Lemma set_inter_iff_kat: @set_inter A = cap.
Proof. reflexivity. Qed.

Lemma set_subset_iff_kat: @set_subset A = leq.
Proof. reflexivity. Qed.

Lemma set_equiv_iff_kat: @set_equiv A = weq.
Proof. unfold set_equiv. unfold weq. simpl. unfold iff. unfold set_subset.
       rel_ext. firstorder. Qed.

Lemma singl_rel_iff_kat: forall (a b: A), singl_rel a b = [fun x => x = a]⋅top⋅[fun x => x = b].
Proof.
  simpl. unfold seq, singl_rel. unfold inj'. simpl.
  intros; rel_ext.
  split.
  - intros [H1 H2]. exists y. split; eauto.
  - intros [z [[z0 [[H3 H4] _]] [H1 H2]]]. rewrite H3, H4, H1, H2 in *. split; reflexivity.
Qed.

End Lifting.

Ltac lift_to_kat := repeat rewrite -> same_rel_iff_weq;
                    repeat rewrite -> inclusion_iff_leq;
                    repeat rewrite -> inter_rel_iff_cap;
                    repeat rewrite -> union_rel_iff_cup;
                    repeat rewrite -> clos_refl_trans_iff_str;
                    repeat rewrite -> close_trans_iff_itr;
                    repeat rewrite -> lift_clos_refl;
                    repeat rewrite -> dom_iff_test;
                    repeat rewrite -> restr_rel_iff_kat;
                    repeat rewrite -> acyclic_iff_kat;
                    repeat rewrite -> irreflexive_iff_kat2;
                    repeat rewrite -> cross_rel_iff_kat;
                    repeat rewrite -> set_empty_iff_kat;
                    repeat rewrite -> set_full_iff_kat;
                    repeat rewrite -> set_compl_iff_kat;
                    repeat rewrite -> set_union_iff_kat;
                    repeat rewrite -> set_inter_iff_kat;
                    repeat rewrite -> set_subset_iff_kat;
                    repeat rewrite -> set_equiv_iff_kat;
                    repeat rewrite -> singl_rel_iff_kat;
                    idtac.

Ltac lift_to_kat_all := repeat rewrite -> same_rel_iff_weq in *;
                        repeat rewrite -> inclusion_iff_leq in *;
                        repeat rewrite -> inter_rel_iff_cap in *;
                        repeat rewrite -> union_rel_iff_cup in *;
                        repeat rewrite -> clos_refl_trans_iff_str in *;
                        repeat rewrite -> close_trans_iff_itr in *;
                        repeat rewrite -> lift_clos_refl in *;
                        repeat rewrite -> dom_iff_test in *;
                        repeat rewrite -> restr_rel_iff_kat in *;
                        repeat rewrite -> acyclic_iff_kat in *;
                        repeat rewrite -> irreflexive_iff_kat2 in *;
                        repeat rewrite -> cross_rel_iff_kat in *;
                        repeat rewrite -> set_empty_iff_kat in *;
                        repeat rewrite -> set_full_iff_kat in *;
                        repeat rewrite -> set_compl_iff_kat in *;
                        repeat rewrite -> set_union_iff_kat in *;
                        repeat rewrite -> set_inter_iff_kat in *;
                        repeat rewrite -> set_subset_iff_kat in *;
                        repeat rewrite -> set_equiv_iff_kat in *;
                        repeat rewrite -> singl_rel_iff_kat in *;
                        idtac.

Require Import RelationAlgebra.kat_reification.

(* Ltac kat :=  *)
(*   intros; rewrite ?leq_iff_cup;  *)
(*     (apply catch_kat_weq || fail "could not find a KAT structure");  *)
(*     pre_dec true. *)

Ltac kat' :=
  lift_to_kat;
  intros; rewrite ?leq_iff_cup;
    (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
    pre_dec true.

(* Ltac hkat := *)
(*   intros; aggregate_hoare_hypotheses; rewrite ?leq_iff_cup;  *)
(*   (apply catch_kat_weq || fail "could not find a KAT structure");  *)
(*   let L := fresh "L" in intro L; *)
(*   let u := fresh "u" in  *)
(*   ((ra_get_kat_alphabet; intro u;  *)
(*     eapply (elim_hoare_hypotheses_weq (u^* ) (u^* )); [eassumption|]) *)
(*   || fail "typed hkat is not supported yet");  *)
(*   subst u; revert L; pre_dec true. *)

Ltac aggregate_hoare_hypotheses' :=
  repeat 
    match goal with
      | H: _ ≡ _ |- _ => 
        apply (ab_to_hoare (n:=tt)) in H || 
        (rewrite (cp_c _ _ H); clear H) || 
        (rewrite (pc_c _ _ H); clear H) || 
        apply weq_spec in H as [? ?]
    end;
  repeat
    match goal with
      | H: _ ≦ _ |- _ => 
        apply (ab'_to_hoare (n:=tt)) in H || 
        apply (bpqc_to_hoare (* (n:=tt) (m:=tt) *)) in H || 
        apply (pbcq_to_hoare (* (n:=tt) (m:=tt) *) ) in H || 
        apply (qcp_to_hoare  (* (n:=tt) (m:=tt) *) ) in H ||
        apply (qpc_to_hoare  (* (n:=tt) (m:=tt) *) ) in H
      | H: _ ≦ 0,  H': _ ≦ 0 |- _ => 
        apply (join_leq _ _ _ H') in H; clear H'
      | H: _ ≦ bot,  H': _ ≦ bot |- _ => 
        apply (join_leq _ _ _ H') in H; clear H'
    end.

Ltac aggregate_hoare_hypotheses'' :=
  repeat 
    match goal with
      | H: _ ≡ _ |- _ => 
        apply (ab_to_hoare (n:=tt)) in H || 
        (rewrite (cp_c _ _ H); clear H) || 
        (rewrite (pc_c _ _ H); clear H) || 
        apply weq_spec in H as [? ?]
    end;
  repeat
    match goal with
      | H: _ ≦ _ |- _ => 
        apply (ab'_to_hoare (n:=tt)) in H || 
        apply (bpqc_to_hoare (n:=tt) (m:=tt)) in H || 
        apply (pbcq_to_hoare (n:=tt) (m:=tt) ) in H || 
        apply (qcp_to_hoare  (n:=tt) (m:=tt) ) in H ||
        apply (qpc_to_hoare  (n:=tt) (m:=tt) ) in H
      | H: _ ≦ 0,  H': _ ≦ 0 |- _ => 
        apply (join_leq _ _ _ H') in H; clear H'
      | H: _ ≦ bot,  H': _ ≦ bot |- _ => 
        apply (join_leq _ _ _ H') in H; clear H'
    end.

Ltac hkat' :=
  lift_to_kat_all;
  intros; aggregate_hoare_hypotheses'; rewrite ?leq_iff_cup;
  (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
  let L := fresh "L" in intro L;
  let u := fresh "u" in
  ((ra_get_kat_alphabet; intro u;
    eapply (elim_hoare_hypotheses_weq (u^* ) (u^* )); [eassumption|])
  || fail "typed hkat is not supported yet");
  subst u; revert L; pre_dec true.


Ltac hkat'' :=
  lift_to_kat_all;
  intros; aggregate_hoare_hypotheses''; rewrite ?leq_iff_cup;
  (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
  let L := fresh "L" in intro L;
  let u := fresh "u" in
  ((ra_get_kat_alphabet; intro u;
    eapply (elim_hoare_hypotheses_weq (u^* ) (u^* )); [eassumption|])
  || fail "typed hkat is not supported yet");
  subst u; revert L; pre_dec true.


Section Testing.

Variable A : Type.
Variables r r': relation A.
Variables dom dom1 dom2: A -> Prop.

Goal forall `{r: relation A}, r ≡ r.
Proof. intro. kat'. Qed.

(* Notation "x ^+" := (itr tt x)   (left associativity, at level 5, format "x ^+"): ra_terms. *)

Locate "x ^+".
Locate "x ∩ y".
Locate "x ⁺".
Locate "x ^+".

Local Notation " [ p ] " := (inj (n:=tt) p): ra_terms.

Check @cap rel_lattice_ops (str tt r) r.
Check cap (str tt r) r.
Check (r ⊓ str tt r).

Goal  (r ⊓ (str tt r) ⊔ r) ≡ bot.
Proof.
  rewrite <- same_rel_iff_weq.
Abort.

Goal r⁺ ∩ (one tt) <--> bot.
Proof.
  lift_to_kat.
  (* rewrite -> acyclic_iff_kat. *)
Abort.

Goal @weq rel_lattice_ops ((one tt) ⊓ (str tt r)) bot.
Proof.
  rewrite <- same_rel_iff_weq.
Abort.

Goal r ⊆ r＊.
Proof. kat'. Qed.

(** ** inclusion_eqv_rt
   Lemma inclusion_eqv_rt : ⦗dom⦘ ⊆ r'＊.
   Proof. by unfold eqv_rel, inclusion; ins; desf; vauto. Qed.
 *)
Goal ⦗dom⦘ ⊆ r'＊.
Proof. kat'. Qed.


(** ** inclusion_r_rt
Lemma inclusion_r_rt' : r ⊆ r' -> (union (@one _ tt) r) ⊆ r'＊.
Proof. Abort. (* That type of hypotheses is not supported *)
 *)

Goal r ⊆ bot -> r ⊆ r'.
Proof. hkat'. Qed.

Lemma acyclic_restr d : acyclic r -> acyclic (restr_rel d r).
Proof. Abort.

Goal dom1 ≦ dom2 -> ⦗dom1⦘ ≦ ⦗dom2⦘.
Proof. hkat'. Qed.

Check ⦗dom2⦘.
Goal dom1 ≡ dom2 -> ⦗dom1⦘ <--> ⦗dom2⦘.
Proof. hkat'. Qed.

Goal dom2 ≦ dom1 -> ⦗dom1⦘ ⨾ ⦗dom2⦘ <--> ⦗dom2⦘.
Proof. lift_to_kat_all. hkat'. Qed.

(* Local Notation " [ p ] " := (inj (n:=tt) p): ra_terms. *)
(* Local Notation "x ⋅ y" := (@dot _ tt tt tt x y). *)
(* Local Notation dot' := (@dot _ tt tt tt). *)
Local Notation top := (@lattice.top rel_lattice_ops).

Goal top ;; ⦗dom1⦘;; (top;;⦗dom1⦘)＊ ≡ top ;; ⦗dom1⦘.
Proof. Fail kat'. Abort.

Implicit Type s : A -> Prop.
Lemma ct_of_cross s s' : (s × s')⁺ <--> s × s'.
Proof. lift_to_kat_all. Fail kat'. Abort.


End Testing.
