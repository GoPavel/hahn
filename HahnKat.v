(** * Define KAT instance and canonical stractures *)

Add LoadPath "../relation-algebra-1.7.1".
Require Import RelationAlgebra.kat_tac.
Require Import RelationAlgebra.lattice.
Require Import RelationAlgebra.monoid.
Require Import RelationAlgebra.prop.
Require Import RelationAlgebra.kat.

Require Import HahnRelationsBasic.

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
  unfold inj', union, is_true, inter_rel, seq, same_relation, inclusion; simpl.

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

Definition same_rel_iff_weq: same_relation r1 r2 <-> r1 ≡ r2.
Proof. simpl. unfold same_relation. firstorder. Qed.

Definition inclusion_iff_leq: r1 ⊆ r2 <-> r1 ≦ r2.
Proof. simpl. firstorder. Qed.

Definition inter_rel_iff_cap: inter_rel r1 r2 = cap r1 r2.
Proof. reflexivity. Qed.

Definition union_rel_iff_cup: union r1 r2 = cup r1 r2.
Proof. reflexivity. Qed.

(* Definition lift_clos_refl: forall {x y: A}, r^? x y <-> (refl_top ⊔ r) x y. *)
(* Proof. *)
(*   intros. unfold clos_refl. simpl. split; intro; destruct H; vauto. *)
(*   destruct H. now left. *)
(* Qed. (* TODO: redefine refl_top *) *)

Definition clos_refl_trans_iff_str: clos_refl_trans r = @str _ tt r.
Proof. reflexivity. Qed.

Definition dom_iff_test: forall (dom: A -> Prop), ⦗dom⦘ = inj (n:=tt) dom.
Proof. reflexivity. Qed.

End Lifting.

Ltac lift_to_kat := repeat rewrite -> same_rel_iff_weq;
                    repeat rewrite -> inclusion_iff_leq;
                    repeat rewrite -> inter_rel_iff_cap;
                    repeat rewrite -> union_rel_iff_cup;
                    repeat rewrite -> clos_refl_trans_iff_str;
                    (* repeat rewrite -> lift_clos_refl. *)
                    repeat rewrite -> dom_iff_test;
                    idtac.
(* Ltac kat :=  *)
(*   intros; rewrite ?leq_iff_cup;  *)
(*     (apply catch_kat_weq || fail "could not find a KAT structure");  *)
(*     pre_dec true. *)

Ltac kat' :=
  lift_to_kat;
  intros; rewrite ?leq_iff_cup;
    (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
    pre_dec true.

Section Testing.

Variable A : Type.
Variables r r': relation A.

Goal forall `{r: relation A}, r ≡ r.
Proof. intro. kat'. Qed.

Goal r ⊆ r＊.
Proof. kat'. Qed.

(* Ltac hkat := *)
(*   intros; aggregate_hoare_hypotheses; rewrite ?leq_iff_cup;  *)
(*   (apply catch_kat_weq || fail "could not find a KAT structure");  *)
(*   let L := fresh "L" in intro L; *)
(*   let u := fresh "u" in  *)
(*   ((ra_get_kat_alphabet; intro u;  *)
(*     eapply (elim_hoare_hypotheses_weq (u^* ) (u^* )); [eassumption|]) *)
(*   || fail "typed hkat is not supported yet");  *)
(*   subst u; revert L; pre_dec true. *)

(** ** inclusion_eqv_rt
   Lemma inclusion_eqv_rt : ⦗dom⦘ ⊆ r'＊.
   Proof. by unfold eqv_rel, inclusion; ins; desf; vauto. Qed.
 *)
Goal forall (dom: A -> Prop), ⦗dom⦘ ⊆ r'＊.
Proof. intro. kat'. Qed.

Import RelationAlgebra.kat_reification.

Ltac hkat' :=
  lift_to_kat;
  intros; aggregate_hoare_hypotheses; rewrite ?leq_iff_cup;
  (apply (catch_kat_weq tt tt) || fail "could not find a KAT structure");
  let L := fresh "L" in intro L;
  let u := fresh "u" in
  ((ra_get_kat_alphabet; intro u;
    eapply (elim_hoare_hypotheses_weq (u^* ) (u^* )); [eassumption|])
  || fail "typed hkat is not supported yet");
  subst u; revert L; pre_dec true.

(** ** inclusion_r_rt
Lemma inclusion_r_rt' : r ⊆ r' -> (union (@one _ tt) r) ⊆ r'＊.
Proof. Abort. (* That type of hypotheses is not supported *)
 *)

Goal r ⊆ bot -> r ⊆ r'.
Proof. hkat'. Qed.

End Testing.
