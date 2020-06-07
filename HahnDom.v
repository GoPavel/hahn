Require Import HahnBase HahnSets HahnRelationsBasic HahnEquational.
Require Import HahnRewrite.
Require Import Setoid.
Set Implicit Arguments.

(** * Calculating the (co)domain of a relation *)

Require Import HahnKat.

Section Domains.

Variable A B : Type.

Section Definitions.
  Variable r : relation A.
  Variable d : A -> Prop.
  Variables f g : A -> B.

  Definition doma := forall x y (REL: r x y), d x.
  Definition domb := forall x y (REL: r x y), d y.
  Definition eq_dom := forall x (DX: d x), f x = g x. 

  Definition dom_cond d := (fun e => dom_rel (r ⨾ ⦗ eq e ⦘) ⊆₁ d).
End Definitions.

Local Axiom LEM: forall (A: Type) (d : A -> Prop) (x: A), (d x) \/ (not (d x)). (* TODO *)

Lemma doma_iff_kat r d: doma r d <-> ⦗set_compl d⦘ ;; r ⊆ ∅₂.
Proof.
  unfold_all. unfold doma. firstorder.
  - eapply H2, H. rewrite H0; apply H1.
  - assert (not (d x) -> False).
    { intro. eapply H. esplits; eauto. }
    destruct (LEM d x).
    + assumption.
    + apply H0 in H1. destruct H1.
Qed.

Lemma domb_iff_kat r d: domb r d <-> (r ;; ⦗set_compl d⦘ ⊆ ∅₂).
Proof.
  unfold_all. unfold domb. split.
  - firstorder.
  - intros.
    assert (not (d y) -> False). { eauto. }
    destruct (LEM d y).
    + assumption.
    + apply H0 in H1. destruct H1.
Qed.

Hint Rewrite doma_iff_kat domb_iff_kat: redefDb.

Section Lemmas.

  Variables r r' : relation A.
  Variables f g : A -> B.
  Variables d d' : A -> Prop.

  Lemma eqv_doma : doma ⦗d⦘ d.
  Proof. kat'. Qed.

  Lemma eqv_domb : domb ⦗d⦘ d.
  Proof. kat'. Qed.

  Lemma seq_eqv_doma : doma r d -> doma (⦗d'⦘ ⨾ r) d.
  Proof. hkat'. Qed.

  Lemma seq_eqv_domb : domb r d -> domb (r ⨾ ⦗d'⦘) d.
  Proof. hkat'. Qed.

  Lemma restr_eq_rel_doma : doma r d -> doma (restr_eq_rel f r) d.
  Proof. unfold doma, restr_eq_rel; ins; desf; eauto. Qed.

  Lemma restr_eq_rel_domb : domb r d -> domb (restr_eq_rel f r) d.
  Proof. unfold domb, restr_eq_rel; ins; desf; eauto. Qed.

  Lemma seq_doma : doma r d -> doma (r ⨾ r') d.
  Proof. hkat'. Qed.

  Lemma seq_domb : domb r' d -> domb (r ⨾ r') d.
  Proof. hkat'. Qed.

  Lemma union_doma : doma r d -> doma r' d -> doma (r ∪ r') d.
  Proof. hkat'. Qed.

  Lemma union_domb : domb r d -> domb r' d -> domb (r ∪ r') d.
  Proof. hkat'. Qed.

  Lemma ct_doma : doma r d -> doma r⁺ d.
  Proof. hkat'. Qed.

  Lemma ct_domb : domb r d -> domb r⁺ d.
  Proof. hkat'. Qed.

  Lemma seq_r_doma : doma r d -> doma r' d -> doma (r^? ⨾ r') d.
  Proof. hkat'. Qed.

  Lemma seq_r_domb : domb r d -> domb r' d -> domb (r ⨾ r'^?) d.
  Proof. hkat'. Qed.

  Lemma minus_doma : doma r d -> doma (r \ r') d.
  Proof. unfold doma, minus_rel; ins; desf; eauto. Qed.

  Lemma minus_domb : domb r d -> domb (r \ r') d.
  Proof. unfold domb, minus_rel; ins; desf; eauto. Qed.

  Lemma doma_inter_r : doma r (d ∩₁ d') <-> doma r d /\ doma r d'.
  Proof.
    split; [> intro; split | intros [H1 H2]].
    all: hkat'.
  Qed.

  Lemma domb_inter_r : domb r (d ∩₁ d') <-> domb r d /\ domb r d'.
  Proof.
    split; [> intro; split | intros [H1 H2]].
    all: hkat'.
  Qed.

  Lemma restr_doma : doma (restr_rel d r) d.
  Proof. kat'. Qed.

  Lemma restr_domb : domb (restr_rel d r) d.
  Proof. kat'. Qed.

  Lemma restr_doma_mon : doma r d -> doma (restr_rel d' r) d.
  Proof. hkat'. Qed.

  Lemma restr_domb_mon : domb r d -> domb (restr_rel d' r) d.
  Proof. hkat'. Qed.

  Lemma dom_empty : dom_rel (A:=A) ∅₂ ≡₁ ∅.
  Proof. unfolder; split; ins; desf. Qed. 

  Lemma codom_empty : codom_rel (A:=A) ∅₂ ≡₁ ∅.
  Proof. unfolder; split; ins; desf. Qed. 

  Lemma codom_seq : codom_rel (r ⨾ r') ⊆₁ codom_rel r'.
  Proof. unfold codom_rel, seq, set_subset.
         ins; desf; eauto. Qed.

  Lemma dom_union : dom_rel (r ∪ r') ≡₁ dom_rel r ∪₁ dom_rel r'.
  Proof. unfold dom_rel, union, set_union, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma codom_union : codom_rel (r ∪ r') ≡₁ codom_rel r ∪₁ codom_rel r'.
  Proof. unfold codom_rel, union, set_union, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma dom_eqv : dom_rel ⦗d⦘ ≡₁ d.
  Proof. unfold dom_rel, eqv_rel, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma codom_eqv : codom_rel ⦗d⦘ ≡₁ d.
  Proof. unfold codom_rel, eqv_rel, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma dom_eqv1 : dom_rel (⦗d⦘ ⨾ r) ≡₁ d ∩₁ dom_rel r.
  Proof. unfold dom_rel, eqv_rel, seq, set_inter, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma codom_eqv1 : codom_rel (r ⨾ ⦗d⦘) ≡₁ codom_rel r ∩₁ d.
  Proof. unfold codom_rel, eqv_rel, seq, set_inter, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma dom_cross (N: ~ d' ≡₁ ∅): dom_rel (d × d') ≡₁ d.
  Proof. apply set_nonemptyE in N; unfold dom_rel, cross_rel, set_equiv, set_subset; 
         split; ins; desf; eauto. Qed.

  Lemma codom_cross (N: ~ d ≡₁ ∅): codom_rel (d × d') ≡₁ d'.
  Proof. apply set_nonemptyE in N; unfold codom_rel, cross_rel, set_equiv, set_subset; 
         split; ins; desf; eauto. Qed.

  Lemma transp_doma : domb r d -> doma (transp r) d.
  Proof. unfold doma, domb, transp; eauto. Qed.

  Lemma transp_domb : doma r d -> domb (transp r) d.
  Proof. unfold doma, domb, transp; eauto. Qed.

  (* NOTE: cross_rel contains top, that isn't support fully *)
  Lemma cross_doma : doma (d × d') d.
  Proof. kat'. Qed.

  (* NOTE: cross_rel contains top, that isn't support fully *)
  Lemma cross_domb : domb (d × d') d'.
  Proof. kat'. Qed.

  Lemma lift_dom_impl: (forall a, d a -> d' a) <-> (d ⊆₁ d').
  Proof. reflexivity. Qed.
  Hint Rewrite lift_dom_impl: redefDb.

  Lemma doma_implies : (forall a, d a -> d' a) -> doma r d -> doma r d'.
  Proof. hkat'. Qed.

  Lemma domb_implies : (forall a, d a -> d' a) -> domb r d -> domb r d'.
  Proof. hkat'. Qed.

  Lemma doma_fold :
    (doma r d) -> (forall a, d a -> d' a) -> ⦗d'⦘ ⨾ r ≡ r.
  Proof. hkat'. Qed.

  Lemma domb_fold :
    (domb r d) -> (forall a, d a -> d' a) -> r ⨾ ⦗d'⦘ ≡ r.
  Proof. hkat'. Qed.

  Lemma doma_rewrite : doma r d -> r ⊆ ⦗d⦘ ⨾ r. 
  Proof. hkat'. Qed.

  Lemma domb_rewrite : domb r d -> r ⊆ r ⨾ ⦗d⦘. 
  Proof. hkat'. Qed.

  Lemma doma_helper : r ⊆ ⦗d⦘ ⨾ r <-> doma r d.
  Proof.
    split; [> hkat'' | hkat'].
  Qed.

  Lemma domb_helper : r ⊆ r ⨾ ⦗d⦘ <-> domb r d.
  Proof. 
    split; [> hkat'' | hkat'].
  Qed.
  
  Lemma domab_helper : 
    r ⊆ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ <-> doma r d /\ domb r d'.
  Proof.
    split; intros.
    - split; lift_to_kat_all; rewrite H; kat'.
    - destruct H; hkat'.
  Qed.

(* NOTE FAIL: kat fail because not support ⊤ fully. *)
  Lemma domab_helper2 :
    r ⊆ d × d' <-> doma r d /\ domb r d'.
  Proof.
    split.
    - rewrite cross_rel_iff_kat.
      intros; lift_to_kat_all; rewrite H; split; kat'.
    - (* intros [H1 H2]. *)
      (* assert (r ⊆ ⦗d⦘ ;; r ;; ⦗d'⦘). hkat'. *)
      (* rewrite H. kat'.  *)
      unfold doma, domb, cross_rel, inclusion; intuition; firstorder.
  Qed.

  Lemma dom_to_doma : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> doma r d.
  Proof.
    intro H; lift_to_kat_all; rewrite H; kat'.
  Qed.

  Lemma dom_to_domb : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> domb r d'.
  Proof.
    intro H; lift_to_kat_all; rewrite H; kat'.
  Qed.

  Lemma dom_l : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> r ≡ ⦗d⦘ ⨾ r.
  Proof.
    intro H; lift_to_kat_all; rewrite H; kat'.
  Qed.

  Lemma dom_r : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> r ≡ r ⨾ ⦗d'⦘.
  Proof.
    intro H; rewrite H; kat'.
  Qed.

  Lemma dom_helper_1 : r ⊆ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ <-> r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘.
  Proof.
    split; intros H.
    - split; [> apply H | kat'].
    - rewrite H; kat'.
  Qed.

  (* NOTE: top isn't supported *)
  Lemma dom_helper_2 : r ⊆ ⦗d⦘ ⨾ top_rel ⨾ ⦗d'⦘ <-> r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma dom_helper_3 : r ⊆ d × d' <-> r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma step_dom 
        (E: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
        de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗d'⦘)
        ed (ED: ed = ⦗d'⦘ ⨾ r ⨾ ⦗d⦘)
        ee (EE: ee = ⦗d'⦘ ⨾ r ⨾ ⦗d'⦘) :
    r ⊆ dd ∪ de ∪ ed ∪ ee.
  Proof.
    rewrite E. subst. kat'.
  Qed.

  Lemma path_dom
        (E1: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        (E2: ⦗d⦘ ⨾ ⦗d'⦘ ⊆ ∅₂)
        dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
        de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗d'⦘)
        ed (ED: ed = ⦗d'⦘ ⨾ r ⨾ ⦗d⦘)
        ee (EE: ee = ⦗d'⦘ ⨾ r ⨾ ⦗d'⦘) : 
    r⁺ ⊆ (dd⁺ ∪ (dd＊ ⨾ de ⨾ ee＊ ⨾ ed)⁺ ⨾ dd＊ ) ∪
       (ee⁺ ∪ (ee＊ ⨾ ed ⨾ dd＊ ⨾ de)⁺ ⨾ ee＊ ) ∪
       (ee＊ ⨾ ed ⨾ dd＊ ⨾ de)＊ ⨾ ee＊ ⨾ ed ⨾ dd＊ ∪
       (dd＊ ⨾ de ⨾ ee＊ ⨾ ed)＊ ⨾ dd＊ ⨾ de ⨾ ee＊.
  Proof. 
    apply inclusion_t_ind_right.
    { rewrite step_dom at 1; try eassumption.
      repeat apply inclusion_union_l; rewrite ?seqA.
      1,4: sin_rewrite !ct_end.
      all: try hkat'. }
    rewrite step_dom at 1; try eassumption.
    { rewrite ?DD, ?ED, ?DE, ?EE. hkat'. }
  Qed.

  Lemma path_dom_same
        (E1: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        (E2: ⦗d⦘ ⨾ ⦗d'⦘ ⊆ ∅₂)
        dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
        de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗d'⦘)
        ed (ED: ed = ⦗d'⦘ ⨾ r ⨾ ⦗d⦘)
        ee (EE: ee = ⦗d'⦘ ⨾ r ⨾ ⦗d'⦘) : 
    ⦗d⦘ ⨾ r⁺ ⨾ ⦗d⦘ ⊆ dd⁺ ∪ (dd＊ ⨾ de ⨾ ee＊ ⨾ ed)⁺ ⨾ dd＊.
  Proof.
    rewrite path_dom; try edone.
    { rewrite ?DD, ?ED, ?DE, ?EE. hkat'. }
  Qed.

  Lemma irr_dom
        (E1: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        (E2: ⦗d⦘ ⨾ ⦗d'⦘ ⊆ ∅₂)
        (IRRd: irreflexive (⦗d⦘ ⨾ r ⨾ ⦗d⦘)) 
        (IRRe: irreflexive (⦗d'⦘ ⨾ r ⨾ ⦗d'⦘)) :
    irreflexive r.
  Proof.
    rewrite step_dom; try edone.
    repeat rewrite irreflexive_union; splits; try done; 
      generalize E2; basic_solver 8.
  Qed.

  Lemma eq_dom_union :
    eq_dom (d ∪₁ d') f g <-> eq_dom d f g /\ eq_dom d' f g.
  Proof. 
    split.
    { ins. unfold eq_dom in *. 
      splits; ins; apply (H x); basic_solver. }
    intros [Hs Hs'].
    unfold eq_dom in *. ins. 
    unfold set_union in DX. 
    desf; basic_solver.
  Qed.  

  Lemma eq_dom_full_eq (EQD : eq_dom (fun _ => True) f g) :
    f = g.
  Proof. apply functional_extensionality. ins. by apply EQD. Qed.

  Lemma dom_cond_elim : r ⨾ ⦗dom_cond r d⦘ ⊆ ⦗d⦘ ⨾ r.
  Proof.
    unfold dom_cond; basic_solver 12.
  Qed.

  Lemma dom_cond_elim1 (IN: r ⊆ r') :
    r ⨾ ⦗dom_cond r' d⦘ ⊆ ⦗d⦘ ⨾ r.
  Proof. unfold dom_cond; basic_solver 21. Qed.

  Lemma dom_cond_elim2 :
    d' ∩₁ dom_cond r d ⊆₁ dom_cond (⦗ d' ⦘ ⨾ r) d.
  Proof. unfold dom_cond. basic_solver 12. Qed.

  Lemma dom_cond_union :
    dom_cond (r ∪ r') d ≡₁ dom_cond r d ∩₁ dom_cond r' d.
  Proof. unfold dom_cond; split; basic_solver 21. Qed.

  Lemma dom_cond_in :
    r ⨾ ⦗d'⦘ ⊆ ⦗d⦘ ⨾ r' -> d' ⊆₁ dom_cond r d.
  Proof.
    unfold dom_cond; unfolder; ins; desf.
   splits; eauto; eapply H; eauto.
  Qed.

  Lemma dom_rel_ext :
    dom_rel (r ⨾ r'^?) ≡₁ dom_rel r.
  Proof. basic_solver 10. Qed.

  Lemma dom_rel_eqv_dom_rel :
    dom_rel (r ⨾ ⦗dom_rel r'⦘) ≡₁ dom_rel (r ⨾ r').
  Proof. basic_solver 42. Qed.

  Lemma dom_rel_eqv_codom_rel :
    dom_rel (r ⨾ ⦗codom_rel r'⦘) ≡₁ dom_rel (r ⨾ r'⁻¹).
  Proof. basic_solver 42. Qed.

  Lemma dom_rel_fun_alt w : (fun a => r a w) ≡₁ dom_rel (r ⨾ ⦗ eq w ⦘).
  Proof. basic_solver 10. Qed.

  Lemma dom_rel_helper (IN:  dom_rel r ⊆₁ d) : r ≡ ⦗d⦘ ⨾ r.
  Proof. unfolder in *; basic_solver. Qed.

  Lemma dom_rel_helper_in (IN:  dom_rel r ⊆₁ d) : r ⊆ ⦗d⦘ ⨾ r.
  Proof. unfolder in *; basic_solver. Qed.
End Lemmas.

Lemma doma_eqv (d : A -> Prop) (r : relation A): doma (⦗d⦘ ⨾ r) d.
Proof. kat'. Qed.

Lemma domb_eqv (d : A -> Prop) (r : relation A): domb (r ⨾ ⦗d⦘) d.
Proof. kat'. Qed.

Lemma acyc_dom (r: relation A) d e
      (E1: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
      (E2: ⦗d⦘ ⨾ ⦗e⦘ ⊆ ∅₂)
      dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
      de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗e⦘)
      ed (ED: ed = ⦗e⦘ ⨾ r ⨾ ⦗d⦘)
      ee (EE: ee = ⦗e⦘ ⨾ r ⨾ ⦗e⦘) 
      (ACYCd: acyclic dd) 
      (ACYCe: acyclic ee) 
      (ACYCed: acyclic (ed ⨾ dd＊ ⨾ de ⨾ ee＊)) :
  acyclic r.
Proof.
  red.
  eapply irr_dom; try edone.
  { arewrite (⦗d⦘ ∪ ⦗e⦘ ≡ ⦗fun x => d x \/ e x⦘) by basic_solver.
    apply domab_helper; split.
    apply ct_doma; eapply domab_helper with (d':= fun x => d x \/ e x).
    rewrite E1 at 1; basic_solver.
    apply ct_domb; eapply domab_helper with (d := fun x => d x \/ e x).
    rewrite E1 at 1; basic_solver. }
  sin_rewrite path_dom_same; try edone.
  { repeat rewrite irreflexive_union; splits; try done.
    rewrite irreflexive_seqC.
    arewrite( dd＊ ⨾ (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ⁺ ⊆ (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ⁺).
    {  kat'. }
    assert (acyclic (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed)); try done. (*?*)
    rewrite acyclic_seqC; rewrite !seqA. 
    rewrite acyclic_seqC; rewrite !seqA. 
    rewrite acyclic_seqC; rewrite !seqA. 
    done. }
  rewrite unionC in E1.
  sin_rewrite path_dom_same; try edone; try by rewrite seq_eqvC.
  repeat rewrite irreflexive_union; splits; try done.
  rewrite irreflexive_seqC.
  arewrite( ee＊ ⨾ (ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de) ⁺  ⊆ (ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de) ⁺).
  { kat'. }
  assert (acyclic(ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de)); try done. (*?*)
  rewrite acyclic_seqC; rewrite !seqA. 
  done.
Qed.

End Domains.

Hint Rewrite doma_iff_kat domb_iff_kat: redefDb.

Add Parametric Morphism A : (@doma A) with signature
  inclusion --> set_subset ==> Basics.impl as doma_mori.
Proof.
  unfold inclusion, doma, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@domb A) with signature
  inclusion --> set_subset ==> Basics.impl as domb_mori.
Proof.
  unfold inclusion, domb, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@doma A) with signature
  same_relation ==> set_equiv ==> iff as doma_more.
Proof.
  unfold same_relation; ins; rewrite set_equivE in *; 
    desc; split; eapply doma_mori; eauto.
Qed.

Add Parametric Morphism A : (@domb A) with signature
  same_relation ==> set_equiv ==> iff as domb_more.
Proof.
  unfold same_relation; ins; rewrite set_equivE in *; 
    desc; split; eapply domb_mori; eauto.
Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
  inclusion ==> set_subset as dom_rel_mori.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
  inclusion ==> set_subset as codom_rel_mori.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
  same_relation ==> set_equiv as dom_rel_more.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
  same_relation ==> set_equiv as codom_rel_more.
Proof.
  firstorder. 
Qed.

Add Parametric Morphism A : (@dom_cond A) with signature
  inclusion --> set_subset ==> set_subset as dom_cond_mori.
Proof.
  ins. unfold dom_cond.
  red; ins.
    by rewrite H, <- H0.
Qed.

Add Parametric Morphism A : (@dom_cond A) with signature
  same_relation ==> set_equiv ==> set_equiv as dom_cond_more.
Proof.
  unfold dom_cond; unfolder; ins; splits; ins; desf; eauto 10.
Qed.

Hint Unfold doma domb eq_dom dom_cond : unfolderDb.

Hint Resolve eqv_doma seq_eqv_doma restr_eq_rel_doma : hahn. 
Hint Resolve seq_doma union_doma ct_doma seq_r_doma : hahn.
Hint Resolve transp_doma cross_doma restr_doma restr_doma_mon : hahn.
Hint Resolve eqv_domb seq_eqv_domb restr_eq_rel_domb : hahn.
Hint Resolve seq_domb union_domb ct_domb seq_r_domb : hahn.
Hint Resolve transp_domb cross_domb restr_domb restr_domb_mon : hahn.

Hint Rewrite dom_empty codom_empty dom_union codom_union : hahn.
Hint Rewrite dom_eqv codom_eqv dom_eqv1 codom_eqv1 : hahn.
Hint Rewrite dom_cross codom_cross : hahn_full.
