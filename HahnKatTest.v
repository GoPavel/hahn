Require Import HahnKat.
Require Import RelationAlgebra.kat_tac.
Require Import RelationAlgebra.lattice.
Require Import RelationAlgebra.monoid.
Require Import RelationAlgebra.kat.

Require Import HahnRelationsBasicDef HahnBase.

Set Printing Coercions.
Set Implicit Arguments.

Variable A : Type.
Variables r r': relation A.
Variables dom dom1 dom2 d d1 d2: A -> Prop.

Goal r ⊆ r ∪ r'.
Proof. kat'. Qed.

Goal forall `{r: relation A}, r ≡ r.
Proof. intro. kat'. Qed.

(* BUG in relation-algebra
     When we have only [cp_c] there isn't any hypotheses with shape [r ≦ 0] after aggregation.
     So hkat have fail in that case.
 *)
Lemma cp_c `{L: laws} {n} (c: tst n) (p: X n n):
  [c]⋅p ≡ [c] -> p ≡ [!c]⋅p+[c].
Proof. Fail hkat. Abort.

Goal ⦗d⦘;;r <--> ⦗d⦘ -> ⦗d⦘;;r <--> ⦗d⦘.
Proof. hkat''. Qed.

(* Notation "x ^+" := (itr tt x)   (left associativity, at level 5, format "x ^+"): ra_terms. *)

Locate "x ^+".
Locate "x ∩ y".
Locate "x ⁺".
Locate "x ^+".

Local Notation " [ p ] " := (inj (n:=tt) p): ra_terms.

Check @cap rel_lattice_ops (str tt r) r.
Check cap (str tt r) r.
Check (r ⊓ str tt r).

(* Canonical Structure dual_rel_kat_ops A := (dual (@rel_kat_ops A)). *)
(* Instance dual_rel_kat_laws A : kat.laws (@dual_rel_kat_ops A) *)
(*   := dual_laws rel_kat_laws. *)

(* Lemma l1 `{L: kat.laws} {n m} (p: X n m): (cup p p ≡ p). *)
(* Proof. kat. Qed. *)

(* Lemma l2 `{L: kat.laws} {m n} (p: X m n): (cap p p ≡ p). *)
(* Proof. dual @l1. remember(lattice.dualize _ (@l1)). *)
(*         apply w. hnf in w. apply w. *)

(* Lemma l2 (p: relation A): (p ⊓ p ≡ p). *)
(* Proof. remember(dualize (@l1) (H:=@rel_kat_laws A)). *)
(*         apply w. hnf in w. apply w. *)

Goal  (r ⊓ (str tt r) ⊔ r) ≡ bot.
Proof.
  rewrite <- same_rel_iff_weq.
Abort.

Goal r⁺ ∩ (one tt) <--> bot.
Proof.
  lift_to_kat_all.
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

(* KAT doesn't support transp *)
Goal transp r ;; transp r <--> transp (r ;; r).
Proof. lift_to_kat_all. repeat rewrite transp_iff_cnv. Fail kat'. Abort.

Goal ⦗d⦘ <--> transp ⦗d⦘.
Proof. Fail kat'. Abort.

Lemma acyclic_restr: acyclic r -> acyclic (restr_rel d r).
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

(* ⊤ isn't supported by KAT *)
Goal top ;; ⦗dom1⦘;; (top;;⦗dom1⦘)＊ ≡ top ;; ⦗dom1⦘.
Proof. Fail kat'. Abort.

Implicit Type s : A -> Prop.
Lemma ct_of_cross s s' : (s × s')⁺ <--> s × s'.
Proof. lift_to_kat_all. Fail kat'. Abort.

Definition prefix_clos x (r: relation A) := r ;; ⦗x⦘ ⊆ ⦗x⦘ ;; r.

(* Lemma pre_agg_prefix_clos *)

Goal forall (H1: prefix_clos d r) (H2: prefix_clos d r'),
    prefix_clos d (r ;; r).
Proof.
  unfold prefix_clos.
  lift_to_kat_all.
  hkat''.
Qed.

Goal (r ∪ r);;⦗(@neg dset')d⦘ <--> (r;;⦗(@neg dset')d⦘) ∪ (r;;⦗(@neg dset')d⦘).
Proof. kat'. Qed.

Goal (r ∪ r);;⦗(@neg dset')d⦘ ⊆ bot <-> r;;⦗(@neg dset')d⦘ ∪ r;;⦗(@neg dset')d⦘ ⊆ bot.
Proof.
  split.
  - hkat'.
  - hkat'.
Qed.
