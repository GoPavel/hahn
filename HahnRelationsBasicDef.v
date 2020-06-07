Require Import HahnBase HahnList.
Require Export Relations.

Set Implicit Arguments.

(******************************************************************************)
(** * Relational operators *)
(******************************************************************************)

Arguments clos_trans [A] R x y.
Arguments clos_refl_trans [A] R x y.
Arguments union [A] R1 R2 x y.
Arguments reflexive [A] R.
Arguments symmetric [A] R.
Arguments transitive [A] R.
Arguments antisymmetric [A] R.
Arguments inclusion {A} R1 R2.
Arguments same_relation {A} R1 R2.
Arguments transp [A] R x y.

Section RelDefs.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables r r' : relation A.

  Definition singl_rel a b : relation A := fun x y => x = a /\ y = b.

  Definition inter_rel : relation A := fun x y => r x y /\ r' x y.

  Definition minus_rel : relation A := fun x y => r x y /\ ~ r' x y.

  Definition eq_rel : relation A := fun x y => f x = f y.

  Definition eqv_rel : relation A := fun x y => x = y /\ cond x.

  Definition eqv_dom_rel dom : relation A :=
    fun x y => x = y /\ In x dom.

  Definition restr_rel : relation A :=
    fun x y => r x y /\ cond x /\ cond y.

  Definition restr_eq_rel : relation A :=
    fun x y => r x y /\ f x = f y.

  Definition seq : relation A :=
    fun x y => exists z, r x z /\ r' z y.

  Definition map_rel (r'' : relation B) : relation A := fun x y => r'' (f x) (f y).

  Definition clos_refl : relation A := fun x y => x = y \/ r x y.

  Definition dom_rel := fun x => exists y, r x y.
  Definition codom_rel := fun y => exists x, r x y.

  Definition collect_rel : relation B := fun x y =>
    exists x' y', r x' y' /\ f x' = x /\ f y' = y.

  Definition immediate : relation A := fun a b =>
    r a b /\ (forall c (R1: r a c) (R2: r c b), False).

  Definition irreflexive := forall x, r x x -> False.

  Definition is_total :=
    forall a (IWa: cond a)
           b (IWb: cond b) (NEQ: a <> b),
      r a b \/ r b a.

  Definition restr_subset :=
    forall a (IWa: cond a)
           b (IWb: cond b) (REL: r a b),
      r' a b.

  Definition upward_closed (P: A -> Prop) :=
    forall x y (REL: r x y) (POST: P y), P x.

  Definition functional := forall x y z, r x y -> r x z -> y=z.
  
  Definition strict_partial_order := irreflexive /\ transitive r.

  Definition strict_total_order := strict_partial_order /\ is_total.
End RelDefs.

Fixpoint pow_rel A (r: relation A) n :=
  match n with
  | 0 => eqv_rel (fun _ => True)
  | S n => seq (pow_rel r n) r
  end.

Definition bunion A B (P : A -> Prop) (r: A -> relation B) x y :=
  exists a, P a /\ r a x y.

Definition acyclic A (r: relation A) := irreflexive (clos_trans r).

Definition cross_rel A (r r' : A -> Prop) := (fun a b => r a /\ r' b).

Hint Unfold reflexive symmetric transitive inclusion same_relation : unfolderDb. 
Hint Unfold union transp singl_rel inter_rel minus_rel bunion : unfolderDb.
Hint Unfold eq_rel eqv_rel eqv_dom_rel restr_rel restr_eq_rel seq map_rel : unfolderDb.
Hint Unfold clos_refl dom_rel codom_rel cross_rel collect_rel : unfolderDb.
Hint Unfold immediate irreflexive acyclic is_total functional : unfolderDb. 
Hint Unfold upward_closed : unfolderDb.
Hint Unfold antisymmetric strict_partial_order strict_total_order : unfolderDb.

(** We introduce the following notation. *)

Notation "P ∩ Q" := (inter_rel P Q) (at level 40, left associativity).
Notation "P ∪ Q" := (union P Q) (at level 50, left associativity).
Notation "P \ Q" := (minus_rel P Q) (at level 46).
Notation "P ⨾ Q" := (seq P Q) (at level 44, right associativity).
Notation "⦗ a ⦘" := (eqv_rel a) (format "⦗ a ⦘").
Notation "∅₂" := (fun _ _ => False).
Notation "P × Q" := (cross_rel P Q) (at level 29, left associativity).

Notation "a ^?" := (clos_refl a) (at level 1, format "a ^?").
Notation "a ^^ n" := (pow_rel a n) (at level 1).

Notation "a ⁺" := (clos_trans a) (at level 1, format "a ⁺").
Notation "a ＊" := (clos_refl_trans a) (at level 1, format "a ＊").
Notation "a ⁻¹" := (transp a) (at level 1, format "a ⁻¹").
Notation "a ⊆ b" := (inclusion a b)  (at level 60).
(* Notation "a ≡ b" := (same_relation a b)  (at level 60). *)

Notation "⋃ x ∈ s , a" := (bunion s (fun x => a))
  (at level 200, x ident, right associativity, 
   format "'[' ⋃ '/ ' x  ∈  s ,  '/ ' a ']'").
Notation "'⋃' x , a" := (bunion (fun _ => True) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x ,  '/ ' a ']'").
Notation "'⋃' x < n , a" := (bunion (fun t => t < n) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  <  n ,  '/ ' a ']'").
Notation "'⋃' x <= n , a" := (bunion (fun t => t <= n) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  <=  n ,  '/ ' a ']'").
Notation "'⋃' x > n , a" := (bunion (fun t => n < t) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  >  n ,  '/ ' a ']'").
Notation "'⋃' x >= n , a" := (bunion (fun t => n <= t) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  >=  n ,  '/ ' a ']'").

(** Here are some alternative non-unicode notations *)

Notation "P +++ Q" := (union P Q) (at level 50, left associativity, only parsing).
Notation "P ;; Q" := (seq P Q) (at level 44, right associativity, only parsing).
Notation "<| a |>" := (eqv_rel a) (only parsing).
(* Notation "a ^+" := (clos_trans a) (at level 1, only parsing). *)
(* Notation "a ^*" := (clos_refl_trans a) (at level 1, only parsing). *)
Notation "a ^{-1}" := (transp a) (at level 1, only parsing).
Notation "a <<= b" := (inclusion a b)  (at level 60, only parsing).
(* Notation "a <--> b" := (same_relation a b)  (at level 60(* , only parsing  *)). *)
