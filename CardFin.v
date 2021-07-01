(** CardFin.v Version 1.1 February 2011 *)
(** runs under V8.4beta, tested with version trunk 15623 *)

(** Celia Picard, I.R.I.T.,  University of Toulouse, 
    based on a development by Yves Bertot (INRIA Sophia-Antipolis), 
    communicated privately *)

(**  provides a proof of a calculation of the cardinal of Fin, 
     without using Ssreflect (hence with no card operation really) 
     and an alternative proof of the injectivity of Fin *)

Require Import List Arith.
Require Import Fin.

Set Implicit Arguments.

Definition eq_dec (T: Type) : Type := forall (x y : T), {x = y}+{x <> y}.

Section EnumFinType.
 
Variable T : Type.
Variable T_eq_dec : eq_dec T.

Fixpoint count (tst : eq_dec T) x l :=
  match l with
    nil => 0
  | a::tl => if tst x a then 1 + count tst x tl else count tst x tl
  end.

Lemma count_irrel : forall tst1 tst2 x l, count tst1 x l = count tst2 x l.
Proof.
  intros tst1 tst2 x l.
  induction l as [ | a tl Ht].
  reflexivity.
  simpl; case (tst1 x a);[intros xa | intros xna];
    (case (tst2 x a);[intros xa' | intros xna']).
  rewrite Ht ; reflexivity.
  case xna'; assumption.
  case xna; assumption.
  apply Ht.
Qed.

(* An enumeration is a list that contains exactly once all the 
   elements of T *)
Definition is_enum l := forall x, count T_eq_dec x l = 1.

Lemma count_app (l1 l2 : list T)(t: T) : 
  count T_eq_dec t (l1++l2) = count T_eq_dec t l1 + count T_eq_dec t l2.
Proof.
  induction l1 as [|t1 l1 IH].
  reflexivity.
  simpl.
  elim (T_eq_dec t t1) ; intros a.
  rewrite IH.
  reflexivity.
  apply IH.
Qed.

Fixpoint rem1 x l :=
  match l with
    nil => nil
  | a::tl => if T_eq_dec x a then tl else a::rem1 x tl
  end.

Lemma count_rem1_eq :
  forall x l, count T_eq_dec x l <> 0 ->
  count T_eq_dec x l = 1 + count T_eq_dec x (rem1 x l).
Proof.
intros x; induction l as [ | a tl Ht].
  intros abs; case abs; reflexivity.
simpl; case_eq (T_eq_dec x a); simpl.
  intros _ _ _; reflexivity.
intros n tst cn0; rewrite tst.
  apply Ht; assumption.
Qed.

Lemma count_rem1_eq_length :
  forall x l, count T_eq_dec x l <> 0 -> length l = S (length (rem1 x l)). 
Proof.
  intros x ; induction l as [|t l IH]. 
  intros H1.
  apply False_rec, H1, eq_refl.
  simpl.
  elim (T_eq_dec x t) ; intros H1 H2 ; f_equal.
  apply (IH H2).
Qed.

Lemma count_rem1_diff :
  forall x y l, x <> y -> count T_eq_dec y l = count T_eq_dec y (rem1 x l).
Proof.
intros x y l xny; induction l as [ | a tl Ht].
  reflexivity.
simpl; case_eq (T_eq_dec y a); intros ya tya.
  case (T_eq_dec x a).
    intros xa; case xny; rewrite ya; assumption.
  simpl; rewrite tya, Ht; reflexivity.
case (T_eq_dec x a); [reflexivity | simpl; rewrite Ht, tya; reflexivity].
Qed.

Lemma count_rem1_diff_length :
  forall x l, count T_eq_dec x l = 0 -> length l = length (rem1 x l).
Proof.
  intros x l H; induction l as [ | t l IH].
  reflexivity.
  revert H ; simpl; elim (T_eq_dec x t) ; intros H1 H.
  inversion H.
  simpl ; f_equal.
  apply IH, H.
Qed.

Lemma rem1_cons_eq :
  forall x l, rem1 x (x::l) = l.
Proof.
  intros x l.
  simpl.
  elim (T_eq_dec x x) ; intros H.
  reflexivity.
  apply False_rec, H, eq_refl.
Qed.

Lemma rem1_cons_diff :
  forall x y l, x <> y -> rem1 x (y :: l) = y :: rem1 x l.
Proof.
  intros x y l H1.
  simpl.
  elim (T_eq_dec x y) ; intros H2.
  contradiction H1.
  reflexivity.
Qed.

Lemma count_cons_eq :
  forall x l, count T_eq_dec x (x :: l) = S (count T_eq_dec x l).
Proof.
  intros x l.
  simpl.
  elim (T_eq_dec x x) ; intros H1.
  reflexivity.
  apply False_rec, H1, eq_refl.
Qed.

Lemma count_cons_diff :
  forall x y l, x <> y -> count T_eq_dec x (y :: l) = count T_eq_dec x l.
Proof.
  intros x y l H1.
  simpl.
  elim (T_eq_dec x y) ; intros H2.
  contradiction H1.
  reflexivity.
Qed.

Lemma rem1_count_inf : forall x y l, count T_eq_dec x (rem1 y l) <= count T_eq_dec x l.
Proof.
  intros x y ; induction l as [|t l IH].
  apply le_refl.
  simpl.
  elim (T_eq_dec y t) ; simpl ; elim (T_eq_dec x t) ; intros H1 H2.
  apply le_n_Sn.
  apply le_refl.
  apply le_n_S, IH.
  apply IH.
Qed.

Lemma rem1_count_0 :
  forall x y l, count T_eq_dec x l = 0 -> count T_eq_dec x (rem1 y l) = 0.
Proof.
  intros x y l H1.
  apply sym_eq, le_n_0_eq.
  rewrite <- H1.
  apply rem1_count_inf.
Qed.

Lemma is_enum_eq (x: T)(l1 l2 : list T) : 
  is_enum (l1 ++ x :: l2) -> count T_eq_dec x l1 = 0 /\ count T_eq_dec x l2 = 0.
Proof.
  intros H.
  assert (H1 := H x).
  rewrite count_app, count_cons_eq, <- plus_n_Sm in H1.
  apply eq_add_S in H1.
  apply plus_is_O, H1.
Qed.

Lemma is_enum_eq_cor1 (x: T)(l1 l2 : list T) : 
  is_enum (l1 ++ x :: l2) -> count T_eq_dec x l1 = 0.
Proof.
  intros H.
  destruct (is_enum_eq _ _ _ H) as [H1 _].
  assumption.
Qed.

Lemma is_enum_eq_cor2 (x: T)(l1 l2 : list T) : 
  is_enum (l1 ++ x :: l2) -> count T_eq_dec x l2 = 0.
Proof.
  intros H.
  destruct (is_enum_eq _ _ _ H) as [_ H1].
  assumption.
Qed.

Lemma indep_enum:
  forall l1 l2, is_enum l1 -> is_enum l2 -> length l1 = length l2.
Proof.
  assert (aux : forall l1 l2 l3, 
    is_enum (l3++l1) -> is_enum (l3++l2) -> length l1 = length l2).
  induction l1 as [|t1 l1 IH1] ; intros [|t2 l2] l3 H1 H2.
  reflexivity.
  rewrite app_nil_r in H1.
  assert (H3 := is_enum_eq_cor1 _ _ _ H2).
  rewrite (H1 t2) in H3.
  inversion H3.

  rewrite app_nil_r in H2.
  assert (H3 := is_enum_eq_cor1 _ _ _ H1).
  rewrite (H2 t1) in H3.
  inversion H3.

  assert (H3 : length (t2 :: l2) = length (t1::rem1 t1 (t2::l2))).
  simpl.
  elim (T_eq_dec t1 t2) ; intros a.
  reflexivity.
  simpl.
  f_equal.
  rewrite <- count_rem1_eq_length.
  reflexivity.
  intros H.
  assert (H2' := H2 t1).
  rewrite count_app, count_cons_diff, H, (is_enum_eq_cor1 _ _ _ H1) in H2' ; try apply a.
  inversion H2'.
  rewrite H3.
  change (S (length l1) = S (length (rem1 t1 (t2 :: l2)))).
  f_equal.
  elim (T_eq_dec t1 t2) ; intros a.
  rewrite a.
  rewrite rem1_cons_eq.
  rewrite <- a in H2.
  apply (IH1 _ (l3 ++ t1 :: nil)) ;
  rewrite <- app_assoc, <- app_comm_cons, app_nil_l ; assumption.

  rewrite rem1_cons_diff; try apply a.
  apply (IH1 (t2 :: rem1 t1 l2) (l3 ++ t1 :: nil)).
  rewrite <- app_assoc, <- app_comm_cons, app_nil_l ; assumption.
  rewrite <- app_assoc, <- app_comm_cons, app_nil_l.
  intros x.
  generalize (H2 x).
  do 2 rewrite count_app.
  simpl.
  elim (T_eq_dec x t2) ; elim (T_eq_dec x t1) ; intros H4 H5 H6 ; 
  try (rewrite <- H4 in *|-* ; clear H4) ; try (rewrite <- H5 in *|-* ; clear H5).
  apply False_rec, a, eq_refl.
  rewrite <- H6 ; do 2 f_equal.
  rewrite (is_enum_eq_cor2 _ _ _ H2).
  apply rem1_count_0, (is_enum_eq_cor2 _ _ _ H2).
  rewrite <- H6 ; f_equal.
  rewrite (count_rem1_eq x l2).
  reflexivity.
  intros H7.
  rewrite (is_enum_eq_cor1 _ _ _ H1), H7 in H6.
  inversion H6.

  rewrite <- H6 ; f_equal.
  rewrite <- count_rem1_diff.
  reflexivity.
  apply not_eq_sym, H4.
  intros l1 l2 H1 H2.
  apply (aux _ _ nil) ; rewrite app_nil_l ; assumption.
Qed.

End EnumFinType.

Section CardFin.

Lemma eq_dec_Fin (n: nat) : eq_dec (Fin n).
Proof.
  intros i1 i2.
  elim (eq_nat_dec (decode_Fin i1) (decode_Fin i2)) ; intros a.
  left.
  apply decode_Fin_unique, a.
  right.
  intros b.
  apply a ; rewrite b ; reflexivity.
Qed.

Lemma first_succ_count_0 (n: nat)(l: list (Fin n)): 
  count (@eq_dec_Fin _) (first n) (map (@succ _) l) = 0.
Proof.
  induction l as [|t l IH].
  trivial.
  simpl.
  elim (eq_dec_Fin (first n) (succ t)) ; intros a.
  inversion a.
  apply IH.
Qed.

Definition injective (T U : Set)(f: T -> U) : Prop :=
  forall t1 t2, f t1 = f t2 -> t1 = t2.

Lemma count_map (T U : Set)(tstT : eq_dec T)
  (tstU : eq_dec U)(f: T -> U)(h: injective f)(l: list T):
  forall t, count tstT t l = count tstU (f t) (map f l).
Proof.
  induction l as [|tt l IH] ; intros t.
  reflexivity.
  simpl.
  rewrite IH.
  elim (tstT t tt) ; intros a.
  rewrite a.
  elim (tstU (f tt) (f tt)) ; intros b.
  reflexivity.
  apply False_rec, b ; reflexivity.
  
  elim (tstU (f t) (f tt)) ; intros b.
  apply h in b.
  contradiction a.
  reflexivity.
Qed.

Lemma succ_inj (n: nat) : injective (@succ n).
Proof.
  intros i1 i2 H.
  (* The injection tactic does not help here *)
  assert (H1 := decode_Fin_S_gt_O i1).
  rewrite <- (get_cons_ok2 H1), <- (get_cons_ok i2).
  revert H1 ; rewrite H ; intros H1.
  apply get_cons_proofirr.
Qed.

Lemma enum_makeListFin : forall n, is_enum (@eq_dec_Fin _) (makeListFin n).
Proof.
  induction n as [|n IH] ; intros i.
  inversion i.
  simpl.
  elim (eq_dec_Fin i (first n)) ; intros a.
  rewrite a.
  rewrite first_succ_count_0.
  reflexivity.
  elim (zerop (decode_Fin i)) ; intros b.
  contradiction a.
  apply (decode_Fin_0_first _ b).
  rewrite <- (get_cons_ok1 _ b), <- (count_map (@eq_dec_Fin _) _ (@succ_inj _)).
  apply IH.
Qed.


Lemma Fin_inj_alt (n m: nat) : Fin n = Fin m -> n = m.
Proof.
  intros H1.
  generalize (@eq_dec_Fin n), (makeListFin n), (makeListFin_nb_elem_ok n), 
    (@enum_makeListFin n).
  rewrite H1.
  intros Heq l H2 H3.
  rewrite <- H2, <- makeListFin_nb_elem_ok.
  apply (indep_enum H3).
  intros x.
  rewrite (count_irrel Heq (@eq_dec_Fin _)).
  apply enum_makeListFin.
Qed.

End CardFin.
