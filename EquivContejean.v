(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides a proof of equivalence between IlistPerm3 and 
     a definition given by Contejean *)

Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Basics.
Require Import Fin.
Require Import Ilist.
Require Import IlistPerm.
Require Import Extroduce.
Require Import Tools.

Set Implicit Arguments.

(* Definition Contejean *)
Inductive permut (A B : Set) (R : A -> B -> Prop) : (list A -> list B -> Prop) :=
  | Pnil : permut R nil nil
  | Pcons : forall a b l l1 l2, R a b -> permut R l (l1 ++ l2) ->
                   permut R (a :: l) (l1 ++ b :: l2).

Lemma equiv_list_permut_IlistPerm3 (T: Set)(R: relation T): 
  forall (l1 l2: list T), permut R l1 l2 -> IlistPerm3 R (list2ilist l1) (list2ilist l2).
Proof.
  intros l1 l2 H.
  induction H as [| a b l l1 l2 H1 H2 IH].
  apply IlistPerm3nil.

  assert (h: length l1 < lgti (list2ilist (l1 ++ b :: l2))).
  cbn.
  rewrite app_length.
  apply lt_plus_S.
  apply (IlistPerm3_cons _ _ (first _ : Fin (lgti (list2ilist (a :: l)))) (code_Fin1 h)).
  do 2 rewrite <- (list2ilist_nth2 _ _ b).
  fold (length l).
  rewrite decode_code1_Id.
  rewrite (app_nth2 _ _ b (le_refl _)).
  rewrite minus_diag.
  assumption.

  assert (H3 : ilist_rel eq (list2ilist l) (extroduce (list2ilist (a :: l)) (first _))).
  simpl.
  set (Hyp1 := refl_equal _ : lgti (list2ilist l) = lgti (mkilist (fun x => nth (decode_Fin x) l a))).
  apply (is_ilist_rel eq _ _ Hyp1).
  cbn in *|-*.
  intro i.
  symmetry. 
  apply (list2ilist_nth2 l).

  assert (H4 : ilist_rel eq (list2ilist (l1 ++ l2))
    (extroduce (list2ilist (l1 ++ b :: l2)) (code_Fin1 h))).
  assert (h1 : lgti (list2ilist (l1 ++ l2)) = 
    lgti (extroduce (list2ilist (l1 ++ b :: l2)) (code_Fin1 h))).
  apply eq_add_S.
  rewrite <- extroduce_lgti.
  apply list2ilist_app_lgti.
  apply (is_ilist_rel _ _ _ h1).
  intros i ; simpl in i.
  rewrite <- (list2ilist_nth2 _ _ b).
  elim (le_lt_dec (decode_Fin (code_Fin1 h)) (decode_Fin (rewriteFins h1 i))) ; intros h2.
  rewrite extroduce_ok3' ; try assumption.
  rewrite <- (list2ilist_nth2 _ _ b).
  rewrite <- decode_Fin_match'.
  simpl.
  rewrite <- decode_Fin_match'.
  rewrite <- decode_Fin_match', decode_code1_Id in h2.
  rewrite app_nth2, app_nth2 ; try assumption.
  rewrite <- minus_Sn_m ; try assumption.
  reflexivity.
  apply (le_trans _ _ _ h2 (le_n_Sn _)).

  rewrite extroduce_ok2' ; try assumption.
  rewrite <- (list2ilist_nth2 _ _ b).
  rewrite <- decode_Fin_match', weakFin_ok, <- decode_Fin_match'.
  rewrite <- decode_Fin_match', decode_code1_Id in h2.
  rewrite app_nth1, app_nth1 ; try assumption.
  reflexivity.
  apply (IlistPerm3_ilist_rel_eq H3), (IlistPerm3_ilist_rel_eq_snd H4), IH.
Qed.

Lemma equiv_ilist_IlistPerm3_permut (T: Set)(R: relation T): 
  forall (l1 l2: ilist T), IlistPerm3 R l1 l2 -> permut R (ilist2list l1) (ilist2list l2).
Proof.
  intros l1 l2 H1.
  apply IlistPerm3_IlistPerm4_eq in H1.
  induction H1 as [l1 l2 H2 IH] using IlistPerm4_ind_better.
  destruct l1 as [n l1] ; destruct l2 as [n2 l2].
  fold (mkilist l1) (mkilist l2) in *|-*.
  simpl in H2. 
  revert l2 IH ; rewrite <- H2  ; clear n2 H2 ; intros l2 IH.
  destruct n as [|n].
  apply Pnil.

  simpl fcti in IH.
  simpl (lgti (mkilist _)) in IH.
  
  destruct (IH (first n)) as [i2 [H1 [_ H3]]] ; clear IH.

  assert (H4 := left_sib_right_sib (mkilist l2) i2).
  assert (H5 : ilist2list (mkilist l1) = l1 (first n) :: ilist2list (mkilist (fun x => l1 (succ x)))).
  unfold ilist2list.
  simpl.
  f_equal.
  apply map_map.
  rewrite <- H4, H5 ; clear H4 H5.
  
  apply Pcons.
  assumption.
  rewrite left_right_sib_extroduce_bis.
  assumption.
Qed.

Lemma equiv_list_IlistPerm3_permut' (T: Set)(R: relation T): 
  forall (l1 l2: list T), IlistPerm3 R (list2ilist l1) (list2ilist l2) -> permut R l1 l2.
Proof.
  intros l1 l2 H.
  rewrite <- (ilist2list_list2ilist_id l1).
  rewrite <- (ilist2list_list2ilist_id l2).
  apply equiv_ilist_IlistPerm3_permut.
  assumption.
Qed.

Lemma equiv_ilist_permut_IlistPerm3 (T: Set)(R: relation T): 
  forall (l1 l2: ilist T), permut R (ilist2list l1) (ilist2list l2) -> IlistPerm3 R l1 l2.
Proof.
  intros l1 l2 H.
  apply (IlistPerm3_ilist_rel_eq (list2ilist_ilist2list_id l1)),
    (IlistPerm3_ilist_rel_eq_snd (list2ilist_ilist2list_id l2)).
  apply (equiv_list_permut_IlistPerm3 H).
Qed.


