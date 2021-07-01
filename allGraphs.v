(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides the implementation of the type Graphs, properties 
     and lemmas on it, and the development of various examples *)

Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import List.
Require Import Ilist.
Require Import Fin.
Require Import Graphs.
Require Import Morphisms.
Require Import Basics.
Require Import Tools.
Require Import PermsLists.
Require Import GPerm.

Set Implicit Arguments.

Section AllGraphs_def_tools. 

  Variable T: Set.
  (* Definition of coinductive graphs *)
  Definition AllGraph: Set := Graph (option T).
  
  Definition AGeq (R: relation T) : relation AllGraph := Geq (RelOp R).

  Lemma AGeq_refl (R: relation T)(Rrefl: Reflexive R) : Reflexive (AGeq R).
  Proof.
    red.
    apply Geq_refl.
    red.
    apply RelOp_refl, Rrefl.
  Qed.

  Lemma AGeq_sym (R: relation T)(Rsym: Symmetric R) : Symmetric (AGeq R).
  Proof.
    red.
    apply Geq_sym.
    red.
    apply RelOp_sym, Rsym.
  Qed.

  Lemma AGeq_trans (R: relation T)(Rtrans: Transitive R) : Transitive (AGeq R).
  Proof.
    red.
    apply Geq_trans.
    red.
    apply RelOp_trans, Rtrans.
  Qed.
  
  Add Parametric Relation (RelT: relation T)(Req: Equivalence RelT): (AllGraph) (AGeq RelT)
    reflexivity proved by (AGeq_refl _)
    symmetry proved by (AGeq_sym _)
    transitivity proved by (AGeq_trans _)
  as AGeqRel.

  Definition ForestGr : Set := list (Graph T).
  
  CoFixpoint G2AG (g: Graph T) : AllGraph := mk_Graph (Some (label g)) (imap G2AG (sons g)).
  
  CoFixpoint FG2AG (lg : ForestGr) : AllGraph := mk_Graph None (list2ilist (map G2AG lg)).
  
  Definition FGeq (R: relation T) : relation ForestGr := permut1 (GPPerm R).
  
  Lemma FGeq_refl (R: relation T)(Rrefl: Reflexive R) : Reflexive (FGeq R).
  Proof.
    red.
    apply permut1_refl.
    red.
    apply GPPerm_refl, Rrefl.
  Qed.

  Lemma FGeq_sym (R: relation T) : Symmetric (FGeq R).
  Proof.
    red.
    apply permut1_sym.
    red.
    apply GPPerm_sym.
  Qed.

  Lemma FGeq_trans (R: relation T)(Rtrans: Transitive R) : Transitive (FGeq R).
  Proof.
    red.
    apply permut1_trans.
    red.
    apply GPPerm_trans, Rtrans.
  Qed.
  
  Add Parametric Relation (RelT: relation T)(Req: Equivalence RelT): (ForestGr) (FGeq RelT)
    reflexivity proved by (FGeq_refl _)
    symmetry proved by (@FGeq_sym _)
    transitivity proved by (FGeq_trans _)
  as FGeqRel.


End AllGraphs_def_tools.
(* Graph 1 -> 0 <- 2*)

Definition two_roots_AllGraph : AllGraph nat.
Proof.
  set (node0 := mk_Graph (Some 0) (inil (AllGraph nat))).
  set (node1 := mk_Graph (Some 1) (icons node0 (inil (AllGraph nat)))).
  set (node2 := mk_Graph (Some 2) (icons node0 (inil (AllGraph nat)))).
  exact (mk_Graph None (icons node1 (icons node2 (inil (AllGraph nat))))).
Defined.

Definition two_roots_ForestGr : ForestGr nat.
Proof.
  set (node0 := mk_Graph 0 (inil (Graph nat))).
  set (node1 := mk_Graph 1 (icons node0 (inil (Graph nat)))).
  set (node2 := mk_Graph 2 (icons node0 (inil (Graph nat)))).
  exact (node1 :: node2 :: nil).
Defined.

Lemma two_roots_ForestGr_two_roots_AllGraph : 
  Geq (RelOp eq) two_roots_AllGraph (FG2AG two_roots_ForestGr).
Proof.
  apply Geq_intro.
  
  simpl.
  trivial.
  
  assert (h1 := refl_equal _: lgti (sons two_roots_AllGraph) = lgti (sons (FG2AG two_roots_ForestGr))).
  apply (is_ilist_rel _ _ _ h1).
  intro i.
  simpl in *|-*.
  rewrite <- decode_Fin_match'.
  elim (zerop (decode_Fin i)) ; intros a.
  rewrite (decode_Fin_0_first _ a).
  apply Geq_intro.
  reflexivity.
  simpl.
  assert (h2 := refl_equal _ : 
  lgti (icons (mk_Graph (Some 0) (inil (AllGraph nat))) (inil (AllGraph nat))) = 
  lgti (imap (@G2AG _)(icons (mk_Graph 0 (inil (Graph nat))) (inil (Graph nat))))).
  apply (is_ilist_rel _ _ _ h2).
  simpl in *|-*.
  intro i'.
  rewrite <- (decode_Fin_unique _ _ (decode_Fin_match' i' h2)).
  rewrite (Fin_first_1 i').
  apply Geq_intro.
  reflexivity.
  simpl.
  assert (h3 := refl_equal _ : lgti (inil (AllGraph nat)) = lgti (imap (@G2AG _) (inil (Graph nat)))).
  apply (is_ilist_rel _ _ _ h3).
  intro i'' ; inversion i''.
  
  assert (h2 : i = succ (first 0)).
  apply decode_Fin_unique.
  apply symmetry, (le_antisym _ _ (lt_le_S _ _ a) (lt_n_Sm_le _ _ (decode_Fin_inf_n i))).
  rewrite h2 ; clear h2.
  simpl.
  apply Geq_intro.
  reflexivity.
  simpl.
  assert (h2 := refl_equal _ : 
  lgti (icons (mk_Graph (Some 0) (inil (AllGraph nat))) (inil (AllGraph nat))) = 
  lgti (imap (@G2AG _)(icons (mk_Graph 0 (inil (Graph nat))) (inil (Graph nat))))).
  apply (is_ilist_rel _ _ _ h2).
  simpl in *|-*.
  intro i'.
  rewrite <- (decode_Fin_unique _ _ (decode_Fin_match' i' h2)).
  rewrite (Fin_first_1 i').
  apply Geq_intro.
  reflexivity.
  simpl.
  assert (h3 := refl_equal _ : lgti (inil (AllGraph nat)) = lgti (imap (@G2AG _) (inil (Graph nat)))).
  apply (is_ilist_rel _ _ _ h3).
  intro i'' ; inversion i''.
Qed.

























