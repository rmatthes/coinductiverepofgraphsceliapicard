(** GPermBij.v Version 1.1.1 April 2016 *)
(** runs under V8.5pl1 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of various relations using permutations
    based on a bijective function on 
    Graphs and equivalence proofs with associated tools and lemmas *)

Require Import Fin.
Require Import Ilist.
Require Import IlistPerm.
Require Import Graphs.
Require Import GPerm.
Require Import Tools.

Require Import Setoid.
Require Import Utf8.
Require Import Basics.

Set Implicit Arguments.

Section GeqPerm2.
  Variable T : Set.
  Variable RelT : relation T.
  
  CoInductive GeqPerm2 : relation (Graph T) :=
    GeqPerm2_intro: forall g1 g2, RelT (label g1) (label g2) -> 
    IlistPerm7 GeqPerm2 (sons g1) (sons g2) -> GeqPerm2 g1 g2.
    
  Lemma GeqPerm2_refl (Rrefl : Reflexive RelT) : forall g, GeqPerm2 g g.
  Proof.
    cofix Hc ; intros g.
    apply GeqPerm2_intro.
    reflexivity.
    apply (@perm7 _ _ _ _ (fun x => x) (fun x => x)).
    split ; reflexivity.
    intro i.
    apply Hc.
  Qed.
  
  Lemma GeqPerm2_sym(Rsym : Symmetric RelT): forall g1 g2, GeqPerm2 g1 g2 -> GeqPerm2 g2 g1.
  Proof.
    cofix Hc.
    intros _ _ [g1 g2 h1 [f g h2 h3]].
    apply GeqPerm2_intro ; simpl in *|-*.
    symmetry ; assumption.
    apply (perm7 _ _ _ (Bij_sym h2)).
    intro i.
    apply Hc.
    destruct h2 as [_ h2].
    rewrite <- (h2 i) at 2.
    apply h3.
  Qed.

  Lemma GeqPerm2_trans(Rtrans : Transitive RelT): 
    forall g1 g2 g3, GeqPerm2 g1 g2 -> GeqPerm2 g2 g3 -> GeqPerm2 g1 g3.
  Proof.
    cofix Hc.
    intros g1 g2 g3 h1 h2.
    destruct h1 as [g1 g2 h1 [f1 gg1 h3 h4]].
    destruct h2 as [g2 g3 h2 [f2 gg2 h5 h6]].
    apply GeqPerm2_intro ; simpl in *|-*.
    transitivity (label g2) ; assumption.
    
    apply (perm7 _ _ _ (Bij_trans h3 h5)).
    intros i.
    apply (Hc _ (fcti (sons g2) (f1 i)) _ (h4 _) (h6 _)).
  Qed.
  
  Add Parametric Relation (Req: Equivalence RelT): (Graph T)(GeqPerm2) 
    reflexivity proved by (GeqPerm2_refl _)
    symmetry proved by (GeqPerm2_sym _)
    transitivity proved by (GeqPerm2_trans _)
  as GeqPerm2Rel.

  (* the Mendler-style variant - see Nakata and Uustalu, SOS'10 *)
  CoInductive GeqPerm1' : relation (Graph T) :=
    GeqPerm1'_intro: forall g1 g2 (X: relation (Graph T)), subrelation X GeqPerm1' -> 
      RelT (label g1) (label g2) -> IlistPerm7 X (sons g1) (sons g2) -> GeqPerm1' g1 g2.
      
  Lemma subrelation_trans (U: Set)(R1 R2 R3 : relation U): 
    subrelation R1 R2 -> subrelation R2 R3 -> subrelation R1 R3.
  Proof.
    intros h1 h2 u1 u2 h3.
    apply (h2 _ _ (h1 _ _ h3)).
  Qed.
  
  Lemma GeqPerm1'_GeqPerm2: subrelation GeqPerm1' GeqPerm2.
  Proof.
    cofix Hc.
    intros _ _ [g1 g2 R h1 h2 [f g h3 h4]].
    apply GeqPerm2_intro.
    assumption.
    apply (perm7 _ _ _ h3).
    intro i.
    apply Hc, h1, h4.
  Qed.
  
  Lemma GeqPerm2_GeqPerm1': subrelation GeqPerm2 GeqPerm1'.
  Proof.
    cofix Hc.
    intros _ _ [g1 g2 h1 h2].
    apply (GeqPerm1'_intro _ _ Hc) ; assumption.
  Qed.
  
  Lemma GeqPerm0_GeqPerm1': subrelation (GeqPerm0 RelT) GeqPerm1'.
  Proof.
    cofix Hc.
    intros _ _ [g1 g2 h1 h2] .
    apply (GeqPerm1'_intro _ _ Hc).
    assumption.
    apply IlistPerm3_IlistPerm7, h2.
  Qed.

  Lemma GeqPerm0_GeqPerm2: subrelation (GeqPerm0 RelT) GeqPerm2.
  Proof.
    apply (subrelation_trans GeqPerm0_GeqPerm1' GeqPerm1'_GeqPerm2).
  Qed.
  
  Lemma GeqPerm1'_GeqPerm1: subrelation GeqPerm1' (GeqPerm1 RelT).
  Proof.
    cofix Hc.
    intros _ _ [g1 g2 R h1 h2 h3] .
    apply (GeqPerm1_intro _ _ Hc).
    assumption.
    apply IlistPerm7_IlistPerm3.
    apply (IlistPerm7_mon h1), h3.
  Qed.
  
  Lemma GeqPerm1_GeqPerm1': subrelation (GeqPerm1 RelT) GeqPerm1'.
  Proof.
    cofix Hc.
    intros _ _ [g1 g2 R h1 h2 h3] .
    apply (GeqPerm1'_intro _ _ Hc).
    assumption.
    apply IlistPerm3_IlistPerm7.
    apply (IlistPerm3_mon h1), h3.
  Qed.
  
  Lemma GeqPerm_GeqPerm2: subrelation (GeqPerm RelT) GeqPerm2.
  Proof.
    intros g1 g2 h.
    apply GeqPerm1'_GeqPerm2, GeqPerm1_GeqPerm1', GeqPerm_GeqPerm1, h.
  Qed.
  
  Lemma GeqPerm2_GeqPerm: subrelation GeqPerm2 (GeqPerm RelT).
  Proof.
    intros g1 g2 h.
    apply GeqPerm1_GeqPerm, GeqPerm1'_GeqPerm1, GeqPerm2_GeqPerm1', h.
  Qed.
  
  (* direct proof by R.M.: *)
  Lemma GeqPerm2_GeqPerm_ALT: subrelation GeqPerm2 (GeqPerm RelT).
  Proof.
    red.
    apply GeqPerm_coind.
    intros _ _ [g1 g2 H1 H2].
    apply IlistPerm7_IlistPerm3 in H2.
    split; assumption.
  Qed.
      
  Lemma GeqPerm0_GeqPerm2_ALT: subrelation (GeqPerm0 RelT) GeqPerm2.
  Proof.
    intros g1 g2 H.
    apply GeqPerm_GeqPerm2.
    apply GeqPerm0_GeqPerm.
    assumption.
  Qed. 
End GeqPerm2.