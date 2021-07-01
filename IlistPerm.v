(** IlistPerm.v Version 1.1 February 2011 *)
(** runs under V8.3, tested with 8.3pl2 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of various relations of permutation 
    on ilist with associated tools and lemmas *)

Require Import Fin.
Require Import Ilist. 
Require Import Setoid.
Require Import Extroduce. 
Require Import Utf8.
Require Import Basics.
Require Import Morphisms.
Require Import Tools.

Set Implicit Arguments. 

(* this section corresponds to the developments around ilist_perm_occ in the paper (section 2.1) *)
Section Ilist_Perm_occ.

  Fixpoint count_occn (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(t: T)(n: nat)
    (i: ilistn T n){struct n} : nat := 
    match n as m return (ilistn T m -> nat) with 
      0 => fun _: ilistn T 0 => 0 
    | S m => fun i0: ilistn T (S m) =>  
    if (R_dec t (i0 (first m))) then
        S (count_occn RelT R_dec t (fun f => i0 (succ f)))
        else (count_occn RelT R_dec t (fun f => i0 (succ f)))
      end i.

  (* Counts number of occurrences of t in i *)
  (* called nb_occ in the paper - Definition 7 *)
  Definition count_occ(T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(t: T)(i: ilist T) : nat := 
     let (n, i') := i  in count_occn RelT R_dec t i'.

  Add Parametric Morphism (T: Set)(RelT: relation T)(RelTEq: Equivalence RelT)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(t: T): 
    (count_occ RelT R_dec t)
  with signature (ilist_rel RelT ==> @eq nat)
  as count_occM1.
  Proof.
    intros [n1 i1] [n2 i2] [h H].
    simpl in h, H.
    assert (h' := h) ; revert i2 h H ; rewrite <- h' ; intros i2 h H ; clear h' n2.
    fold (mkilist i1); fold (mkilist i2).
    assert (e1: forall f, f = rewriteFins h f).
    intro f.
    apply decode_Fin_unique, decode_Fin_match'.
    assert (H': forall f, RelT (i1 f) (i2 f)).
    intro f ; rewrite (e1 f) at 2 ; apply H. 
    clear h H e1.
    simpl.
    induction n1 as [|n IH].
    reflexivity.
    simpl.
    destruct RelTEq as [Rrefl Rsym Rtrans].
    elim (R_dec t (i1 (first n))) ; intros a ;
    elim (R_dec t (i2 (first n))) ; intros c ;
    rewrite (IH _ (fun f : Fin n => i2 (succ f)));
    try reflexivity ; 
    try (intro f ; apply H') ; 
    try assert (b := Rtrans _ _ _ a (H' (first n))) ; 
    try assert (b := Rtrans _ _ _ c (Rsym _ _ (H' (first n)))) ;
    contradiction b.
  Qed.

  (* Indicates whether an ilist is a permutation of another using decidability *)
  (* Called ilist_perm_occ in the paper - Definition 8 *)
  Inductive IlistPerm (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(i1 i2: ilist T): Prop :=
    is_IlistPerm: (forall t: T,
      count_occ RelT R_dec t i1 = 
      count_occ RelT R_dec t i2) -> 
        IlistPerm RelT R_dec i1 i2.

  Lemma count_occn_in (T: Set)(RelT: relation T)(Req: Equivalence RelT)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(n: nat)(l : ilistn T n)(i: Fin n) : 
     exists m, count_occn RelT R_dec (l i) l = S m.
  Proof.
    induction i.
    simpl.
    elim (R_dec (l (first k)) (l (first k))) ; intros a.
    exists (count_occn RelT R_dec (l (first k)) (fun f : Fin k => l (succ f))).
    reflexivity.
    unfold not in a.
    contradiction a.
    reflexivity.
    simpl.
    elim (R_dec (l (succ i)) (l (first k))) ; intros a.
    exists (count_occn RelT R_dec (l (succ i)) (fun f : Fin k => l (succ f))).
    reflexivity.
    destruct (IHi (fun f : Fin k => l (succ f))) as [m H].
    exists m.
    apply H.
  Qed.

  Lemma count_occn_not_exist (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(n: nat)(l : ilistn T n)(t: T): 
     not (exists i: Fin n, RelT t (l i)) -> count_occn RelT R_dec t l = 0.
   Proof.
     intros H.
     induction n as [|n IH].
     reflexivity.
     simpl.
     elim (R_dec t (l (first n))) ; intros a.
     destruct H.
     exists (first n) ; assumption.
     apply IH.
     intros [f H'].
     destruct H.
     exists (succ f) ; assumption.
   Qed.

  Lemma count_occn_exist (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(n: nat)(l : ilistn T n)(t: T)(m: nat): 
     count_occn RelT R_dec t l = S m -> exists i: Fin n, RelT t (l i).
   Proof.
     intro H.
     induction n as [|n IH].
     inversion H.
     simpl in H.
     revert H.
     elim (R_dec t (l (first n))) ; simpl ; intros a H.
     exists (first n) ; assumption.
     destruct (IH (fun x => l (succ x)) H) as [f H'].
     exists (succ f) ; assumption.
   Qed.

  Lemma IlistPerm_refl: forall (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(i1: ilist T), 
    IlistPerm RelT R_dec i1 i1.
  Proof.
    intros T RelT R_dec i1.
    apply is_IlistPerm.
    reflexivity.
  Qed.

  Lemma IlistPerm_sym: forall (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(i1 i2: ilist T),
    IlistPerm RelT R_dec i1 i2 -> IlistPerm RelT R_dec i2 i1.
  Proof.
    intros T RelT Req i1 i2 [H].
    apply is_IlistPerm.
    intro t.
    apply (sym_eq (H t)).
  Qed.

  Lemma IlistPerm_trans: forall (T: Set)(RelT: relation T)
    (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(i1 i2 i3: ilist T),
    IlistPerm RelT R_dec i1 i2 -> IlistPerm RelT R_dec i2 i3 -> 
    IlistPerm RelT R_dec i1 i3.
  Proof.
    intros T RelT R_dec i1 i2 i3 [H1] [H2].
    apply is_IlistPerm.
    intro t.
    apply (trans_eq (H1 t) (H2 t)).
  Qed.
   
    Add Parametric Relation(T: Set)(RelT: relation T)
      (R_dec: forall x y, {RelT x y}+{not (RelT x y)}): 
      (ilist T) (@IlistPerm T RelT R_dec)
      reflexivity proved by (@IlistPerm_refl T RelT R_dec)
      symmetry proved by (@IlistPerm_sym T RelT R_dec)
      transitivity proved by (@IlistPerm_trans T RelT R_dec)
      as IlistPermRel.

   Add Parametric Morphism (T: Set)(RelT: relation T)(REq: Equivalence RelT)
      (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(i: ilist T): 
      (fun x => count_occ RelT R_dec x i)
   with signature (RelT ==> @eq nat)
   as count_occM2.
   Proof.
     intros t1 t2 H.
     destruct i as [n i].
     simpl.
     induction n as [|n IH].
     reflexivity.
     simpl.
     destruct REq as [Rrefl Rsym Rtrans].
     elim (R_dec t1 (i (first n))) ; intros a ;
     elim (R_dec t2 (i (first n))) ; intros b ;
     try (rewrite IH ; reflexivity); 
     try assert (c := Rtrans _ _ _ (Rsym _ _ H) a) ;
     try assert (c := Rtrans _ _ _ H b) ;
     contradiction c.
   Qed.

   Lemma ilist_rel_finer_IlistPerm: 
     forall (T: Set)(RelT: relation T) (REq : Equivalence RelT)
       (R_dec: forall x y, {RelT x y}+{not (RelT x y)})(i1 i2: ilist T), 
     ilist_rel RelT i1 i2 -> IlistPerm RelT R_dec i1 i2.
   Proof.
     intros T RelT [Rrefl Rsym Rtrans] R_dec [n i1] [n2 i2] [h H].
     apply is_IlistPerm.
     intros t.
     simpl in *|-*.
     assert (h' := h) ; revert i1 i2 h H ; rewrite <- h' ; intros i1 i2 h H ; clear h' n2.
     assert (H1 : forall f, RelT (i1 f) (i2 f)).
     intro f.
     rewrite (decode_Fin_unique _ _ (decode_Fin_match' f h)) at 2.
     apply (H f).
     clear H h.

     induction n as [|n IH].
     reflexivity.
     simpl.
     elim (R_dec t (i1 (first n))) ; elim (R_dec t (i2 (first n))) ; intros a b.
     f_equal ; apply IH.
     intro f ; apply (H1 (succ f)).
     contradiction (Rtrans _ _ _ b (H1 (first n))).
     contradiction (Rtrans _ _ _ a (Rsym _ _ (H1 (first n)))).
     apply IH.
     intro f ; apply (H1 (succ f)).
   Qed.
End Ilist_Perm_occ.

Section IlistPerm_ind.

   (* In the paper, iperm *)
   Inductive IlistPerm3 (T: Set)(RelT: relation T)(i1 i2: ilist T): Prop :=
     IlistPerm3_nil: lgti i1 = lgti i2 -> lgti i1 = 0 -> IlistPerm3 RelT i1 i2  
   | IlistPerm3_cons: forall f1 f2, RelT (fcti i1 f1) (fcti i2 f2) -> 
        IlistPerm3 RelT (extroduce i1 f1) (extroduce i2 f2) -> 
        IlistPerm3 RelT i1 i2.

   (* In the paper, iperm' *)
   Inductive IlistPerm4 (T: Set)(RelT: relation T): ilist T-> ilist T-> Prop :=
     is_IlistPerm4: forall (i1 i2: ilist T), lgti i1 = lgti i2 -> 
       (forall f1, exists f2, RelT (fcti i1 f1) (fcti i2 f2) /\
        IlistPerm4 RelT (extroduce i1 f1) (extroduce i2 f2)) -> 
        IlistPerm4 RelT i1 i2.

   Scheme IlistPerm4_ind_rich := Induction for IlistPerm4 Sort Prop.

   Lemma IlistPerm4_ind_better : forall (T : Set)(RelT : relation T)(P : ilist T -> ilist T -> Prop), 
     (forall i1 i2 : ilist T, lgti i1 = lgti i2 -> 
       (forall f1 : Fin (lgti i1), exists f2 : Fin (lgti i2),
       RelT (fcti i1 f1) (fcti i2 f2) /\ IlistPerm4 RelT (extroduce i1 f1) (extroduce i2 f2) /\
       P (extroduce i1 f1) (extroduce i2 f2)) -> P i1 i2)
       -> (forall i i0 : ilist T, IlistPerm4 RelT i i0 -> P i i0).
   Proof.
     intros T RelT P H.
     refine (fix Hr (i00 i0: ilist T)(h: IlistPerm4 RelT i00 i0){struct h} : P i00 i0 := 
       match h with is_IlistPerm4 i1 i2 h1 h2 => _ end).
     clear i00 i0 h.
     apply H.
     assumption.
     intro f1.
     destruct (h2 f1) as [f2 [h3 h4]].
     exists f2.
     split ; try split ; try assumption.
     apply (Hr _ _ h4).
   Qed.
   
   Inductive IlistPerm5 (T: Set)(RelT: relation T): ilist T -> ilist T -> Prop :=
     is_IlistPerm5: forall (i1 i2: ilist T), lgti i1 = lgti i2 -> 
       (forall f2, exists f1, RelT (fcti i1 f1) (fcti i2 f2) /\
        IlistPerm5 RelT (extroduce i1 f1) (extroduce i2 f2)) -> 
        IlistPerm5 RelT i1 i2.

   Lemma IlistPerm5_ind_better : forall (T : Set)(RelT : relation T)(P : ilist T → ilist T → Prop), 
     (forall i1 i2 : ilist T, lgti i1 = lgti i2 -> 
       (forall f2 : Fin (lgti i2), exists f1 : Fin (lgti i1),
       RelT (fcti i1 f1) (fcti i2 f2) /\ IlistPerm5 RelT (extroduce i1 f1) (extroduce i2 f2) /\
       P (extroduce i1 f1) (extroduce i2 f2)) -> P i1 i2)
       -> (forall i i0 : ilist T, IlistPerm5 RelT i i0 -> P i i0).
   Proof.
     intros T RelT P H.
     refine (fix Hr (i00 i0: ilist T)(h: IlistPerm5 RelT i00 i0){struct h} : P i00 i0 := 
       match h with is_IlistPerm5 i1 i2 h1 h2 => _ end).
     clear i00 i0 h.
     apply H.
     assumption.
     intro f2.
     destruct (h2 f2) as [f1 [h3 h4]].
     exists f1.
     split ; try split ; try assumption.
     apply (Hr _ _ h4).
   Qed.

   Lemma IlistPerm3_lgti: forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm3 RelT i1 i2 -> lgti i1 = lgti i2.
   Proof.
     intros T RelT i1 i2 H.
     induction H as [i1 i2 h1 h2 | i1 i2 f1 f2 h1 h2 IH].
     assumption.
     apply eq_S in IH.
     do 2 rewrite <- extroduce_lgti in IH.
     assumption.
   Qed.

   (* D2 => D1 *)
   Lemma IlistPerm4_IlistPerm3_eq : forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm4 RelT i1 i2 -> IlistPerm3 RelT i1 i2.
   Proof.
     intros T RelT i1 i2 h.
     induction h as [i1 i2 h1 h2] using IlistPerm4_ind_better.
     destruct i1 as [n1 i1]; destruct i2 as [n2 i2].
     simpl lgti in h1, h2 ; simpl fcti in h2.
     fold (mkilist i1) in *|-*.
     fold (mkilist i2) in *|-*.
     destruct n1 as [|n1].
     apply IlistPerm3_nil.
     assumption.
     reflexivity.
     destruct (h2 (first n1)) as [f2 [h3 [h4 h5]]] ; clear h2.
     clear h4.
     apply (IlistPerm3_cons _ _ (first _: Fin (lgti (mkilist _))) 
       (f2: Fin (lgti (mkilist _)))) ; assumption.
     Qed.
     
   Lemma IlistPerm5_IlistPerm3_eq : forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm5 RelT i1 i2 -> IlistPerm3 RelT i1 i2.
   Proof.
     intros T RelT i1 i2 h.
     induction h as [i1 i2 h1 h2] using IlistPerm5_ind_better.
     destruct i1 as [n1 i1]; destruct i2 as [n2 i2].
     simpl lgti in h1, h2 ; simpl fcti in h2.
     fold (mkilist i1) in *|-*.
     fold (mkilist i2) in *|-*.
     destruct n2 as [|n2].
     apply IlistPerm3_nil ; assumption.
     destruct (h2 (first n2)) as [f1 [h3 [h4 h5]]] ; clear h2.
     clear h4.
     apply (IlistPerm3_cons _ _ (f1 : Fin (lgti (mkilist _))) 
       (first _: Fin (lgti (mkilist _)))) ; assumption.
    Qed.

   Lemma IlistPerm4_refl_refl: forall (T: Set)(RelT: relation T)(Rrefl: Reflexive RelT)(i: ilist T),
     IlistPerm4 RelT i i.
   Proof.
     intros T RelT Rrefl [n i].
     induction n as [|n IH] ;
     apply (is_IlistPerm4 _ _ (refl_equal _)) ;
     simpl lgti ; simpl fcti ;
     intro f ; exists f.
     inversion f.
     split.
     reflexivity.
     set (e := extroduce (existT (fun n0 : nat => ilistn T n0) (S n) i) f).
     assert (h:= extroduce_lgti_S _ _ : n = lgti e).
     destruct e as [n' e].
     simpl in h ; revert e ; rewrite <- h ; intro e ; apply IH.
   Qed.

   Lemma IlistPerm4_refl: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(i: ilist T),
     IlistPerm4 RelT i i.
   Proof.
     intros T RelT [Rrefl _ _] [n i].
     induction n as [|n IH] ;
     apply (is_IlistPerm4 _ _ (refl_equal _)) ;
     simpl lgti ; simpl fcti ;
     intro f ; exists f.
     inversion f.
     split.
     apply Rrefl.
     set (e := extroduce (existT (fun n0 : nat => ilistn T n0) (S n) i) f).
     assert (h: lgti e = n).
     apply eq_add_S.
     unfold e.
     rewrite <- extroduce_lgti.
     reflexivity.
     destruct e as [n' e].
     simpl in h ; revert e ; rewrite h ; intro e ; apply IH.
   Qed.

   (* Deduced from IlistPerm4_refl *)
   Lemma IlistPerm3_refl_refl: forall (T: Set)(RelT: relation T)(Rrefl: Reflexive RelT)(i: ilist T),
     IlistPerm3 RelT i i.
   Proof.
     intros T RelT Rrefl i.
     apply IlistPerm4_IlistPerm3_eq.
     apply (IlistPerm4_refl_refl Rrefl).
   Qed.

   (* Deduced from IlistPerm4_refl *)
   Lemma IlistPerm3_refl: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(i: ilist T),
     IlistPerm3 RelT i i.
   Proof.
     intros T RelT EqT i.
     apply IlistPerm4_IlistPerm3_eq.
     apply (IlistPerm4_refl EqT).
   Qed.

   Lemma IlistPerm3nil: forall (T: Set)(RelT: relation T)(i1 i2: ilistn T 0), 
     IlistPerm3 RelT (mkilist (n:=0) i1) (mkilist (n:=0) i2).
   Proof.
     intros T RelT i1 i2.
     apply IlistPerm3_nil ; reflexivity.
   Qed.

   Lemma IlistPerm4nil: forall (T: Set)(RelT: relation T)(i1 i2: ilistn T 0), 
     IlistPerm4 RelT (mkilist (n:=0) i1) (mkilist (n:=0) i2).
   Proof.
     intros T RelT i1 i2.
     apply is_IlistPerm4.
     reflexivity.
     intro f1 ; inversion f1.
   Qed.

   Lemma IlistPerm4nil_gen: forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     lgti i1 = lgti i2 -> lgti i1 = 0 ->
     IlistPerm4 RelT i1 i2.
   Proof.
     intros T RelT i1 i2 Hyp1 Hyp2.
     apply is_IlistPerm4.
     exact Hyp1.
     intro f1.
     apply False_rec.
     rewrite Hyp2 in f1.
     inversion f1.
   Qed.

   Lemma IlistPerm4_lgti: forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm4 RelT i1 i2 -> lgti i1 = lgti i2.
   Proof.
     intros T RelT _ _ [i1 i2 e1 _] ; assumption.
   Qed.

   Lemma IlistPerm3_flip: forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm3 RelT i1 i2 -> IlistPerm3 (flip RelT) i2 i1.
   Proof.
     intros T RelT i1 i2 ; intros h ;
     induction h as [i1 i2 e1 e2 | i1 i2 f1 f2 h1 _ IH].
     apply (IlistPerm3_nil _ _ _ (sym_eq e1) (trans_eq (sym_eq e1) e2)).
     apply (IlistPerm3_cons _ _ f2 f1) ; assumption.
   Qed.

   Lemma IlistPerm3_flip': forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm3 (flip RelT) i1 i2 -> IlistPerm3 RelT i2 i1.
   Proof.
     intros T RelT i1 i2 ; intros h ;
     induction h as [i1 i2 e1 e2 | i1 i2 f1 f2 h1 h2 IH].
     apply (IlistPerm3_nil _ _ _ (sym_eq e1) (trans_eq (sym_eq e1) e2)).
     apply (IlistPerm3_cons _ _ f2 f1); assumption.
   Qed.

   (* using IlistPerm3_flip *)
   Lemma IlistPerm3_sym: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(i1 i2: ilist T), 
     IlistPerm3 RelT i1 i2 -> IlistPerm3 RelT i2 i1.
   Proof.
     intros T RelT [_ Rsym _] i1 i2 h.
     assert (h1 := IlistPerm3_flip h) ; clear h.
     induction h1 as  [i2 i1 e1 e2 | i2 i1 f2 f1 h1 _ IH].
     apply (IlistPerm3_nil _ _ _ e1 e2).
     apply (IlistPerm3_cons _ _ f2 f1).
     apply (Rsym _ _ h1).
     assumption.
   Qed.

   Lemma IlistPerm3_sym_sym: forall (T: Set)(RelT: relation T)(Rsym: Symmetric RelT)(i1 i2: ilist T), 
     IlistPerm3 RelT i1 i2 -> IlistPerm3 RelT i2 i1.
   Proof.
     intros T RelT Rsym i1 i2 h.
     assert (h1 := IlistPerm3_flip h) ; clear h.
     induction h1 as  [i1 i2 e1 e2 | i1 i2 f1 f2 h1 h2 IH].
     apply (IlistPerm3_nil _ _ _ e1 e2).
     apply (IlistPerm3_cons _ _ f1 f2).
     apply (Rsym _ _ h1).
     assumption.
   Qed.

   Definition TransitiveAt (T: Type)(R: relation T)(t1: T): Prop :=
     forall (t2 t3: T), R t1 t2 -> R t2 t3 -> R t1 t3.

   Lemma IlistPerm4_trans_refined: 
     forall (T: Set)(RelT: relation T)(i1: ilist T), 
     (forall f1: Fin (lgti i1), TransitiveAt RelT (fcti i1 f1)) ->
     TransitiveAt (IlistPerm4 RelT) i1.
   Proof.
    intros T RelT i1 Hyp i2 i3 h1 h2.
    revert i1 h1 Hyp.
    induction h2 as [i2 i3 e2 h2] using IlistPerm4_ind_better.
    intros i1 h1 Hyp.
    destruct h1 as [i1 i2 e1 h1].
    apply is_IlistPerm4.
    apply (trans_eq e1 e2).
    intro f1.
    destruct (h1 f1) as [f2 [h11 h12]] ; clear h1.
    destruct (h2 f2) as [f3 [h21 [h22 h23]]] ; clear h2.
    exists f3.
    split.
    apply (Hyp _ _ _ h11 h21).
    apply (h23 _ h12).
    intro f0.
    destruct (extroduce_ok_cor i1 f1 f0).
    rewrite H.
    apply Hyp.
   Qed.

(* obviously, the following lemma is just a special case *)
   Lemma IlistPerm4_trans: 
     forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(i1 i2 i3: ilist T), 
     IlistPerm4 RelT i1 i2 -> IlistPerm4 RelT i2 i3 -> IlistPerm4 RelT i1 i3.
   Proof.
     intros T RelT [_ _ Rtrans] i1.
     change (TransitiveAt (IlistPerm4 RelT) i1).
     apply IlistPerm4_trans_refined.
     red.
     intros.
     transitivity t2; assumption.
   Qed.

   Lemma IlistPerm4_trans_trans: 
     forall (T: Set)(RelT: relation T)(Rtrans: Transitive RelT)(i1 i2 i3: ilist T), 
     IlistPerm4 RelT i1 i2 -> IlistPerm4 RelT i2 i3 -> IlistPerm4 RelT i1 i3.
   Proof.
     intros T RelT Rtrans i1.
     change (TransitiveAt (IlistPerm4 RelT) i1).
     apply IlistPerm4_trans_refined.
     intros f1 t2 t3 H1 H2.
     transitivity t2; assumption.
   Qed.

   Lemma IlistPerm4_flip_IlistPerm5 : forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm4 RelT i1 i2 -> IlistPerm5 (flip RelT) i2 i1.
   Proof.
     intros T RelT i1 i2 H.
     induction H as [i1 i2 h1 h2] using IlistPerm4_ind_better.
     apply (is_IlistPerm5 _ _ (sym_eq h1)).
     intro f1.
     destruct (h2 f1) as [f2 [h3 [_ h4]]].
     exists f2.
     split ; assumption.
   Qed.

   Lemma IlistPerm4_sym_IlistPerm5 : forall (T: Set)(RelT: relation T)(Rsym: symmetric _ RelT)
     (i1 i2: ilist T), IlistPerm4 RelT i1 i2 -> IlistPerm5 RelT i2 i1.
   Proof.
     intros T RelT Rsym i1 i2 h.
     assert (h1:= IlistPerm4_flip_IlistPerm5 h) ; clear h.
     induction h1 as [i1 i2 h1 h2] using IlistPerm5_ind_better.
     apply (is_IlistPerm5 _ _ h1).
     intro f2.
     destruct (h2 f2) as [f1 [h3 [_ h4]]].
     exists f1.
     split.
     apply (Rsym _ _ h3).
     assumption.
   Qed.

   Lemma IlistPerm5_flip_IlistPerm4 : forall (T: Set)(RelT: relation T)(i1 i2: ilist T), 
     IlistPerm5 RelT i1 i2 -> IlistPerm4 (flip RelT) i2 i1.
   Proof.
     intros T RelT i1 i2 H.
     induction H as [i1 i2 h1 h2] using IlistPerm5_ind_better.
     apply (is_IlistPerm4 _ _ (sym_eq h1)).
     intro f1.
     destruct (h2 f1) as [f2 [h3 [_ h4]]].
     exists f2.
     split ; assumption.
   Qed.

   Lemma IlistPerm5_sym_IlistPerm4 : forall (T: Set)(RelT: relation T)(Rsym: symmetric _ RelT)
     (i1 i2: ilist T), IlistPerm5 RelT i1 i2 -> IlistPerm4 RelT i2 i1.
   Proof.
     intros T RelT Rsym i1 i2 h.
     assert (h1:= IlistPerm5_flip_IlistPerm4 h) ; clear h.
     induction h1 as [i1 i2 h1 h2] using IlistPerm4_ind_better.
     apply (is_IlistPerm4 _ _ h1).
     intro f2.
     destruct (h2 f2) as [f1 [h3 [_ h4]]].
     exists f1.
     split.
     apply (Rsym _ _ h3).
     assumption.
   Qed.

   (* deduced from IlistPerm4_refl *)
   Lemma IlistPerm5_refl: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(i: ilist T),
     IlistPerm5 RelT i i.
   Proof.
     intros T RelT EqT i.
     apply IlistPerm4_sym_IlistPerm5.
     destruct EqT as [_ Rsym _] ; assumption.
     apply (IlistPerm4_refl EqT).
   Qed.

   (* Proof by induction on IlistPerm4 *)
   Lemma IlistPerm4_ilist_rel: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)
     (i1 i1' i2 : ilist T), ilist_rel RelT i1 i1' -> IlistPerm4 RelT i1 i2 -> 
     IlistPerm4 RelT i1' i2.
   Proof.
     intros T RelT EqT i1 i1' i2 h1 h2.
     apply (ilist_rel_sym _) in h1.
     revert i1' h1.
     induction h2 as [i1 i2 e2 h2] using IlistPerm4_ind_better ; intros i1' h1.
     destruct h1 as [e1 h1'].
     apply (is_IlistPerm4 _ _ (trans_eq e1 e2)).
     intro f1.
     destruct (h2 (rewriteFins e1 f1)) as [f3 [h3 [h4 IH]]].
     exists f3.
     split.
     destruct EqT as [_ _ Rtrans].
     apply (Rtrans _ _ _ (h1' f1) h3).
     apply IH.
     assert (h : lgti (extroduce i1' f1) = lgti (extroduce i1 (rewriteFins e1 f1))).
     evalLgtiExtro.
     assumption.
     apply (is_ilist_rel _ _ _ h).
     intro f.
     elim (le_lt_dec (decode_Fin f1) (decode_Fin f)) ; intros a.
     rewrite extroduce_ok3' ; try assumption.
     rewrite extroduce_ok3' by (treatFin a).
     assert (h5: rewriteFins (sym_eq (extroduce_lgti i1 (rewriteFins e1 f1))) (succ (rewriteFins h f)) =
                 rewriteFins e1 (rewriteFins (sym_eq (extroduce_lgti i1' f1)) (succ f))).
     treatFinPure.
     rewrite h5.
     apply h1'.

     rewrite extroduce_ok2' ; try assumption.
     rewrite extroduce_ok2' by (treatFin a).
     assert (h5: rewriteFins (sym_eq (extroduce_lgti i1 (rewriteFins e1 f1)))
        (weakFin (rewriteFins h f)) = rewriteFins e1
        (rewriteFins (sym_eq (extroduce_lgti i1' f1)) (weakFin f))).
     treatFinPure.
     rewrite h5.
     apply h1'.
   Qed.

   (* Proof with induction on IlistPerm3 *)
   Lemma IlistPerm3_ilist_rel: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)
     (i1 i1' i2 : ilist T), ilist_rel RelT i1 i1' -> IlistPerm3 RelT i1 i2 -> 
     IlistPerm3 RelT i1' i2.
   Proof.
     intros T RelT EqT i1 i1' i2 h1 h2.
     revert i1' h1 ; induction h2 as [i1 i2 e2 e3 | i1 i2 f1 f2 e2 h2 IH] ; intros i1' [e1 h1].
     apply (IlistPerm3_nil _ _ _ (trans_eq (sym_eq e1) e2) (trans_eq (sym_eq e1) e3)).
     apply (IlistPerm3_cons _ _ (rewriteFins e1 f1) f2).
     destruct EqT as [_ Rsym Rtrans].
     apply (Rtrans _ _ _ (Rsym _ _ (h1 f1)) e2).
     apply IH.
     assert (h3: lgti (extroduce i1 f1) = lgti (extroduce i1' (rewriteFins e1 f1))).
     evalLgtiExtro.
     assumption.
     apply (is_ilist_rel _ _ _ h3).
     intro f.
     elim (le_lt_dec (decode_Fin f1) (decode_Fin f)) ; intros a.
(* continue as for IlistPerm4_ilist_rel (only variable names have changed) *)
     rewrite extroduce_ok3' ; try assumption.
     rewrite extroduce_ok3' by (treatFin a).
     assert (h4: rewriteFins (sym_eq (extroduce_lgti i1' (rewriteFins e1 f1))) (succ (rewriteFins h3 f)) =
                 rewriteFins e1 (rewriteFins (sym_eq (extroduce_lgti i1 f1)) (succ f))).
     treatFinPure.
     rewrite h4.
     apply h1.

     rewrite extroduce_ok2' ; try assumption.
     rewrite extroduce_ok2' by (treatFin a).
     assert (h5: rewriteFins (sym_eq (extroduce_lgti i1' (rewriteFins e1 f1)))
        (weakFin (rewriteFins h3 f)) = rewriteFins e1
        (rewriteFins (sym_eq (extroduce_lgti i1 f1)) (weakFin f))).
     treatFinPure.
     rewrite h5.
     apply h1.
   Qed.

   Lemma IlistPerm3_ilist_rel_eq: forall (T: Set)(RelT: relation T)(l1 l1' l2 : ilist T)
     (h: ilist_rel (@eq T) l1 l1'), IlistPerm3 RelT l1 l2 ->  IlistPerm3 RelT l1' l2.
   Proof.
     intros T RelT l1 l1' l2 h1 h2.
     revert l1' h1 ; induction h2 as [l1 l2 e2 e3 | l1 l2 i1 i2 e2 h2 IH] ; intros l1' h1 ;
     inversion h1 as [e1 h1'].
     apply (IlistPerm3_nil _ _ _ (trans_eq (sym_eq e1) e2) (trans_eq (sym_eq e1) e3)).
     apply (IlistPerm3_cons _ _ (rewriteFins e1 i1) i2).
     rewrite <- (h1' i1).
     assumption.
     apply IH.
     apply extroduce_ilist_rel_bis.
     assumption.
   Qed.

(* just a dual proof for the changes in the second argument *)
  Lemma IlistPerm3_ilist_rel_eq_snd: forall (T: Set)(RelT: relation T)(l1 l2 l2' : ilist T)
     (h: ilist_rel (@eq T) l2 l2'), IlistPerm3 RelT l1 l2 ->  IlistPerm3 RelT l1 l2'.
   Proof.
     intros T RelT l1 l1' l2 h1 h2.
     revert l2 h1 ; induction h2 as [l1 l2 e2 e3 | l1 l2 i1 i2 e2 h2 IH] ; intros l1' h1 ;
     inversion h1 as [e1 h1'].
     apply (IlistPerm3_nil _ _ _ (trans_eq e2 e1) e3).
     apply (IlistPerm3_cons _ _ i1 (rewriteFins e1 i2)).
     rewrite <- (h1' i2).
     assumption.
     apply IH.
     apply extroduce_ilist_rel_bis.
     assumption.
   Qed.

   Add Parametric Morphism (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(l: ilist T) : 
     (fun x => IlistPerm3 RelT x l)
   with signature (ilist_rel RelT ==> impl) as IlistPerm3M1_Eq.
   Proof.
     intros l2 l2' H2 H3.
     apply (IlistPerm3_ilist_rel EqT H2 H3).
   Qed.
     
   Add Parametric Morphism (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(l: ilist T) : 
     (IlistPerm3 RelT l)
   with signature (ilist_rel RelT ==> impl) as IlistPerm3M2_Eq.
   Proof.
     intros l1 l1' H2 H3.
     apply (IlistPerm3_sym EqT).
     apply (IlistPerm3_sym EqT) in H3.
     apply (IlistPerm3_ilist_rel EqT H2 H3).
   Qed.

   Add Parametric Morphism (T: Set)(RelT: relation T)(EqT: Equivalence RelT): 
     (IlistPerm3 RelT)
   with signature (ilist_rel RelT ==> ilist_rel RelT ==> impl) as IlistPerm3M_Eq.
   Proof.
     intros l1 l1' H1 l2 l2' H2 H3.
     apply (IlistPerm3M2_Eq EqT H2).
     apply (IlistPerm3M1_Eq EqT H1).
     assumption.
   Qed.

   Lemma ilist_rel_finer_IlistPerm3: forall (T: Set)(RelT: relation T)
     (i1 i2 : ilist T), ilist_rel RelT i1 i2 -> IlistPerm3 RelT i1 i2.
   Proof.
     intros T RelT [n l1] [n2 l2] H.
     inversion H as [h2 _].
     simpl in h2.
     revert l2 H ; rewrite <- h2 ; intros l2 H ; clear n2 h2.
     induction n as [|n IH].
     destruct H as [h H] ; simpl in *|-*.
     apply IlistPerm3_nil ; reflexivity.
     assert (i := first n).
     apply (IlistPerm3_cons _ _ (i: Fin (lgti (existT (fun n0 : nat => ilistn T n0) (S n) l1))) 
       (i: Fin (lgti (existT (fun n0 : nat => ilistn T n0) (S n) l2)))).
     destruct H as [h H].
     assert (H1: forall i, RelT (l1 i) (l2 i)).
     intro i'. 
     assert (h' : i' = rewriteFins h i').
     unfold rewriteFins; apply decode_Fin_unique, decode_Fin_match.
     rewrite h' at 2 ; apply (H i').
     clear h H.
     apply H1.
     assert (H1 := extroduce_ilist_rel i H).
     revert H1 ; unfold mkilist.
     set (l1' := extroduce (existT (fun n0 : nat => ilistn T n0) (S n) l1) i).
     set (l2' := extroduce (existT (fun n0 : nat => ilistn T n0) (S n) l2) i).
     intro H1.
     assert (h: lgti l1' = n).
     unfold l1' ; apply eq_add_S.
     rewrite <- extroduce_lgti.
     reflexivity.
     destruct l1' as [n' l1'] ; destruct l2' as [n2 l2'].
     inversion H1 as [h1 _].
     simpl in *|-*.
     revert l1' l2' H1.
     rewrite <- h1, h.
     apply IH.
   Qed.
  
   Lemma ilist_rel_finer_IlistPerm4: forall (T: Set)(RelT: relation T)
     (l1 l2 : ilist T), ilist_rel RelT l1 l2 -> IlistPerm4 RelT l1 l2.
   Proof.
     intros T RelT [n l1] [n2 l2] h.
     inversion h as [h2 _].
     simpl in h2.
     revert l2 h ; rewrite <- h2 ; intros l2 h ; clear n2 h2.
     fold (mkilist l1) (mkilist l2).
     induction n as [|n IH].
     apply IlistPerm4nil.
     apply (is_IlistPerm4 _ _ (refl_equal _ : lgti (mkilist l1) = lgti (mkilist l2))).
     intro i.
     inversion h as [e h'].
     simpl lgti in *|-* ; simpl fcti in *|-*.
     exists i.
     split.
     rewrite (decode_Fin_unique _ _ (decode_Fin_match' i e)) at 2.
     apply h'.
     assert (hex := extroduce_ilist_rel i h).
     revert hex.
     set (l1' := extroduce (mkilist l1) i) ; set (l2' := extroduce (mkilist l2) i) ; 
     assert (h1 := extroduce_lgti_S l1 i :n = lgti l1') ; assert (h2 := extroduce_lgti_S l2 i :n = lgti l2').
     destruct l1' as [n1 l1'] ; destruct l2' as [n2 l2'].
     simpl in h1, h2.
     revert l1' l2' ; rewrite <- h1, <- h2 ; clear n1 n2 h1 h2.
     apply IH.
   Qed.

   Lemma IlistPerm3_imap (T U: Set)(RelT: relation T)(RelU: relation U)
     (f: T -> U)(fM: Proper (RelT ==> RelU) f) (l1 l2: ilist T): 
     IlistPerm3 RelT l1 l2 -> IlistPerm3 RelU (imap f l1) (imap f l2).
   Proof.
     intro H ; induction H as [[n1 l1] [n2 l2] e1 e2 | l1 l2 i1 i2 h2 H IH].
     apply IlistPerm3_nil ; assumption.
     apply (IlistPerm3_cons _ _ (i1 : Fin (lgti(imap f l1))) (i2: Fin (lgti (imap f l2)))).
     simpl.
     apply fM, h2.
     apply (IlistPerm3_ilist_rel_eq (ilist_rel_sym _ (extroduce_imap f l1 i1))).
     apply (IlistPerm3_ilist_rel_eq_snd (ilist_rel_sym _ (extroduce_imap f l2 i2))).
     apply IH.
   Qed.

  Lemma IlistPerm3_imap_bis (A B: Set)(Rel: relation B)(f1 f2: A -> B)(l1 l2: ilist A):
     IlistPerm3 (fun a1 a2 => Rel (f1 a1) (f2 a2)) l1 l2 -> IlistPerm3 Rel (imap f1 l1) (imap f2 l2).
   Proof.
     intro Hyp.
     induction Hyp as [l1 l2 Hyp1 Hyp2 | l1 l2 i1 i2 H1 _ IH].
     apply IlistPerm3_nil ; assumption.
     apply (IlistPerm3_cons _ _ (i1 : Fin (lgti (imap f1 l1))) (i2 : Fin (lgti (imap f2 l2)))).
     assumption.
     assert (H7 := extroduce_imap f1 l1 i1).
     apply ilist_rel_sym in H7 ; try apply eq_equivalence.
     apply (IlistPerm3_ilist_rel_eq H7).
     clear H7.
     assert (H7 := extroduce_imap f2 l2 i2).
     apply ilist_rel_sym in H7 ; try apply eq_equivalence.
     apply (IlistPerm3_ilist_rel_eq_snd H7).
     assumption.
   Qed.

   Lemma IlistPerm3_imap_back (A B: Set)(Rel: relation B)
     (f1 f2: A -> B)(l1 l2: ilist A): IlistPerm3 Rel (imap f1 l1) (imap f2 l2) -> 
     IlistPerm3 (fun a1 a2 => Rel (f1 a1) (f2 a2)) l1 l2.
   Proof.
     remember (lgti l1) as n.
     revert l1 l2 Heqn ; induction n as [|n IH] ; intros l1 l2 H H1. 
     apply IlistPerm3_nil.
     apply (IlistPerm3_lgti H1).
     symmetry ; assumption.
     inversion_clear H1 as [H2 H3 | i1 i2 H2 H3].
     simpl in H3 ; rewrite <- H in H3.
     inversion H3.
     simpl in i1, i2, H2.
     apply (IlistPerm3_cons _ _ i1 i2).
     assumption.
     apply IH.
     evalLgtiExtro.
     apply H.
     assert (H4 := extroduce_imap f1 l1 i1).
     assert (H5 := extroduce_imap f2 l2 i2).
     apply (IlistPerm3_ilist_rel_eq H4), (IlistPerm3_ilist_rel_eq_snd H5), H3.
   Qed.

  Lemma IlistPerm3_exists_rec: forall (T: Set)(RelT: relation T)
     (i1 i2: ilist T), IlistPerm3 RelT i1 i2 -> forall f1, exists f2, RelT (fcti i1 f1) (fcti i2 f2) /\ 
                           IlistPerm3 RelT (extroduce i1 f1) (extroduce i2 f2).
   Proof.
     intros T RelT l1 l2 H.
     induction H as [l1 l2 _ e2 | l1 l2 i1 i2 h2 H IH].
     (* empty list *)
     intros i1.
     apply False_rec.
     rewrite e2 in i1.
     inversion i1.
     (* non-empty list *)
     assert (h1:= eq_S _ _ (IlistPerm3_lgti H)).
     do 2 rewrite <- extroduce_lgti in h1.

     destruct l1 as [n l1] ; destruct l2 as [n2 l2];
     simpl in i1, i2, h1, h2 ;
     fold (mkilist l1) in *|-*;
     fold (mkilist l2) in *|-*.
     revert l2 i2 h2 H IH ; rewrite <- h1 ; intros l2 i2 h2 H IH ; clear n2 h1.
     change (forall i1', exists i2', RelT (l1 i1') (l2 i2') /\ 
                         IlistPerm3 RelT (extroduce (mkilist l1) i1') (extroduce (mkilist l2) i2')).
     intros i1'. 
     (* is there something to do renaming? *)
     elim (eq_nat_dec (decode_Fin i1) (decode_Fin i1')) ; intros a.
     (* f1 = f1' *)
     rewrite <- (decode_Fin_unique _ _ a).
     exists i2.
     split; assumption.
     (* f1 <> f1' *)
     destruct n as [|n].
     (* exclude zero case *)
     inversion i1.
     (* main case *)    
     set (i1'new := index_in_extroduce i1 i1' a).
     destruct (IH (rewriteFins (extroduce_lgti_S _ i1) i1'new)) as [i2IH [IH1 IH2]].
     set (i2IH' := rewriteFins (sym_eq (extroduce_lgti_S _ i2)) i2IH).
     set (i2' := extroduce_Fin i2 i2IH').
     exists i2'.
     split.
     assert (h3: l1 i1' = fcti (extroduce (mkilist l1) i1) (rewriteFins (extroduce_lgti_S l1 i1) i1'new)) by
       apply index_in_extroduce_ok_cor.
     assert (h4: l2 i2' = fcti (extroduce (mkilist l2) i2) i2IH).
     unfold i2', i2IH'.
     rewrite extroduce_Fin_ok_cor.
     f_equal.
     treatFinPure.
     rewrite h3, h4.
     assumption.
     
     set (i1new := index_in_extroduce i1' i1 (not_eq_sym a)).
     assert (a2:  decode_Fin i2' <> decode_Fin i2).
     unfold i2'.
     intro Hyp.
     apply decode_Fin_unique in Hyp.
     apply (extroduce_Fin_not_fex _ Hyp).
     set (i2new := index_in_extroduce i2' i2 a2).
     apply (IlistPerm3_cons _ _ (rewriteFins (extroduce_lgti_S l1 i1') i1new) 
                                (rewriteFins (extroduce_lgti_S l2 i2') i2new)).
     unfold i1new.
     rewrite <- index_in_extroduce_ok_cor.
     unfold i2new.
     rewrite <- index_in_extroduce_ok_cor.
     exact h2.

     assert (H1:= extroduce_interchange_eq l1 i1' i1 (not_eq_sym a) a).
     fold i1new i1'new in H1.
     assert (H2:= extroduce_interchange_eq l2 i2' i2 a2 (not_eq_sym a2)).
     fold i2new in H2.
     apply ilist_rel_sym in H1 ; apply ilist_rel_sym in H2 ; try apply eq_equivalence.
     apply (IlistPerm3_ilist_rel_eq H1), (IlistPerm3_ilist_rel_eq_snd H2).
     assert (H3 : i2IH = rewriteFins (extroduce_lgti_S l2 i2) (index_in_extroduce i2 i2' (not_eq_sym a2))).
     unfold i2', i2IH'.
     rewrite index_in_from_extroduce.
     apply decode_Fin_unique.
     do 2 rewrite <- decode_Fin_match'.
     reflexivity.
     rewrite <- H3.
     assumption.
   Qed.

   (* from the Coq tutorial at POPL'08 *)
   Tactic Notation "remember" constr(c) "as" ident(x) "in" "|-" :=
     let x := fresh x in
     let H := fresh "Heq" x in
     (set (x := c); assert (H : x = c) by reflexivity; clearbody x).

   Lemma IlistPerm3_IlistPerm4_eq: forall (T: Set)(RelT: relation T)(i1 i2: ilist T),
     IlistPerm3 RelT i1 i2 -> IlistPerm4 RelT i1 i2.
   Proof.
     intros T RelT l1 l2 H.
     remember (lgti l1) as n in |-.
     revert l1 l2 H Heqn ; induction n as [|n IH]; intros l1 l2 H Heqn ; simpl in *|-*.
     apply IlistPerm4nil_gen.
     apply (IlistPerm3_lgti H).
     symmetry; assumption.

     apply is_IlistPerm4.
     apply (IlistPerm3_lgti H).
     intro i1.
     destruct (IlistPerm3_exists_rec H i1) as [i2 [Hyp1 Hyp2]].
     exists i2.
     split.
     exact Hyp1.
     apply IH.
     apply Hyp2.
     evalLgtiExtro.
     apply Heqn.
   Qed.

   Lemma IlistPerm3_extroduce : forall (T: Set)(RelT: relation T)
     (i1 i2: ilist T)(f1: Fin (lgti i1)) (f2 : Fin (lgti i2)), RelT (fcti i1 f1) (fcti i2 f2) -> 
     IlistPerm3 RelT (extroduce i1 f1) (extroduce i2 f2) -> IlistPerm3 RelT i1 i2.
   Proof.
     intros T RelT i1 i2 f1 f2.
     apply IlistPerm3_cons.
   Qed.

   Lemma IlistPerm3_trans (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(l1 l2 l3 : ilist T) : 
     IlistPerm3 RelT l1 l2 -> IlistPerm3 RelT l2 l3 -> IlistPerm3 RelT l1 l3.
   Proof.  
     intros H1 H2.
     apply IlistPerm4_IlistPerm3_eq.
     apply IlistPerm3_IlistPerm4_eq in H1.
     apply IlistPerm3_IlistPerm4_eq in H2.
     apply (IlistPerm4_trans _ H1 H2).
   Qed.

   Lemma IlistPerm3_trans_trans (T: Set)(RelT: relation T)(Rtrans: Transitive RelT)(l1 l2 l3 : ilist T) : 
     IlistPerm3 RelT l1 l2 -> IlistPerm3 RelT l2 l3 -> IlistPerm3 RelT l1 l3.
   Proof.  
     intros H1 H2.
     apply IlistPerm4_IlistPerm3_eq.
     apply IlistPerm3_IlistPerm4_eq in H1.
     apply IlistPerm3_IlistPerm4_eq in H2.
     apply (IlistPerm4_trans_trans _ H1 H2).
   Qed.

   Add Parametric Relation (T: Set)(RelT: relation T)(EqT: Equivalence RelT) : (ilist T)(IlistPerm3 RelT) 
      reflexivity proved by (IlistPerm3_refl EqT)
      symmetry proved by (IlistPerm3_sym EqT)
      transitivity proved by (IlistPerm3_trans EqT)
      as IlistPerm3Rel.

   Lemma IlistPerm4_sym (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(l1 l2 : ilist T) : 
     IlistPerm4 RelT l1 l2 -> IlistPerm4 RelT l2 l1.
   Proof.  
     intros H1.
     apply IlistPerm4_IlistPerm3_eq in H1.
     apply IlistPerm3_IlistPerm4_eq.
     apply (IlistPerm3_sym _ H1).
   Qed.

   Lemma IlistPerm4_sym_sym (T: Set)(RelT: relation T)(Rsym: Symmetric RelT)(l1 l2 : ilist T) : 
     IlistPerm4 RelT l1 l2 -> IlistPerm4 RelT l2 l1.
   Proof.  
     intros H1.
     apply IlistPerm4_IlistPerm3_eq in H1.
     apply IlistPerm3_IlistPerm4_eq.
     apply (IlistPerm3_sym_sym _ H1).
   Qed.

   Add Parametric Relation (T: Set)(RelT: relation T)(EqT: Equivalence RelT) : (ilist T)(IlistPerm4 RelT) 
      reflexivity proved by (IlistPerm4_refl EqT)
      symmetry proved by (IlistPerm4_sym EqT)
      transitivity proved by (IlistPerm4_trans EqT)
      as IlistPerm4Rel.

   Lemma IlistPerm5_sym (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(l1 l2 : ilist T) : 
     IlistPerm5 RelT l1 l2 -> IlistPerm5 RelT l2 l1.
   Proof.  
     intros H1.
     inversion EqT as [_ Rsym _].
     apply (IlistPerm5_sym_IlistPerm4 Rsym) in H1.
     apply (IlistPerm4_sym_IlistPerm5 Rsym).
     apply (IlistPerm4_sym _ H1).
   Qed.
     
   Lemma IlistPerm4_trans_special (A: Set)(R1 R2: relation A)(i1 i2 i3: ilist A):
     IlistPerm4 R1 i1 i2 -> IlistPerm4 R2 i2 i3 -> IlistPerm4 
       (fun a1 a3 => exists a2, R1 a1 a2 /\ R2 a2 a3) i1 i3.
   Proof.
     intro Hyp1.
     revert i3.
     induction Hyp1 as [l1 l2 H1 IH] using IlistPerm4_ind_better.
     intros l3 Hyp.
     inversion_clear Hyp as [x y H2 H3].
     apply is_IlistPerm4.
     transitivity (lgti l2); assumption.
     intro i1.
     destruct (IH i1) as [i2 [HypR1 [_ H5]]].
     destruct (H3 i2) as [i3 [HypR2 H2']].
     exists i3.
     split.
     exists (fcti l2 i2).
     split; assumption.
     apply H5, H2'.
   Qed.
 
   Corollary IlistPerm3_trans_special (A: Set)(R1 R2: relation A)(i1 i2 i3: ilist A):
     IlistPerm3 R1 i1 i2 -> IlistPerm3 R2 i2 i3 -> 
     IlistPerm3 (fun a1 a3 => exists a2, R1 a1 a2 /\ R2 a2 a3) i1 i3.
   Proof.
     intros.
     apply IlistPerm4_IlistPerm3_eq.
     apply (IlistPerm4_trans_special (i2:= i2));
     apply IlistPerm3_IlistPerm4_eq; assumption.
   Qed.
   
   Lemma IlistPerm3_mon :forall(U : Set) (l1 l2 : ilist U) R1 R2, 
     subrelation R1 R2 -> IlistPerm3 R1 l1 l2 -> IlistPerm3 R2 l1 l2.
   Proof.
     intros.
     induction H0.
     apply IlistPerm3_nil; assumption.
     apply (IlistPerm3_cons _ _ f1 f2).
     apply H.
     assumption.
     assumption.
   Qed.

  Section IlistPerm34_dec.
    Section IlistPerm6. 
    
      Inductive IlistPerm6 (T: Set)(RelT: relation T)(l1 l2: ilist T): Prop :=
        IlistPerm6_nil: lgti l1 = lgti l2 -> lgti l1 = 0 -> IlistPerm6 RelT l1 l2  
      | IlistPerm6_cons: (exists i1 , exists i2, RelT (fcti l1 i1) (fcti l2 i2) /\
        IlistPerm6 RelT (extroduce l1 i1) (extroduce l2 i2)) -> IlistPerm6 RelT l1 l2.
       
      Lemma IlistPerm6_ind_better (T: Set)(RelT : relation T)(P : ilist T → ilist T → Prop): 
        (forall l1 l2 : ilist T, lgti l1 = lgti l2 -> lgti l1 = 0 -> P l1 l2) -> 
        (forall l1 l2 : ilist T, forall i1 i2, RelT (fcti l1 i1) (fcti l2 i2) ->
        IlistPerm6 RelT (extroduce l1 i1) (extroduce l2 i2) -> P (extroduce l1 i1) (extroduce l2 i2) -> 
        P l1 l2) -> (forall l1 l2 : ilist T, IlistPerm6 RelT l1 l2 -> P l1 l2).
      Proof.
        fix Hr 5.
        intros H1 H2 l1 l2 H3.
        destruct H3 as [H3 H4 | [i1 [i2 [H3 H4]]]].
        apply H1 ; assumption.
        apply (H2 l1 l2 i1 i2 H3 H4).
        apply Hr ; try assumption.
      Qed.

      Lemma IlistPerm6_lgti (T: Set)(RelT: relation T)(l1 l2: ilist T): IlistPerm6 RelT l1 l2 -> 
        lgti l1 = lgti l2.
      Proof.
        revert l1 l2.
        fix Hr 3.
        intros l1 l2 [H1 H2 | [i1 [i2 [H1 H2]]]].
        assumption.
        assert (H3 := Hr _ _ H2).
        apply eq_S in H3.
        do 2 rewrite <- extroduce_lgti in H3.
        assumption.
      Qed.

      Lemma IlistPerm3_IlistPerm6_eq (T: Set)(RelT: relation T)(l1 l2: ilist T): 
        IlistPerm3 RelT l1 l2 -> IlistPerm6 RelT l1 l2.
      Proof.
        intros H ; induction H as [l1 l2 H1 H2 | l1 l2 i1 i2 H1 H2 IH].
        apply IlistPerm6_nil; assumption.
        apply IlistPerm6_cons.
        exists i1, i2 ; split; assumption.
      Qed.

      Lemma IlistPerm6_IlistPerm3_eq (T: Set)(RelT: relation T)(l1 l2: ilist T): 
        IlistPerm6 RelT l1 l2 -> IlistPerm3 RelT l1 l2.
      Proof.
        intros H.
        induction H using IlistPerm6_ind_better.
        apply IlistPerm3_nil ; assumption.
        apply (IlistPerm3_cons _ _ i1 i2); assumption.
      Qed.

      Lemma IlistPerm4_IlistPerm6_eq (T: Set)(RelT: relation T)(l1 l2: ilist T): 
        IlistPerm4 RelT l1 l2 -> IlistPerm6 RelT l1 l2.
      Proof.
        intro H.
        apply IlistPerm3_IlistPerm6_eq, IlistPerm4_IlistPerm3_eq.
        assumption.
      Qed.

      Lemma IlistPerm6_IlistPerm4_eq (T: Set)(RelT: relation T)(l1 l2: ilist T): 
        IlistPerm6 RelT l1 l2 -> IlistPerm4 RelT l1 l2.
      Proof.
        intro H.
        apply IlistPerm3_IlistPerm4_eq, IlistPerm6_IlistPerm3_eq.
        assumption.
      Qed.
    End IlistPerm6. 

    Lemma extroduce_IlistPerm4 (T: Set)(RelT: relation T)(Req : Equivalence RelT)(l1 l2: ilist T): 
      forall i1 i2, IlistPerm4 RelT l1 l2 -> RelT (fcti l1 i1) (fcti l2 i2) -> 
      IlistPerm4 RelT (extroduce l1 i1) (extroduce l2 i2).
    Proof.
      intros i1 i2 H.
      apply IlistPerm4_IlistPerm6_eq in H.
      induction H  as [l1 l2 H1 H2| l1 l2 i1' i2' H1 H2 IH] using IlistPerm6_ind_better.
      apply False_rec; rewrite H2 in i1 ; inversion i1.
      destruct l1 as [n l1] ; destruct l2 as [n2 l2] ; assert (H4 := IlistPerm6_lgti H2) ; 
      simpl in H1, i1', i2'; fold (mkilist l1) (mkilist l2) in *|-*.
      apply eq_S in H4 ; do 2 rewrite <- extroduce_lgti in H4 ; simpl in H4.
      revert l2 i2' H1 H2 IH i2; rewrite <- H4 ; clear n2 H4 ; intros l2 i2' H1 H2 IH i2 H3 ; 
      simpl in i1, i2, H3.
      destruct n as [|n].
      inversion i1.
      apply IlistPerm6_IlistPerm4_eq.
      
      elim (eq_nat_dec (decode_Fin i1') (decode_Fin i1)) ; intros a ; 
      (* case i1 = i1'*) 
      try (revert H3 ; rewrite <- (decode_Fin_unique _ _ a) ; clear i1 a; intros H3) ; 
      elim (eq_nat_dec (decode_Fin i2') (decode_Fin i2)) ; intros b ;
      (* case i2 = i2'*)
      try (revert H3 ; rewrite <- (decode_Fin_unique _ _ b) ;  clear i2 b; intros H3 ) ; 
      (* case i1 = i1' /\ i2 = i2'*)
      try apply H2 ; 
      (* all other cases *)
      apply IlistPerm6_cons ; apply IlistPerm6_IlistPerm4_eq in H2.
      
      (* case i1 = i1' /\ i2 <> i2' *)
      apply IlistPerm4_sym_IlistPerm5, (IlistPerm5_sym Req) in H2; try (destruct Req ; assumption).
      inversion_clear H2 as [i3 i4 H9 H4 H10 H11] ; clear H9.
      destruct (H4 (rewriteFins (extroduce_lgti_S _ _) (index_in_extroduce i2' i2 b))) as [i1 [H5 H6]].
      exists i1, (rewriteFins (extroduce_lgti_S _ _) (index_in_extroduce i2 i2' (not_eq_sym b))).
      split.
      rewrite H5, <- index_in_extroduce_ok_cor, <- index_in_extroduce_ok_cor, <- H3.
      assumption.
      apply IlistPerm3_IlistPerm6_eq, (IlistPerm3_ilist_rel_eq_snd (extroduce_interchange_eq l2 _ _ b _)).
      apply IlistPerm5_IlistPerm3_eq, H6.
      
      (* cas i1 <> i1' /\ i2 = i2' *)
      inversion_clear H2 as [i3 i4 H9 H4 H10 H11] ; clear H9.
      destruct (H4 (rewriteFins (extroduce_lgti_S _ _) (index_in_extroduce i1' i1 a))) as [i2 [H5 H6]].
      exists (rewriteFins (extroduce_lgti_S _ _) (index_in_extroduce i1 i1' (not_eq_sym a))), i2.
      split.
      rewrite <- H5, <- index_in_extroduce_ok_cor, <- index_in_extroduce_ok_cor, H3.
      assumption.
      apply IlistPerm3_IlistPerm6_eq, 
      (IlistPerm3_ilist_rel_eq (extroduce_interchange_eq l1 _ _ a (not_eq_sym a))).
      apply IlistPerm4_IlistPerm3_eq, H6.
      
      (* cas i1 <> i1' /\ i2 <> i2' *) 
      exists (rewriteFins (extroduce_lgti_S _ _) (index_in_extroduce _ _ (not_eq_sym a))), 
      (rewriteFins (extroduce_lgti_S _ _) (index_in_extroduce _ _ (not_eq_sym b))).
      split.
      do 2 rewrite <- index_in_extroduce_ok_cor.
      assumption.
      apply IlistPerm3_IlistPerm6_eq, (IlistPerm3_ilist_rel_eq (extroduce_interchange_eq l1 _ _ a _)).
      apply (IlistPerm3_ilist_rel_eq_snd (extroduce_interchange_eq l2 _ _ b _)), IlistPerm4_IlistPerm3_eq.
      apply IH.
      do 2 rewrite <- index_in_extroduce_ok_cor.
      assumption.
    Qed.

    Lemma exists_eq_Ilist (T: Set)(RelT: relation T)
      (Rdec : forall t1 t2, {RelT t1 t2}+{not (RelT t1 t2)})(t: T)(n: nat) (l : ilistn T n): 
      { i | RelT t (l i)} + {not (exists i, RelT t (l i))}.
    Proof.
      induction n as [|n IH].
      right.
      intros [i _] ; inversion i.
      
      elim (Rdec t (l (first n))) ; intros H.
      left.
      exists (first n) ; assumption.
      
      destruct (IH (fun x => l (succ x))) as [[i H1] | H1].
      left.
      exists (succ i) ; assumption.
      right.
      
      intros [i H2].
      elim (zerop (decode_Fin i)) ; intros a.
      rewrite (decode_Fin_0_first _ a) in H2.
      contradiction.
      apply H1.
      exists (get_cons _ a).
      rewrite <- (decode_Fin_unique _ _ (decode_Fin_get_cons _ _ : 
        decode_Fin i = decode_Fin (succ (get_cons i a)))).
      assumption.
    Qed.
    
    Lemma IlistPerm4_dec (T: Set)(RelT: relation T)(Req : Equivalence RelT)
      (Rdec : forall t1 t2, {RelT t1 t2}+{not (RelT t1 t2)}): 
      forall l1 l2, {IlistPerm4 RelT l1 l2}+{not (IlistPerm4 RelT l1 l2)}.
    Proof.
      intros [n1 l1] [n2 l2].
      (* comparison between n1 and n2 *)
      elim (eq_nat_dec n1 n2) ; intros H.
      (* case n1 = n2 --> suppression of n2 *)
      revert l2.
      rewrite <- H.
      intros l2 ; clear n2 H.
      
      (* induction on n1 *)
      induction n1 as [|n1 IH].
      
      (* case 0 *)
      left.
      apply IlistPerm4nil.
      
      (* case S n1 *)
      (* Does an element in l2 "equal" to l1 (first n1) exists ? *)
      elim (exists_eq_Ilist RelT Rdec (l1 (first n1)) l2) ; intros H1.
      
      (* yes : i *)
      destruct H1 as [i H1].
      (* trick to use IH *)
      set (e1 := extroduce (mkilist l1) (first n1)).
      set (e2 := extroduce (mkilist l2) i).
      assert (H2 : n1 = lgti e1) by apply extroduce_lgti_S.
      assert (H3 : n1 = lgti e2) by apply extroduce_lgti_S.
      assert (H4 := refl_equal _ : e1 = extroduce (mkilist l1) (first n1)).
      assert (H5 := refl_equal _ : e2 = extroduce (mkilist l2) i).
      destruct e1 as [n1' e1] ; destruct e2 as [n2' e2] ; simpl in H2, H3.
      revert e1 e2 H4 H5 ; rewrite <- H2, <- H3 ; clear n1' n2' H2 H3 ; intros e1 e2 H2 H3.
      elim (IH e1 e2) ; clear IH ; intros H4 ; 
      rewrite H2, H3 in H4 ; clear e1 e2 H2 H3.
      
      (* here we prove the ilists are equivalent *)
      left.
      apply IlistPerm3_IlistPerm4_eq.
      apply (IlistPerm3_cons _ _ (first n1 : Fin (lgti (mkilist l1))) (i : Fin (lgti (mkilist l2))) H1).
      apply (IlistPerm4_IlistPerm3_eq H4).
      
      (* here we prove the ilists are not equivalent *)
      right.
      intros H5.
      assert (H6 := extroduce_IlistPerm4 _ (first n1: Fin (lgti (mkilist l1))) 
        (i: Fin (lgti (mkilist l2))) H5 H1).
      contradiction.
      
      (* no *)
      right.
      intro H.
      inversion H.
      rewrite H3, H4 in H2 ; clear i1 i2 H0 H3 H4.
      simpl lgti in H2 ; simpl fcti in H2.
      destruct (H2 (first n1)) as [i [H3 _]].
      apply H1.
      exists i ; assumption.
      
      (* cas n1 <> n2 *)
      right.
      intro H1.
      apply IlistPerm4_lgti in H1.
      contradiction.
    Qed.
      
    Lemma IlistPerm4_dec_IlistPerm3_dec (T: Set)(RelT: relation T):
      (forall l1 l2, {IlistPerm4 RelT l1 l2}+{not (IlistPerm4 RelT l1 l2)}) ->
      forall l1 l2, {IlistPerm3 RelT l1 l2}+{not (IlistPerm3 RelT l1 l2)}.
    Proof.
      intros H l1 l2.
      destruct (H l1 l2) as [H1 | H1].
      left ; apply IlistPerm4_IlistPerm3_eq, H1.
      right ; intro H2 ; apply H1, IlistPerm3_IlistPerm4_eq, H2.
    Qed.
  
    Lemma IlistPerm3_dec (T: Set)(RelT: relation T)(Req : Equivalence RelT)
      (Rdec : forall t1 t2, {RelT t1 t2}+{not (RelT t1 t2)}): 
    forall l1 l2, {IlistPerm3 RelT l1 l2}+{not (IlistPerm3 RelT l1 l2)}.
    Proof.
      apply IlistPerm4_dec_IlistPerm3_dec, IlistPerm4_dec ; assumption.
    Qed.

    End IlistPerm34_dec.

    Section IlistPerm3_cert.

    (* IlistPerm3Cert shall now be IlistPerm3 with a certificate for the chosen permutation *)
    Fixpoint IlistPerm3Cert_list (n: nat) : Set :=
      match n with 
        0 => unit
      | S n' => prod (prod (Fin (S n')) (Fin (S n'))) (IlistPerm3Cert_list n') end.

    Definition IlistPerm3Cert_aux2 (A: Set)(i1 i2: ilist A)(Hyp: lgti i1 = lgti i2) 
      (f1: Fin(lgti i1))(f2: Fin(lgti i2)): lgti (extroduce i1 f1) = lgti (extroduce i2 f2).
    Proof.
      apply eq_add_S.
      do 2 rewrite <- extroduce_lgti.
      assumption.
    Defined.

    Definition rewriteIlistPerm3Cert_list (n1 n2: nat)(H: n1 = n2)(f: IlistPerm3Cert_list n1): 
      IlistPerm3Cert_list n2.
    Proof.
      revert n2 H ; induction n1 as [|n1 IH] ; intros [|n2] H.
      exact tt.
      inversion H.
      inversion H.
      destruct f as [[i1 i2] f].
      fold (IlistPerm3Cert_list n1) in f.
      split.
      exact (rewriteFins H i1, rewriteFins H i2).
      apply (IH f).
      apply eq_add_S, H.
    Defined.

    Definition IlistPerm3Cert_aux3 (A: Set)(l1 l2: ilist A)(Hyp : lgti l1 = lgti l2)(i1: Fin(lgti l1))
      (i2 : Fin (lgti l2))(c: IlistPerm3Cert_list (lgti (extroduce l1 i1))): IlistPerm3Cert_list (lgti l1).
    Proof.
      destruct l1 as [[|n1] l1].
      inversion i1.
      exact (i1, (rewriteFins (sym_eq Hyp) i2), (rewriteIlistPerm3Cert_list (sym_eq (extroduce_lgti_S _ _)) c)).
    Defined.

    Lemma IlistPerm3Cert_list_eq (n: nat)(c: IlistPerm3Cert_list n)(H: n = n) : 
      c = rewriteIlistPerm3Cert_list H c.
    Proof.
      induction n as [|n IH] ; destruct c as [[i1 i2] c].
      reflexivity.
      simpl.
      f_equal ; try f_equal ; try treatFinPure.
      apply IH.
    Qed.

    Lemma rewriteIlistPerm3Cert_list_proofirr: forall (n1 n2: nat)(e1 e2: n1 = n2)
      (f: IlistPerm3Cert_list n1), rewriteIlistPerm3Cert_list e1 f = rewriteIlistPerm3Cert_list e2 f.
    Proof.
      induction n1 as [|n1 IH]; intros [|n2] e1 e2 f.
      reflexivity.
      inversion e1.
      inversion e1.
      destruct f as [[i1 i2] f].
      simpl.
      f_equal.
      f_equal ; treatFinPure.
      apply IH.
    Qed.
    
    Lemma rewriteIlistPerm3Cert_list_sym: forall (n1 n2: nat)(e: n1 = n2)(f: IlistPerm3Cert_list n2),
      rewriteIlistPerm3Cert_list e (rewriteIlistPerm3Cert_list (sym_eq e) f) = f.
    Proof.
      induction n1 as [|n1 IH]; intros [|n2] e f.
      destruct f.
      reflexivity.
      inversion e.
      inversion e.
      destruct f as [[i1 i2] f].
      simpl.
      f_equal.
      f_equal ; treatFinPure.
      rewrite (rewriteIlistPerm3Cert_list_proofirr _ (eq_sym (eq_add_S _ _ e))).
      apply IH.
    Qed.

    Lemma IlistPerm3Cert_aux3_ok1(A: Set)(n: nat)(l1 l2: ilistn A (S n))(Hyp : lgti (mkilist l1) = lgti (mkilist l2))
      (i1: Fin (lgti (mkilist l1)))(i2 : Fin (lgti (mkilist l2)))
      (c: IlistPerm3Cert_list (lgti (extroduce (mkilist l1) i1))):
      IlistPerm3Cert_aux3 (mkilist l1) (mkilist l2) Hyp i1 i2 c = 
      (((i1, i2: Fin (lgti (mkilist l1))), rewriteIlistPerm3Cert_list (sym_eq (extroduce_lgti_S l1 i1)) c)).
    Proof.
      simpl.
      repeat f_equal.
      apply decode_Fin_unique, sym_eq, decode_Fin_match.
    Qed.
    
    Lemma IlistPerm3Cert_aux3_proofirr(T: Set)(l1 l2: ilist T)(H1 H2: lgti l1 = lgti l2)
      (i1 : Fin (lgti l1))(i2 : Fin (lgti l2)) (c: IlistPerm3Cert_list (lgti (extroduce l1 i1))): 
      IlistPerm3Cert_aux3 l1 l2 H1 i1 i2 c = IlistPerm3Cert_aux3 l1 l2 H2 i1 i2 c.
    Proof.
      destruct l1 as [n1 l1] ; destruct l2 as [n2 l2].
      simpl in H1, H2, i1, i2.
      revert l2 H2 i2 c ; rewrite <- H1 ; clear n2 H1 ; intros l2 H2 i2 c.
      destruct n1 as [|n1].
      inversion i1.
      simpl.
      do 2 f_equal.
      treatFinPure.
    Qed.

    Inductive IlistPerm3Cert (A: Set)(RA: relation A)(l1 l2: ilist A)(Hyp: lgti l1 = lgti l2)
      (c: IlistPerm3Cert_list(lgti l1)): Prop :=
      IlistPerm3Cert_nil: lgti l1 = 0 -> IlistPerm3Cert RA l1 l2 Hyp c
    | IlistPerm3Cert_cons: 
        forall (i1: Fin(lgti l1))(i2: Fin(lgti l2))(c': IlistPerm3Cert_list (lgti (extroduce l1 i1))), 
        RA (fcti l1 i1) (fcti l2 i2) -> 
        c = IlistPerm3Cert_aux3 l1 l2 Hyp i1 i2 c'->
        IlistPerm3Cert  RA (extroduce l1 i1) (extroduce l2 i2) (IlistPerm3Cert_aux2 l1 l2 Hyp i1 i2) c'-> 
        IlistPerm3Cert  RA l1 l2 Hyp c.
    
    Lemma IlistPerm3Cert_IlistPerm3 (A: Set)(RA: relation A)(i1 i2: ilist A)(Hyp: lgti i1 = lgti i2)
      (f: IlistPerm3Cert_list(lgti i1)): IlistPerm3Cert RA i1 i2 Hyp f -> IlistPerm3 RA i1 i2.
    Proof.
      intro H.
      induction H.
      apply IlistPerm3_nil; assumption.
      apply (IlistPerm3_cons _ _ i1 i2); assumption.
    Qed.

    Lemma IlistPerm3_IlistPerm3Cert (A: Set)(RA: relation A)(i1 i2: ilist A)(Hyp: lgti i1 = lgti i2): 
      IlistPerm3 RA i1 i2 -> exists f: IlistPerm3Cert_list(lgti i1), IlistPerm3Cert RA i1 i2 Hyp f.
    Proof.
      intro H.
      induction H as [l1 l2 H1 H2 |l1 l2 i1 i2 H1 H2 IH ].
      exists (rewriteIlistPerm3Cert_list (sym_eq H2) tt).
      apply IlistPerm3Cert_nil.
      assumption.
      destruct (IH (IlistPerm3Cert_aux2 l1 l2 Hyp i1 i2)) as [c Hypf].
      exists (IlistPerm3Cert_aux3 l1 l2 Hyp i1 i2 c).
      apply (@IlistPerm3Cert_cons _ _ _ _  _ _  _ i2 c H1 (refl_equal _) Hypf).
    Qed.

    Lemma IlistPerm3Cert_mon (A: Set)(RA1 RA2: relation A)(HypR: subrelation RA1 RA2)(i1 i2: ilist A)
      (Hyp: lgti i1 = lgti i2)(f: IlistPerm3Cert_list(lgti i1)):
      IlistPerm3Cert RA1 i1 i2 Hyp f -> IlistPerm3Cert RA2 i1 i2 Hyp f.
    Proof.
      intro H.
      induction H.
      apply IlistPerm3Cert_nil, H.
      apply (@IlistPerm3Cert_cons _ _ _ _ _ _ _ i2 c') ; try assumption.
      apply HypR, H.
    Qed.

    Lemma IlistPerm3Cert_proofirr(T: Set)(R: relation T)(l1 l2: ilist T)(H1 H2: lgti l1 = lgti l2)
      (c: IlistPerm3Cert_list(lgti l1)): IlistPerm3Cert R l1 l2 H1 c -> IlistPerm3Cert R l1 l2 H2 c.
    Proof.
      intros H3.
      induction H3 as [l1 l2 H1 c H3 |l1 l2 H1 c i1 i2 c' H3 H4 _ IH].
      apply IlistPerm3Cert_nil, H3.
      apply (@IlistPerm3Cert_cons _ _ _ _ _ _ i1 i2 c' H3).
      rewrite H4.
      apply IlistPerm3Cert_aux3_proofirr.
      apply IH.
    Qed.

    Lemma IlistPerm3Cert_inter (A: Set)(l1 l2: ilist A)(Hyp: lgti l1 = lgti l2)
      (c: IlistPerm3Cert_list(lgti l1))(I: Type)(R: I -> relation A)
      (HypR: forall i:I, IlistPerm3Cert (R i) l1 l2 Hyp c):
      IlistPerm3Cert (fun a1 a2 => forall i, R i a1 a2) l1 l2 Hyp c.
    Proof.
      destruct l1 as [n1 l1] ; destruct l2 as [n2 l2]. 
      simpl in Hyp.
      revert l2 c HypR ; rewrite <- Hyp ; intros l2 c H1.
      simpl in *|-*.
      fold (mkilist l1) (mkilist l2) in *|-*.
      clear Hyp n2.
      induction n1 as [|n1 IH].
      apply IlistPerm3Cert_nil.
      reflexivity.
      
      destruct c as [[i1 i2] c] ; fold (IlistPerm3Cert_list n1) in c.
      apply (@IlistPerm3Cert_cons _ _ _ _ _ _ (i1: Fin (lgti (mkilist l1))) 
      (i2: Fin (lgti (mkilist l2))) (rewriteIlistPerm3Cert_list (extroduce_lgti_S _ _) c)).
      intros i.
      destruct (H1 i) as [H | i1' i2' c'' H5 H6 H7].
      inversion H.
      simpl in H6.
      inversion H6.
      assumption.
      simpl.
      rewrite (rewriteIlistPerm3Cert_list_proofirr _ (eq_sym (eq_sym (extroduce_lgti_S l1 i1)))), 
      rewriteIlistPerm3Cert_list_sym.
      reflexivity.
      
      set (l1' := extroduce (mkilist l1) i1).
      set (l2' := extroduce (mkilist l2) i2).
      assert(H4 := extroduce_lgti_S l1 i1 : n1 = lgti l1').
      rewrite (rewriteIlistPerm3Cert_list_proofirr _ H4).
      assert (H5 := IlistPerm3Cert_aux2 (mkilist l1) (mkilist l2) (eq_refl (S n1)) i1 i2 : 
      lgti l1' = lgti l2').
      apply (@IlistPerm3Cert_proofirr _ _ _ _ H5 _ (rewriteIlistPerm3Cert_list H4 c)).
      
      assert (H2 := refl_equal _ : l1' = extroduce (mkilist l1) i1) ;
      assert (H3 := refl_equal _ : l2' = extroduce (mkilist l2) i2).
      destruct l1' as [n1' l1'] ; destruct l2' as [n2' l2'].
      simpl in H4, H5.
      revert l1' l2' H2 H3 ; rewrite <- H5, <- H4 ; clear n1' n2' H4 H5 ; intros l1' l2' H2 H3.
      fold (mkilist l1') (mkilist l2') in *|-*.
      apply IH ; clear IH.
      rewrite <- IlistPerm3Cert_list_eq.
      intros i.
      destruct (H1 i) as [H4 | i1' i2' c'' _ H4 H5].
      inversion H4.
      simpl in H4.
      inversion H4.
      revert H2 H3 ; rewrite H0, H6 ; intros H2 H3 ; clear i1 i2 H1 H0 H4 H6 H7 c.
      assert (H6 := eq_sym (extroduce_lgti_S l1 i1')).
      rewrite (rewriteIlistPerm3Cert_list_proofirr _ H6).
      assert (H7 := IlistPerm3Cert_aux2 (mkilist l1) (mkilist l2) (eq_refl (S n1)) i1' i2').
      apply (IlistPerm3Cert_proofirr H7) in H5.
      revert H5.
      revert H6 H7 c''.
      rewrite <- H2, <- H3.
      simpl.
      intros H6 H7 c''.
      rewrite <- IlistPerm3Cert_list_eq.
      apply IlistPerm3Cert_proofirr.
    Qed.
    
    Definition IlistPerm3Cert_list_function (n: nat)(c: IlistPerm3Cert_list n) : Fin n -> Fin n.
    Proof.
      induction n as [|n IH] ; intro i.
      inversion i.
      destruct c as [[i1 i2] c].
      fold (IlistPerm3Cert_list n) in c.
      elim (eq_nat_dec (decode_Fin i1) (decode_Fin i)); intros a.
      exact i2.
      exact (extroduce_Fin i2 (IH c (index_in_extroduce _ _ a))).
    Defined.

    Definition IlistPerm3Cert_list_inv (n: nat)(c: IlistPerm3Cert_list n) : IlistPerm3Cert_list n.
    Proof.
      induction n as [|n IH].
      apply c.
      destruct c as [[i1 i2] c].
      exact ((i2, i1), (IH c)).
    Defined.

    Definition IlistPerm3Cert_list_function_inv (n: nat)(c: IlistPerm3Cert_list n):= 
      IlistPerm3Cert_list_function (IlistPerm3Cert_list_inv _ c).
      
    Lemma IlistPerm3Cert_list_inv_inv_id (n: nat)(c: IlistPerm3Cert_list n) : 
      IlistPerm3Cert_list_inv _ (IlistPerm3Cert_list_inv _ c) = c.
    Proof.
      induction n as [|n IH].
      reflexivity.
      destruct c as [[i1 i2] c].
      simpl.
      rewrite IH ; reflexivity.
    Qed.

    Lemma IP3Cl_function_ok1 (n: nat)(i1 i2 : Fin (S n))(c: IlistPerm3Cert_list n)(i: Fin (S n)) : 
      decode_Fin i1 = decode_Fin i -> IlistPerm3Cert_list_function (((i1, i2), c): IlistPerm3Cert_list (S n)) i = i2.
    Proof.
      intros H.
      rewrite (decode_Fin_unique _ _ H).
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (eq_nat_dec (decode_Fin i) (decode_Fin i)) ; intros a.
      reflexivity.
      apply False_rec, a, eq_refl.
    Qed.

    Lemma IP3Cl_function_ok2 (n: nat)(i1 i2 : Fin (S n))(c: IlistPerm3Cert_list n)(i: Fin (S n))
      (h: decode_Fin i1 <> decode_Fin i) : 
      decode_Fin i2 <= decode_Fin (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)) -> 
      IlistPerm3Cert_list_function (((i1, i2), c): IlistPerm3Cert_list (S n)) i = 
      succ (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)).
    Proof.
      intros H.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (eq_nat_dec (decode_Fin i1) (decode_Fin i)) ; intros a.
      contradiction a.
      rewrite (index_in_extroduce_proofirr _ _ a h).
      apply extroduce_Fin_ok1.
      assumption.
    Qed.
    
    Lemma IP3Cl_function_ok3 (n: nat)(i1 i2 : Fin (S n))(c: IlistPerm3Cert_list n)(i: Fin (S n))
      (h: decode_Fin i1 <> decode_Fin i) : 
      decode_Fin (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)) < decode_Fin i2 -> 
      IlistPerm3Cert_list_function (((i1, i2), c): IlistPerm3Cert_list (S n)) i = 
        weakFin (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)).
    Proof.
      intros H.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (eq_nat_dec (decode_Fin i1) (decode_Fin i)) ; intros a.
      contradiction a.
      rewrite (index_in_extroduce_proofirr _ _ a h).
      apply extroduce_Fin_ok2.
      assumption.
    Qed.

    Lemma IP3Cl_function_ok4 (n: nat)(i1 i2 : Fin (S n))(c: IlistPerm3Cert_list n)(i: Fin (S n))
      (h: decode_Fin i1 <> decode_Fin i) : 
      IlistPerm3Cert_list_function (((i1, i2), c): IlistPerm3Cert_list (S n)) i = 
      extroduce_Fin i2 (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)).
    Proof.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (eq_nat_dec (decode_Fin i1) (decode_Fin i)) ; intros a.
      contradiction a.
      rewrite (index_in_extroduce_proofirr _ _ a h).
      reflexivity.
    Qed.

    Lemma IP3Cl_function_function_inv_inv (n: nat)(c: IlistPerm3Cert_list n) : 
      forall i, (IlistPerm3Cert_list_function c) (IlistPerm3Cert_list_function_inv c i) = i.
    Proof.
      intros i ; induction n as [|n IH].
      inversion i.
      
      destruct c as [[i1 i2] c].
      fold (IlistPerm3Cert_list n) in c.
      unfold IlistPerm3Cert_list_function_inv.
      change (IlistPerm3Cert_list_inv (S n) (i1, i2, c)) with ((i2, i1, (IlistPerm3Cert_list_inv n c))).

      elim (eq_nat_dec (decode_Fin i2) (decode_Fin i)) ; intros a.
      rewrite (IP3Cl_function_ok1 i2 i1 _ i) ; try assumption.
      rewrite IP3Cl_function_ok1 ; try reflexivity.
      apply decode_Fin_unique, a.
      
      elim (le_lt_dec (decode_Fin i1) 
      (decode_Fin (IlistPerm3Cert_list_function (IlistPerm3Cert_list_inv n c) (index_in_extroduce i2 i a)))); intros b.
      rewrite (IP3Cl_function_ok2 _ _ _ _ a b).
      
      assert (h : decode_Fin i1 <> (decode_Fin (succ
      (IlistPerm3Cert_list_function (IlistPerm3Cert_list_inv n c) (index_in_extroduce i2 i a))))).
      intros h.
      rewrite h in b.
      apply (le_Sn_n _ b).
      
      apply le_lt_n_Sm in b.
      change (S (decode_Fin _)) with (decode_Fin (succ  (IlistPerm3Cert_list_function (IlistPerm3Cert_list_inv n c)
        (index_in_extroduce i2 i a)))) in b.
      fold (IlistPerm3Cert_list_function_inv c) in *|-*.
      

      elim (le_lt_dec (decode_Fin i2) (decode_Fin (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)))); 
      intros d.
      rewrite (IP3Cl_function_ok2 _ _ _ _ h) ; try assumption.
      revert d.
      rewrite index_in_extroduce_succ2 ; try assumption.
      rewrite IH.
      intros d.
      apply index_in_extroduce_succ ; try assumption.
      
      rewrite (IP3Cl_function_ok3 _ _ _ _ h) ; try assumption.
      revert d.
      rewrite index_in_extroduce_succ2 ; try assumption.
      rewrite IH.
      intros d.
      apply index_in_extroduce_weakFin2 ; try assumption.
      
      rewrite (IP3Cl_function_ok3 _ _ _ _ a b).
      rewrite <- weakFin_ok in b.
      
      assert (h : decode_Fin i1 <> (decode_Fin (weakFin
      (IlistPerm3Cert_list_function (IlistPerm3Cert_list_inv n c) (index_in_extroduce i2 i a))))).
      intros h.
      rewrite h in b.
      apply (le_Sn_n _ b).
      
      fold (IlistPerm3Cert_list_function_inv c) in *|-*.
      
      elim (le_lt_dec (decode_Fin i2) (decode_Fin (IlistPerm3Cert_list_function c (index_in_extroduce _ _ h)))); 
      intros d.
      rewrite (IP3Cl_function_ok2 _ _ _ _ h) ; try assumption.
      revert d.
      rewrite index_in_extroduce_weakFin ; try assumption.
      rewrite IH.
      intros d.
      apply index_in_extroduce_succ ; try assumption.
      
      rewrite (IP3Cl_function_ok3 _ _ _ _ h) ; try assumption.
      revert d.
      rewrite index_in_extroduce_weakFin ; try assumption.
      rewrite IH.
      intros d.
      apply index_in_extroduce_weakFin2 ; try assumption.
    Qed.

    Lemma IP3Cl_function_inv_function_inv (n: nat)(c: IlistPerm3Cert_list n) : 
      forall i, (IlistPerm3Cert_list_function_inv c) (IlistPerm3Cert_list_function c i) = i.
    Proof.
      unfold IlistPerm3Cert_list_function_inv.
      rewrite <- (IlistPerm3Cert_list_inv_inv_id _ c), IlistPerm3Cert_list_inv_inv_id.
      apply IP3Cl_function_function_inv_inv.
    Qed.


    Lemma IlistPerm3Cert_list_function_ok_n (T: Set)(R: relation T)(n: nat)(l1 l2 : ilistn T n)
      (c: IlistPerm3Cert_list n)(h: n = n): IlistPerm3Cert R (mkilist l1) (mkilist l2) h c -> 
      forall i, R (l1 i) (l2 (IlistPerm3Cert_list_function c i)).
    Proof.
      intros h1 i.
      induction n as [|n IH].
      inversion i.
      destruct h1 as [h1 |i1 i2 c' h1 h2 h3].
      inversion h1.
      simpl in i1, i2, h1.
      rewrite h2.
      
      rewrite IlistPerm3Cert_aux3_ok1.
      
      elim (eq_nat_dec (decode_Fin i1) (decode_Fin i)) ; intros a.
      rewrite IP3Cl_function_ok1 ; try assumption.
      rewrite <- (decode_Fin_unique _ _ a).
      assumption.
      
      rewrite (IP3Cl_function_ok4 _ _ _ _ a).
      set (i2' := IlistPerm3Cert_list_function (rewriteIlistPerm3Cert_list (eq_sym (extroduce_lgti_S l1 i1)) c') 
      (index_in_extroduce _ _ a)).
      change (R (l1 i) (l2 (extroduce_Fin i2 i2'))).
      
      assert (h4 : decode_Fin i2 <> decode_Fin (extroduce_Fin i2 i2')).
      intro H.
      apply decode_Fin_unique, sym_eq in H.
      apply (extroduce_Fin_not_fex _ H).
      rewrite (index_in_extroduce_ok_cor l1 _ _ a), (index_in_extroduce_ok_cor l2 _ _ h4).
      clear h2.
      rewrite index_in_from_extroduce.
      revert c' h3 i2' h4.
      set (h3' := IlistPerm3Cert_aux2 (mkilist l1) (mkilist l2) h i1 i2).
      set (h5 := extroduce_lgti_S l1 i1) ; set (h6 := extroduce_lgti_S l2 i2).
      generalize h3' h5 h6 ; clear h3' h5 h6.
      set (l1' := extroduce (mkilist l1) i1) ; set (l2' := extroduce (mkilist l2) i2) ;
      assert (h7 := refl_equal _ : extroduce (mkilist l1) i1 = l1') ; 
      assert (h8 := refl_equal _ : l2' = extroduce (mkilist l2) i2).
      destruct l1' as [n1' l1'] ; destruct l2' as [n2' l2'].
      simpl lgti.
      intros h3' h5 h6; revert h3' l1' l2' h7 h8.
      rewrite <- h5, <- h6.
      clear n1' n2' h5 h6.
      intros h3' l1' l2' h5 h6 c' h3.
      fold (mkilist l1') (mkilist l2') in *|-*.
      rewrite <- IlistPerm3Cert_list_eq.
      intros i2' h4.
      do 2 rewrite <- (decode_Fin_unique _ _ (decode_Fin_match' _ _)).
      apply (IH _ _ _ _), h3.
    Qed.

    Lemma IlistPerm3Cert_list_function_ok (T: Set)(R: relation T)(l1 l2 : ilist T)(c: IlistPerm3Cert_list (lgti l1)) 
      (h: lgti l1 = lgti l2): IlistPerm3Cert R l1 l2 h c -> 
      forall i, R (fcti l1 i) (fcti l2 (rewriteFins h (IlistPerm3Cert_list_function c i))).
    Proof.
      intros h1 i.
      destruct l1 as [n l1] ; destruct l2 as [n2 l2] ; simpl in *|-*.
      revert l2 h1 ; rewrite <- h ; intros l2 h1 ; clear n2 h.
      rewrite <- (decode_Fin_unique _ _ (decode_Fin_match' _ _)).
      apply (IlistPerm3Cert_list_function_ok_n h1).
    Qed.
 
    Lemma IlistPerm3Cert_list_function_ok_cor (T: Set)(R: relation T)(n: nat)(l1 l2 : ilistn T n) 
      (c: IlistPerm3Cert_list n): IlistPerm3Cert R (mkilist l1) (mkilist l2) (eq_refl n) c -> 
      forall i, R (l1 i) (l2 (IlistPerm3Cert_list_function c i)).
    Proof.
      intros h1 i.
      assert (h3 : IlistPerm3Cert_list_function c i = rewriteFins 
        (eq_refl _ : lgti (mkilist l1) = lgti (mkilist l2)) (IlistPerm3Cert_list_function c i)).
      treatFinPure.
      rewrite h3.
      apply (IlistPerm3Cert_list_function_ok h1).
    Qed.

    End IlistPerm3_cert.
  
End IlistPerm_ind.

Section IlistPerm_bij.
   Inductive IlistPerm7 (T: Set)(R: relation T)(l1 l2 : ilist T): Prop := 
     perm7 : forall f g, Bijective f g -> (forall i, R (fcti l1 i) (fcti l2 (f i))) -> IlistPerm7 R l1 l2.

   Lemma IlistPerm7_refl (T: Set)(R: relation T)(Rrefl: Reflexive R)(l : ilist T) : IlistPerm7 R l l.
   Proof.
     apply (@perm7 _ R l l (fun x => x) (fun x => x)) ; try split ; reflexivity.
   Qed.

   Lemma IlistPerm7_sym (T: Set)(R: relation T)(Rsym: Symmetric R)(l1 l2 : ilist T) : 
     IlistPerm7 R l1 l2 -> IlistPerm7 R l2 l1.
   Proof.
     intros [f g h1 h2].
     apply (perm7 R _ _ (Bij_sym h1)).
     intro i.
     assert (h3 := h2 (g i)).
     destruct h1 as [h4 h5].
     rewrite (h5 _) in h3.
     apply Rsym, h3.
   Qed.
   
   Lemma IlistPerm7_trans (T: Set)(R: relation T)(Rrefl: Transitive R)(l1 l2 l3: ilist T) : 
     IlistPerm7 R l1 l2 -> IlistPerm7 R l2 l3 -> IlistPerm7 R l1 l3.
   Proof.
     intros [f1 g1 h1 h2] [f2 g2 h3 h4].
     apply (perm7  _ _ _ (Bij_trans h1 h3)).
     
     intro i.
     transitivity (fcti l2 (f1 i)).
     apply h2.
     apply h4.
   Qed.

   Add Parametric Relation (T: Set)(RelT: relation T)(EqT: Equivalence RelT) : (ilist T)(IlistPerm7 RelT) 
     reflexivity proved by (IlistPerm7_refl _)
     symmetry proved by (IlistPerm7_sym _)
     transitivity proved by (IlistPerm7_trans _)
   as IlistPerm7Rel.

   Lemma IlistPerm7_mon (U: Set)(l1 l2 : ilist U)(R1 R2 : relation U) :
     subrelation R1 R2 -> IlistPerm7 R1 l1 l2 -> IlistPerm7 R2 l1 l2.
   Proof.
     intros h1 [f g h2 h3].
     apply (perm7 R2 _ _ h2).
     intros i.
     apply (h1 _ _ (h3 i)).
   Qed.

   Lemma IlistPerm7_lgti (T: Set)(R: relation T)(l1 l2 : ilist T) : IlistPerm7 R l1 l2 -> lgti l1 = lgti l2.
   Proof.
     intros [f g h _].
     apply (Fin_inj_aux h).
   Qed.

   Lemma Bijective_IP3Cl_function (n: nat)(c: IlistPerm3Cert_list n) : 
     Bijective (IlistPerm3Cert_list_function c) (IlistPerm3Cert_list_function_inv c).
   Proof.
     split.
     apply IP3Cl_function_inv_function_inv.
     apply IP3Cl_function_function_inv_inv.
   Qed.

   Lemma IlistPerm3_IlistPerm7 (T: Set)(R: relation T)(l1 l2 : ilist T) : 
     IlistPerm3 R l1 l2 -> IlistPerm7 R l1 l2.
   Proof.
     destruct l1 as [n l1] ; destruct l2 as [n2 l2].
     intros h1 ; assert (h2 := IlistPerm3_lgti h1) ; simpl in *|-* ; revert l1 l2 h1 ; rewrite <- h2 ; clear n2 h2;
     intros l1 l2 h1.
     destruct (IlistPerm3_IlistPerm3Cert (refl_equal _ : lgti (existT _ _ l1) = lgti (existT _ _ l2)) h1) as [c h2].
     fold (mkilist l1) (mkilist l2) in *|-*.
     apply (perm7 R (mkilist l1) (mkilist l2) (Bijective_IP3Cl_function _ c)).
     apply IlistPerm3Cert_list_function_ok_cor, h2.
   Qed.
   
   Lemma IlistPerm7_IlistPerm3 (T: Set)(R: relation T)(l1 l2 : ilist T) : 
     IlistPerm7 R l1 l2 -> IlistPerm3 R l1 l2.
   Proof.
     intros h1 ; assert (h := IlistPerm7_lgti h1).
     destruct l1 as [n l1] ; destruct l2 as [n2 l2] ; simpl in *|-* ; revert l1 l2 h1 ; rewrite <- h ;
     intros l1 l2 [f g [h1 h2] h3]; clear n2 h ; simpl in *|-*.
     
     induction n as [|n IH].
     apply IlistPerm3_nil ; reflexivity.
     apply (IlistPerm3_cons _ _ (first n : Fin (lgti (existT _ _ l1))) (f (first n) :  Fin (lgti (existT _ _ l2)))).
     apply h3.
     
     assert (hex1_aux := extroduce_lgti (existT _ _ l1) (first n)).
     assert (hex1 : forall i, fcti (extroduce (existT _ _ l1) (first n)) i = fcti (existT _ _ l1)
     (rewriteFins (eq_sym hex1_aux) (succ i))).
     intro i.
     rewrite extroduce_ok3'.
     f_equal.
     treatFinPure.
     apply le_0_n.
     
     assert (hex2_aux := extroduce_lgti (existT _ _ l2) (f (first n))).
     assert (hex21 : forall i, decode_Fin i < decode_Fin (f (first n)) -> 
     fcti (extroduce (existT _ _ l2) (f (first n))) i = 
     fcti (existT _ _ l2) (rewriteFins (eq_sym hex2_aux) (weakFin i))).
     intros i h4.
     rewrite extroduce_ok2' ; try assumption.
     f_equal.
     treatFinPure.
     
     assert (hex22 : forall i, decode_Fin (f (first n)) <=  decode_Fin i -> 
     fcti (extroduce (existT _ _ l2) (f (first n))) i = 
     fcti (existT _ _ l2) (rewriteFins (eq_sym hex2_aux) (succ i))).
     intros i h4.
     rewrite extroduce_ok3' ; try assumption.
     f_equal.
     treatFinPure.
     
     revert hex1_aux hex1 hex2_aux hex21 hex22.
     set (l1' := extroduce (existT _ _ l1) (first n)) ; set (l2' := extroduce (existT _ _ l2) (f (first n))).
     assert (h4 := refl_equal _ : l1' =  extroduce (existT _ _ l1) (first n)) ; 
     assert (h5 := refl_equal _ : l2' =  extroduce (existT _ _ l2) (f (first n))).
     destruct l1' as [n' l1'] ; destruct l2' as [n2' l2'].
     assert (h6 : n' = n2').
     change (lgti (existT (fun n : nat => ilistn T n) _ l1') = lgti (existT (fun n : nat => ilistn T n) _ l2')).
     rewrite h4, h5.
     apply extroduce_lgti_S.
     assert (h7 : n' = n).
     change (lgti (existT (fun n : nat => ilistn T n) _ l1') = n).
     apply eq_add_S.
     rewrite h4, <- extroduce_lgti.
     reflexivity.
     revert l1' l2' h4 h5 ; rewrite <- h6, h7 ; intros l1' l2' h4 h5.
     simpl.
     intros hex1_aux hex1 hex2_aux hex21 hex22; 
     clear n' n2' h6 h7.
     
     assert (hex1' : forall i, l1' i = l1 (succ i)).
     intro i.
     assert (h6 : succ i = rewriteFins (eq_sym hex1_aux) (succ i)) by treatFinPure.
     rewrite h6 ; apply hex1.
     assert (hex21' : forall i, decode_Fin i < decode_Fin (f (first n)) -> l2' i = l2 (weakFin i)).
     intros i h6.
     assert (h7 : weakFin i = rewriteFins (eq_sym hex2_aux) (weakFin i)) by treatFinPure.
     rewrite h7 ; apply hex21, h6.
     assert (hex22' : forall i, decode_Fin (f (first n)) <= decode_Fin i -> l2' i = l2 (succ i)).
     intros i h6.
     assert (h7 : succ i = rewriteFins (eq_sym hex2_aux) (succ i)) by treatFinPure.
     rewrite h7 ; apply hex22, h6.
     clear hex1_aux hex2_aux hex1 hex21 hex22.
     
     fold (mkilist l1') (mkilist l2') in *|-*.
     
     assert (h6 : forall i, decode_Fin (f (first n)) <> decode_Fin (f (@succ n i))).
     intros i h6.
     apply decode_Fin_unique, (f_equal g) in h6.
     do 2 rewrite h1 in h6.
     inversion h6.
     set (f' := fun i => index_in_extroduce _ _ (h6 i)).
     
     assert (h7 : forall i, decode_Fin (first n) <> decode_Fin (g (extroduce_Fin (f (first n)) i))).
     intro i.
     unfold extroduce_Fin, sumbool_rec, sumbool_rect.
     elim (le_lt_dec (decode_Fin (f (first n))) (decode_Fin i)) ; intros a h7 ;
     apply decode_Fin_unique, (f_equal f) in h7 ; rewrite h2 in h7 ; rewrite h7 in a.
     apply (le_Sn_n _ a).
     rewrite weakFin_ok in a.
     apply (lt_irrefl _ a).
     set (g' := fun i => index_in_extroduce _ _ (h7 i)).
     
     apply (IH _ _ f' g') ; intros i; unfold f', g' ; clear f' g'.
     assert (h8 : decode_Fin (first n) < decode_Fin (g (extroduce_Fin (f (first n))
     (index_in_extroduce (f (first n)) (f (succ i)) (h6 i))))).
     rewrite (index_from_in_extroduce _ _ (h6 i)), h1. 
     apply lt_0_Sn.
     apply decode_Fin_unique, eq_add_S.
     rewrite index_in_extroduce_decode1, (index_from_in_extroduce _ _ (h6 i)), h1 ; try assumption.
     reflexivity.
     
     elim (lt_eq_lt_dec (decode_Fin (f (first n))) (decode_Fin (f (succ (index_in_extroduce (first n)
       (g (extroduce_Fin (f (first n)) i)) (h7 i)))))) ; try intros [a|a] ; try intros a ; 
     apply decode_Fin_unique.
     apply eq_add_S.
     rewrite index_in_extroduce_decode1 ; try assumption.
     
     elim (lt_eq_lt_dec (decode_Fin (first n)) (decode_Fin (g (extroduce_Fin (f (first n)) i)))) ; 
     try intros [b|b] ; try intros b.
     rewrite (decode_Fin_unique _ _ (index_in_extroduce_decode1 _ _ (h7 _) b : decode_Fin (succ _) = _)), h2.
     elim (le_lt_dec (decode_Fin (f (first n))) (decode_Fin i)) ; intros c.
     rewrite extroduce_Fin_ok1 ; try assumption.
     reflexivity.
     apply False_rec.
     rewrite (decode_Fin_unique _ _ (index_in_extroduce_decode1 _ _ (h7 _) b : decode_Fin (succ _) = _)), h2 in a.
     rewrite extroduce_Fin_ok2, weakFin_ok in a ; try assumption.
     apply (lt_irrefl _ (lt_trans _ _ _ a c)).
     contradiction (h7 i).
     inversion b.
     
     apply decode_Fin_unique, (f_equal g) in a.
     do 2 rewrite h1 in a.
     inversion a.
     
     rewrite index_in_extroduce_decode2 ; try assumption.
     revert a ; set (h8 := h7 i) ; generalize h8 ; clear h8.
     elim (le_lt_dec (decode_Fin (f (first n))) (decode_Fin i)) ; intros b.
     rewrite extroduce_Fin_ok1 ; try assumption.
     intros h8 a.
     elim (lt_eq_lt_dec (decode_Fin (first n)) (decode_Fin (g (succ i)))) ; try intros [c|c] ; try intros c.
     rewrite (decode_Fin_unique _ _ (index_in_extroduce_decode1 _ _ h8 c : decode_Fin (succ _) = _)), h2 in a.
     apply False_rec, (le_Sn_n _ (lt_le_weak _ _ (lt_le_trans _ _ _ a b))).
     contradiction c.
     inversion c.
     
     rewrite extroduce_Fin_ok2 ; try assumption.
     intros h8 a.
     elim (lt_eq_lt_dec (decode_Fin (first n)) (decode_Fin (g (weakFin i)))) ; try intros [c|c] ; try intros c.
     rewrite (decode_Fin_unique _ _ (index_in_extroduce_decode1 _ _ h8 c : decode_Fin (succ _) = _)), h2.
     apply weakFin_ok.
     contradiction c.
     inversion c.
     
     set (h8 := h6 i) ; generalize h8 ; clear h8 ; intros h8.
     rewrite hex1'.
     
     assert (h9 : l2' (index_in_extroduce (f (first n)) (f (succ i)) h8) = l2 (f (succ i))).
     rewrite (index_in_extroduce_ok_cor l2 _ _ h8).
     set (h9 := extroduce_lgti_S l2 (f (first n))).
     generalize h9 ; clear h9.
     change (mkilist l2' = extroduce (mkilist l2) (f (first n))) in h5.
     rewrite <- h5.
     intros h9.
     simpl.
     f_equal.
     treatFinPure.
     
     rewrite h9.
     apply h3.
   Qed.
     
  End IlistPerm_bij.
