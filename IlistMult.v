(** IlistMult.v Version 0.9.3.1 April 2016 *)
(** runs under V8.5pl1 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides an implementation of the Ilist version that allows 
     to represent multiplicities. It also provides various properties 
     and lemmas about it *)

(** this is code that conforms to the description in the article
    " Coinductive graph representation: the problem of embedded lists"
    by the authors *)


Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Fin.
Require Import ListEq.
Require Import Ilist.
Set Implicit Arguments.

(* In this file we define functions and sets that will act like list 
   without being lists and taking into account multiplicities*)
Section ilistnMult_def_tools. 

  Variable T: Set. 

  (* Definition of the property of multiplicity *)
  Definition PropMult (inf: nat) (sup: option nat)(i : nat): Prop := 
    match sup with 
      Some s => i >= inf /\ i <= s
    | None => i >= inf 
    end.

  (* Definition of the function *)
  Definition ilistnMult (inf: nat)(sup: option nat)(i: nat):= 
    {l: ilistn T i | PropMult inf sup i}.

  Definition fctin  (inf: nat)(sup: option nat)(i: nat)
    (l: ilistnMult inf sup i) : ilistn T i := proj1_sig l.
    
  Definition propin (inf: nat)(sup: option nat)(i: nat)
    (l: ilistnMult inf sup i): PropMult inf sup i := proj2_sig l.

End ilistnMult_def_tools.

Program Definition inMMapP (T U:Set) (f:T->U)(n: nat)(m: option nat)(i: nat)
  (l:ilistnMult T n m i) : ilistnMult U n m i := 
  fun fi => f (l fi).
Next Obligation. 
  destruct l as [l p].
  assumption.
Defined.

Definition inMMap (T U:Set) (f:T->U)(n: nat)(m: option nat)(i: nat)
  (l:ilistnMult T n m i) : ilistnMult U n m i.
Proof.
  destruct l as [l p].
  unfold ilistnMult.
  exists (fun x => f (l x)).
  assumption.
Defined.

Section ilistMult_def_tools.
	
  (* Definition of the couple *)
  Definition ilistMult(T:Set)(inf: nat) (sup: option nat) := 
  {n: nat & ilistnMult T inf sup n}.

  (* Basic operations on ilistMult *)
  Definition lgtiMult(T: Set)(n: nat)(m: option nat)(i: ilistMult T n m): nat:= 
    projS1 i.

  Definition fctiMult(T: Set)(n: nat)(m: option nat)(i: ilistMult T n m): 
    ilistnMult T n m (lgtiMult i) := projT2 i.
  
  Definition ffctiMult (T: Set)(n: nat)(m: option nat)(i: ilistMult T n m): 
    Fin (lgtiMult i) -> T := fctin (fctiMult i).

  (* Definition of the equivalent for map on ilistMult *)
  Definition iMMap(T U:Set) (f:T->U) (n: nat)(m: option nat)
   (l:ilistMult T n m): ilistMult U n m := 
   existS (ilistnMult U n m) (lgtiMult l) (inMMap f (fctiMult l)).

  Definition iMMap0(T U:Set) (f:T->U) (n: nat)(m: option nat)
   (l:ilistMult T n m): ilistMult U n m.
  Proof.
    destruct l as [i [l p]].
    exists i.
    exists (fun x => (f (l x))).
    assumption.
  Defined.

  (* Equivalent for forall on ilistMult *)
  Program Definition iMAllP(T:Set)(p:T->Prop)(n: nat)(m: option nat)
    (l: ilistMult T n m): Prop := 
    forall (f: Fin (lgtiMult l)), p (fctiMult l f). 

  Definition iMAll(T:Set)(p:T->Prop)(n: nat)(m: option nat)
    (l: ilistMult T n m): Prop := 
    forall (f: Fin (lgtiMult l)), p (ffctiMult l f).

  Lemma iMultMap_lgti: 
    forall (T U: Set)(n: nat)(m: option nat)(i: ilistMult T n m)(f: T -> U), 
    lgtiMult (iMMap f i) = lgtiMult i.
  Proof.
    reflexivity.
  Qed.

  Lemma iMMap_f: forall (T U: Set)(cmpU: relation U)(cmpUR: Equivalence cmpU)
    (f: T -> U)(inf: nat)(sup: option nat)(i: ilistMult T inf sup)
    (fi: Fin (lgtiMult i)), 
    cmpU (ffctiMult (iMMap f i) fi) (f (ffctiMult i fi)).
  Proof.
    intros T U cmpU [cmpU_refl cmpU_sym cmpU_trans] f inf sup [n [p i]] fi.
    reflexivity.
  Qed.

  (* Definition of a more general relation on ilistMult *)
  Inductive imeq (T:Set)(cmp: T->T->Prop)(n: nat) (m: option nat)
  (l1 l2: ilistMult T n m):Prop :=
    is_imeq: (forall (h: lgtiMult l1 = lgtiMult l2), 
        (forall (f:Fin(lgtiMult l1)), cmp (ffctiMult l1 f) 
        (ffctiMult l2 (rewriteFins h f))) 
        -> imeq cmp l1 l2).

  Section prImeq.
    
    (* Proof that imeq is an equivalence relation *)
    Lemma imeq_refl (T:Set) (cmp: T->T->Prop)(cmpRel: Equivalence cmp):
      forall (n: nat)(m: option nat)(l: ilistMult T n m), imeq cmp l l.
    Proof.
      intros n m i.
      destruct cmpRel as  [cmp_refl _ _].
      apply (is_imeq cmp i i (refl_equal (lgtiMult i))).
      intros f.
      apply cmp_refl.
    Qed.

    Lemma imeq_sym (T:Set) (cmp: T->T->Prop)(cmpRel: Equivalence cmp):
      forall (n: nat)(m: option nat)(l1 l2: ilistMult T n m), 
      imeq cmp l1 l2 -> imeq cmp l2 l1.
    Proof.
      destruct cmpRel as [_ cmp_sym _]. 
      intros n m l1 l2 [e H].
      apply (is_imeq cmp l2 l1 (sym_eq e)).
      intros f.
      apply cmp_sym.
      assert (H1 : f = rewriteFins e (rewriteFins (eq_sym e) f)) by treatFinPure.
      rewrite H1 at 2.
      apply H.
    Qed.
 
    Lemma imeq_trans (T:Set) (cmp: T->T->Prop)(cmpRel: Equivalence cmp): 
      forall (n: nat) (m: option nat)(l1 l2 l3: ilistMult T n m), 
      imeq cmp l1 l2 -> imeq cmp l2 l3 -> imeq cmp l1 l3.
    Proof.
      destruct cmpRel as [_ _ cmp_trans]. 
      intros n m l1 l2 l3 [e1 h1] [e2 h2].
      apply (is_imeq cmp l1 l3 (trans_eq e1 e2)).
      intros f.
      assert (H1: rewriteFins (eq_trans e1 e2) f = rewriteFins e2 (rewriteFins e1 f)).
      treatFinPure.
      rewrite H1.
      apply (cmp_trans _ _ _ (h1 f) (h2 _)).
    Qed.
   
    Add Parametric Relation(T: Set)(n: nat)(m: option nat)(cmp: T -> T -> Prop)
      (cmpRel: Equivalence cmp): (ilistMult T n m) (@imeq T cmp n m)
      reflexivity proved by (@imeq_refl T cmp cmpRel n m)
      symmetry proved by (@imeq_sym T cmp cmpRel n m)
      transitivity proved by (@imeq_trans T cmp cmpRel n m)
      as imeqRel.
  End prImeq.

  Definition get_imeq_cmp_eq_lgt(T: Set)(n: nat)(m: option nat)(cmp : T -> T -> Prop)
    (l1 l2: ilistMult T n m)(h:imeq cmp l1 l2) :
    lgtiMult l1= lgtiMult l2.
  Proof.
    destruct h as [e _].
    assumption.
  Defined.
  
  Lemma imeq_cmp_i: forall (T:Set)(n: nat)(m: option nat)(cmp: T -> T -> Prop)
    (l1 l2: ilistMult T n m)(h: lgtiMult l1 = lgtiMult l2)
    (H : (∀f : Fin (lgtiMult l1), cmp (ffctiMult l1 f)
    (ffctiMult l2 match h in (_ = l) return (Fin l) with refl_equal => f end))),
    (forall (i: Fin (lgtiMult l2)), 
    (cmp (ffctiMult l1 match (sym_eq h) in (_ = l) return Fin l with refl_equal => i end)
    (ffctiMult l2 i))).
  Proof.
    intros T n m cmp l1 l2 e h f.
    set (H':= (h match sym_eq e in (_ = l) return (Fin l) with
      | refl_equal => f end)).
    rewrite <- (match_eq_sym_eq f e) in H'.
    apply H'.
  Qed.
  

End ilistMult_def_tools.

(* Proof that ther exists a bijection between ilistMult and list *)
Section Bij_ilistMult_list.
  Variable T: Set.
  Variable comp : T -> T -> Prop.
  Variable compRel: Equivalence comp.
  Variable inf: nat.
  Variable sup: option nat. 

  Add Parametric Morphism (i: ilistMult T inf sup): 
    (@ffctiMult T inf sup i)
    with signature (eq(A:= Fin (lgtiMult i))) ==> (comp)
  as fctiMM.
  Proof.
    reflexivity.
  Qed.


  Definition ilistM2list (i: ilistMult T inf sup): list T := 
    map (ffctiMult i) (makeListFin (lgtiMult i)).

  Definition eq_comp_morph (n : nat) (f: Fin (n) -> T) := 
    Morphism (eq(A:= Fin (n)) ==> comp) f.

  Definition fctiiMM (i: ilistMult T inf sup): 
    Morphism (eq(A:= Fin (lgtiMult i)) ==> comp) (ffctiMult i).
  Proof.
    unfold Proper.
    reflexivity.
  Qed.

  Definition iM (n: nat)(i: ilistnMult T inf sup n): 
    Morphism (eq(A:= Fin n) ==> comp) (fctin i).
  Proof.
    unfold Proper.
    reflexivity.
  Qed.

  (* proof that this translation is correct *)
  Lemma ilistM2list_all_elem_ilistM_in_list (i: ilistMult T inf sup): 
    iMAll (fun x => In x (ilistM2list i)) i.
  Proof.
    intro f.
    apply in_map.
    apply all_Fin_n_in_makeListFin.
  Qed.

  Lemma ilistM2list_all_elem_list_in_ilistM(i: ilistMult T inf sup): 
    forall f: Fin(lgtiMult i), In (ffctiMult i f) (ilistM2list i).
  Proof.
    intros f.
    apply in_map.
    apply all_Fin_n_in_makeListFin.
  Qed.
    
  Lemma ilistM2list_nth: 
    forall (t: T)(i: ilistMult T inf sup)(n: nat)(h: n < lgtiMult i), 
      comp (ffctiMult i (code_Fin1 h)) 
      (nth n (ilistM2list i) (ffctiMult i (code_Fin1 h))).
  Proof.
    intros t i n h.
    unfold ilistM2list.
    rewrite map_nth.
    rewrite nth_makeListFin at 1.
    reflexivity.
  Qed.

  Lemma length_ilistM2list: forall (i: ilistMult T inf sup), 
    length (ilistM2list i) = lgtiMult i.
  Proof.
    intros i.
    unfold ilistM2list.
    rewrite map_length.
    apply (makeListFin_nb_elem_ok).
  Qed.

  Lemma lgtiMult_map_ilistM2list: 
    forall (U: Set)(l: ilistMult T inf sup)(f: T -> U), 
    length (map f (ilistM2list l)) = lgtiMult l.
  Proof.
    intros U l f.
    rewrite map_length.
    apply length_ilistM2list.
  Qed.

  Lemma ilistM2list_nth2: forall (i: ilistMult T inf sup)(f: Fin (lgtiMult i)),
    comp (ffctiMult i f) 
         (nth (decode_Fin f) (ilistM2list i) (ffctiMult i f)).
  Proof.
    intros i f.
    unfold ilistM2list.
    rewrite map_nth.
    rewrite <- (code1_decode_Id f) at 1.
    rewrite nth_makeListFin at 1.
    rewrite code1_decode_Id.
    reflexivity.
  Qed.

  Lemma ilistM2list_nth3: 
    forall (t: T)(i: ilistMult T inf sup)(f: Fin (lgtiMult i)),
    comp (ffctiMult i f) (nth (decode_Fin f) (ilistM2list i) t).
  Proof.
    intros t i f.
    assert (H: decode_Fin f < length (ilistM2list i)).
    rewrite length_ilistM2list.
    apply decode_Fin_inf_n.
    rewrite (nth_indep (ilistM2list i) t (ffctiMult i f) H).
    apply ilistM2list_nth2.
  Qed.

  Program Definition list2ilistM (l: list T)(p: PropMult inf sup (length l)): 
    ilistMult T inf sup:=
    existS (ilistnMult T inf sup) (length l) (list2Fin_T l).

  Lemma lgtiM_length : forall (l: list T)(p: PropMult inf sup (length l)), 
    length l = lgtiMult (list2ilistM l p).
  Proof.
    reflexivity.
  Qed.

  Lemma list2ilistM_lgtiM_cons: 
    forall (a: T) (l: list T)(p1: PropMult inf sup (length l))
    (p2: PropMult inf sup (length (a::l))), 
     S (lgtiMult (list2ilistM l p1)) = lgtiMult (list2ilistM (a :: l) p2).
  Proof.
    reflexivity.
  Qed.

  (* proof that this translation is correct *)
  Lemma list2ilistM_all_elem_ilistM_in_list(l: list T)
    (p: PropMult inf sup (length l)): iMAll (fun x => In x l) (list2ilistM l p).
  Proof.
    intro f.
    elim (zerop (decode_Fin f)) ; intros a ;
    destruct l as [| h l].
    inversion f.
    left.
    refine (match (sym_eq a) in (_ = df) return 
      h = match df with 0 => h | S m => nth m l h end 
      with refl_equal => _ end).
    reflexivity.
    inversion f.
    right.
    inversion a as [e | n H e].
    refine (match e in (_ = df) return 
      In match df with 0 => h | S m => nth m l h end l 
      with refl_equal => _ end).
    destruct l as [| ht l].
    apply 
      (lt_irrefl _ (gt_le_trans _ _ _ a (gt_S_le _ _ (decode_Fin_inf_n f)))).
    left ; reflexivity.
    refine (match e in (_ = df) return 
      In match df with 0 => h | S m => nth m l h end l 
      with refl_equal => _ end).
    assert (H': n < (length l)).
    apply lt_S_n.
    rewrite e.
    apply decode_Fin_inf_n.
    apply (nth_In _ _ H').
  Qed.

  Definition inf_length_lgtiM (n: nat)(l: list T)(h: n < length l)
    (p: PropMult inf sup (length l)): n < lgtiMult (list2ilistM l p).
  Proof.
    rewrite (lgtiM_length _ p) in h.
    assumption.
  Defined.

  Lemma list2ilistM_nth: 
    forall (n: nat)(l: list T)(h: n < length l)(t: T) (p: PropMult inf sup _),
    comp (nth n l t) (proj1_sig (fctiMult (list2ilistM l p)) 
      (code_Fin1 (inf_length_lgtiM l h p))).
  Proof.
    destruct n as [|n]; intros l h t p;
    destruct l as [| hd l].
    inversion h.
    simpl.
    rewrite code_Fin1_Sn_0.
    reflexivity.
    inversion h.
    simpl in h.
    simpl nth.
    assert (h':= lt_le_S _ _ (lt_S_n _ _ h)).
    assert (H: decode_Fin (code_Fin1_Sn (lt_n_Sm_le (S n) (length l) 
      (inf_length_lgtiM (hd :: l) h p)))=
    S n).
    rewrite (code_Fin1_Sn_proofirr _ h').
    revert n h h'.
    induction (length l) as [| ll IHll] ; intros n h h'.
    inversion h'.
    rewrite code_Fin1_Sn_S.
    simpl.
    f_equal.
    assert (h1 := le_S_n _ _ h').
    rewrite (code_Fin1_Sn_proofirr _ h1).
    destruct n as [|n].
    rewrite code_Fin1_Sn_0.
    reflexivity.
    apply (IHll _ (lt_S_n _ _ h)).
    simpl.
    rewrite H.
    apply (nth_indep_comp _ l t hd h').
  Qed.
    
  Lemma list2ilistM_nth2: forall (l: list T)(p: PropMult _ _ _)
    (f: Fin (lgtiMult (list2ilistM l p)))(t: T),
    comp (nth (decode_Fin f) l t) (ffctiMult (list2ilistM l p) f).
  Proof.
    intros l p f t.
    unfold ffctiMult.
    unfold fctin.
    destruct l as [|hd l].
    inversion f.
    simpl.
    simpl in f.
    elim (zerop (decode_Fin f)); intros a.
    rewrite a; reflexivity.
    inversion a as [e| n H e] ; 
    assert (h:= decode_Fin_inf_n f).
    destruct l as [|hhd l].
    rewrite <- e in h.
    apply False_rec.
    apply (lt_irrefl _ h).
    reflexivity.
    apply (nth_indep_comp _ _ _ _).
    rewrite <- e in h.
    apply (lt_S_n _ _ h).
  Qed.
    
  Lemma lgtiM_list2ilistM: forall (l: list T)(p: PropMult inf sup (length l)), 
    lgtiMult (list2ilistM l p) = length l.
  Proof.
    reflexivity.
  Qed.

  Lemma list2ilistM_ilistM2list_id : forall (i: ilistMult T inf sup), 
    imeq comp (list2ilistM (ilistM2list i) 
    match sym_eq (length_ilistM2list _) in (_=x) return PropMult _ _ x 
    with refl_equal => (propin (fctiMult i)) end) i.
  Proof.
    intros i.
    set (p := match sym_eq (length_ilistM2list _) in (_=x) return PropMult _ _ x 
    with refl_equal => (propin (fctiMult i)) end).
    assert (h : lgtiMult (list2ilistM (ilistM2list i) p) = lgtiMult i).
    rewrite lgtiM_list2ilistM.
    apply length_ilistM2list.
    apply (is_imeq _ _ _ h).
    intros f.
    rewrite <- (list2ilistM_nth2 _ _ _ 
      (ffctiMult (list2ilistM (ilistM2list i) p) f)).
    rewrite (decode_Fin_match f h).
    rewrite <- (ilistM2list_nth3
      (ffctiMult (list2ilistM (ilistM2list i) p) f)).
    reflexivity.
  Qed.

  Lemma list2Fin_T_succ: forall (l: list T)(a: T)(x: Fin (length l)),
    comp (list2Fin_T (a :: l) (succ x)) (list2Fin_T l x).
  Proof.
   induction l as [|hd l]; intros a f.
   inversion f.
   simpl.
   elim (zerop (decode_Fin f)); intros b.
   refine (match (sym_eq b) as b' in ( _ = df) return 
   (comp match df with 0 => hd | S m => _ end  
    match df with 0 => hd | S m => _ end) with refl_equal => _ end).
   reflexivity.
   inversion b as [e | n H e].
   destruct l as [|hhd l].
   apply False_rec.
   assert (H:= decode_Fin_inf_n f) ; simpl in H.
   rewrite e in H.
   apply (lt_irrefl _ H).
   reflexivity.
   assert (H1:= decode_Fin_inf_n f); simpl in H1.
   rewrite <- e in H1.
   apply (lt_S_n n (length l)) in H1.
   apply (nth_indep_comp compRel l a hd H1).
  Qed.

  Lemma list2Fin_T_succ_map: 
    forall (l: list T)(a: T)(lf: list (Fin (length l))), 
     ListEq comp (map (fun x : Fin (length l) => list2Fin_T l x) lf)
       (map (fun x : Fin (length l) => list2Fin_T (a :: l) (succ x)) lf).
  Proof.
    intros l a ; induction lf as [| hd lf].
    apply ListEq_nil.
    apply ListEq_cons.
    rewrite list2Fin_T_succ.
    reflexivity.
    apply IHlf.
  Qed.


  Lemma ilistM2list_list2ilistM_id : forall (l: list T)(p: PropMult inf sup _),
   ListEq comp (ilistM2list (list2ilistM l p)) l.
  Proof.
    intros l p.
    unfold ilistM2list.
    unfold ffctiMult.
    unfold fctin.
    simpl.
    clear p.
    induction l as [|hd l].
    reflexivity.
    simpl.
    apply ListEq_cons.
    reflexivity.
    rewrite (map_map_ListEq (A:= Fin (length l))(B:= Fin (S (length l))) 
      compRel).
    change (ListEq comp (map (fun x => list2Fin_T (hd::l) (succ x)) (makeListFin (length l))) l).
    rewrite <- list2Fin_T_succ_map.
    apply IHl.
  Qed.

  Program Definition ilistMM (n: nat)(p: PropMult inf sup n)
    (l: ilistnMult T inf sup n): Morphism (eq(A:= Fin n) ==> comp) l.
  Proof.
    unfold Proper.
    reflexivity.
  Qed.

  Definition iMfilter (i: ilistMult T inf sup)(P: T -> bool) := 
    list2ilistM (filter P (ilistM2list i)).

  End Bij_ilistMult_list.

  Section imeq_ListEq.
  Variable inf: nat.
  Variable sup: option nat.

  Lemma imeq_ListEq_eq: forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)
    (i1 i2: ilistMult T inf sup), 
    imeq eqT i1 i2 <-> ListEq eqT (ilistM2list i1) (ilistM2list i2).
  Proof.
    intros T eqT eqTRel i1 i2 ; split ; intros H ;
    destruct i1 as [n1 i1]; destruct i2 as [n2 i2].
    destruct H as [e H].
    simpl in e.
    revert i2 H; rewrite <- e ; simpl ; clear e n2 ; intros i2 H.
    unfold ilistM2list ; simpl.
    destruct n1 as [|n1].
    reflexivity.
    simpl.
    apply ListEq_cons.
    apply H.
    apply (ListEq_map_f_g _ _ _ _ H).

    assert (H1 := ListEq_length H).
    unfold ilistM2list in H1.
    do 2 rewrite map_length, makeListFin_nb_elem_ok in H1 ; simpl in H1.
    revert i2 H ; rewrite <- H1 ; clear n2 H1 ; intros i2 H.
    apply (is_imeq _ _ _ (refl_equal _ :  
      lgtiMult (existT (fun n : nat => ilistnMult T inf sup n) n1 i1) = 
      lgtiMult (existT (fun n : nat => ilistnMult T inf sup n) n1 i2))) ; intro f.
    apply (ListEq_eq eqTRel _ _ _ H _ (all_Fin_n_in_makeListFin f)).
  Qed.

  Lemma ListEq_imeq_eq: 
    forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)(l1 l2: list T)
    (p1: PropMult inf sup (length l1))(p2: PropMult inf sup (length l2)), 
    imeq eqT (list2ilistM _ _ _ p1) (list2ilistM _ _ _ p2) <-> ListEq eqT l1 l2.
  Proof.
    intros T eqT eqTR l1 l2 p1 p2.
    set (i1 := list2ilistM _ _ l1 p1); set (i2 := list2ilistM _ _ l2 p2).
    rewrite <- (ilistM2list_list2ilistM_id _ inf sup l1).
    rewrite <- (ilistM2list_list2ilistM_id _ inf sup l2).
    apply (imeq_ListEq_eq eqTR).
  Qed.

  End imeq_ListEq.

  Add Parametric Morphism (T: Set)(inf: nat)(sup: option nat)(eqT: relation T)
    (eqTR: Equivalence eqT): (@ilistM2list T inf sup)
    with signature (@imeq T eqT inf sup) ==> (ListEq eqT)
  as ilistM2listM.
  Proof.
    intros x y h.
    apply (imeq_ListEq_eq eqTR x y).
    assumption.
  Qed.

  Lemma map_iMMap_ilistM_list: forall (T U: Set)(inf: nat)(sup: option nat)
    (i: ilistMult T inf sup)(f: T -> U)
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Morphism (compT ==> compU) f), 
    imeq compU (iMMap f i) 
               (list2ilistM _ _ (map f (ilistM2list i)) 
    match sym_eq (lgtiMult_map_ilistM2list _ _) in (_=x) return PropMult _ _ x 
    with refl_equal => (propin (fctiMult i)) end).
  Proof.
    intros T U inf sup i f compT compTRel compU compURel fM.
    set (p := match sym_eq (lgtiMult_map_ilistM2list i f) in (_ = x) 
      return (PropMult inf sup x) with refl_equal => propin (fctiMult i) end).
    assert (H: lgtiMult (iMMap f i) = 
      lgtiMult (list2ilistM inf sup (map f (ilistM2list i)) p)).
    simpl.
    rewrite map_length.
    apply (sym_eq (length_ilistM2list i)).
    apply (is_imeq _ _ _ H); intro fi ;
    destruct i as [[|n] i].
    inversion fi.
    simpl in H ,p.
    rewrite <- (code1_decode_Id fi) at 1.
    unfold ffctiMult, fctin.
    simpl.
    rewrite <- decode_Fin_match'.
    elim (zerop (decode_Fin fi)); intros a ;
    destruct i as [i pp].
    refine (match (sym_eq a) in (_ = df) return 
    compU _ match df with 0 => f (i (first n)) | S m => _ end
    with refl_equal => _ end).
    rewrite (decode_Fin_0_first _ a).
    rewrite code_Fin1_Sn_0.
    reflexivity.
    inversion a as [e | m H1 e].

    destruct n as [|n].
    rewrite (Fin_first_1 fi) in e.
    inversion e.

    rewrite (decode_Fin_unique fi (succ (first n)) (sym_eq e)).
    simpl.
    rewrite code_Fin1_Sn_S.
    rewrite code_Fin1_Sn_0.
    reflexivity.
    unfold ffctiMult.
    unfold fctin.
    simpl.
   
    do 2 rewrite map_map.

    refine (match e in (_ = df) return 
    compU _ match df with 0 => _ | S m => 
      nth m (List.map (fun x : Fin n => f (i (@succ n x))) (makeListFin n)) (f (i (first n)))
    end with refl_equal => _ end).
    rewrite <- (map_map (fun x => i (succ x)) f), <- (map_map (@succ _) i).
    rewrite (map_map_nth_comp compTRel compURel i fM).
    assert (H2 := (lt_n_Sm_le (decode_Fin fi) n (decode_Fin_inf_n fi))).
    rewrite (code_Fin1_Sn_proofirr _ H2).
    revert H2 ; simpl ; rewrite <- e; intro H2.
    destruct n as [|n].
    inversion H2.

    rewrite (nth_indep _ (first (S n)) (succ (first n))).
    rewrite map_nth.
    rewrite code_Fin1_Sn_S.
    rewrite <- (nth_makeListFin_def H2).
    simpl.
    rewrite (code_Fin1_Sn_proofirr _ (lt_n_Sm_le m n H2)).
    reflexivity.
    simpl.
    do 2 (rewrite map_length).
    rewrite makeListFin_nb_elem_ok.
    apply H2.
  Qed.

  Lemma list2Fin_T_succ_map_f: 
    forall (T U: Set) (l: list T)(a: T)(lf: list (Fin (length l)))(f: T -> U)
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Morphism (compT ==> compU) f), 
     ListEq compU (map (fun x : Fin (length l) => f( list2Fin_T l x)) lf)
       (map (fun x : Fin (length l) => f(list2Fin_T (a :: l) (succ x))) lf).
  Proof.
    intros T U l a lf f compT compTRel compU compURel fM.
    induction lf as [| hd lf IHlf].
    apply ListEq_nil.
    apply ListEq_cons.
    rewrite (list2Fin_T_succ compTRel).
    reflexivity.
    apply IHlf.
  Qed.

  Lemma iMMap_cons: forall (T U: Set)(a: T)(l: list T)(f: T -> U)
    (inf: nat)(sup: option nat)(p1: PropMult inf sup (length (a::l)))
    (p2: PropMult inf sup (length l))
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Morphism (compT ==> compU) f), 
    ListEq compU (ilistM2list (iMMap f (list2ilistM inf sup (a :: l) p1))) 
      (f a :: (ilistM2list (iMMap f (list2ilistM inf sup l p2)))).
  Proof.
    intros T U a l f inf sup p1 p2 compT compTRel compU compURel fM .
    rewrite (map_iMMap_ilistM_list (list2ilistM _ _ (a :: l) _) _ _ fM).
    rewrite (ilistM2list_list2ilistM_id compURel).
    simpl.
    apply ListEq_cons.
    reflexivity.
    unfold ilistM2list.
    do 2 (rewrite (map_map_ListEq compURel)).
    rewrite (list2Fin_T_succ_map_f l a _ compTRel compURel fM).
    reflexivity.
  Qed.

  Lemma iMMap_map_list_ilistM: forall (T U: Set)(l: list T)(f: T -> U)
    (inf: nat)(sup: option nat)(p: PropMult inf sup (length l))
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Morphism (compT ==> compU) f), 
    ListEq compU (map f l) (ilistM2list (iMMap f (list2ilistM inf sup l p))).
  Proof.
    intros T U l f inf sup p compT compTRel compU compURel fM.
    unfold ilistM2list.
    unfold ffctiMult.
    unfold fctin.
    simpl.
    clear p.
    induction l as [|hd l IHl].
    reflexivity.
    simpl.
    apply ListEq_cons.
    reflexivity.
    rewrite IHl.
    rewrite map_map.
    destruct l as [|hhd l] ; simpl.
    reflexivity.
    apply ListEq_cons.
    reflexivity.
    do 2 (rewrite map_map).
    apply ListEq_map_f_g.
    intro a.
    simpl.
    rewrite (nth_indep l hd hhd (decode_Fin_inf_n a)).
    reflexivity.
  Qed.

Section manip_ilistMult.
  Variable inf: nat.
  Variable sup: option nat.

  (* ilistMult with one single element *)
  Program Definition singletonMProg(T: Set)(p: PropMult inf sup 1)(t: T): 
    ilistMult T inf sup:= existS (ilistnMult T inf sup) 1 (fun i => t).

  Definition singletonM (T: Set)(p: PropMult inf sup 1)(t: T): ilistMult T inf sup:= 
    existS (ilistnMult T inf sup) 1 (exist _ (fun _ : Fin 1 => t) p).
  
  Lemma singletonM_lgtiMult: forall (T: Set)(p: PropMult inf sup 1)(t: T), 
    lgtiMult (singletonM p t) = 1.
  Proof.
    reflexivity.
  Qed.
  
  Lemma singletonM_ok: forall (T: Set)(p: PropMult inf sup 1)(t: T)
    (eqT: relation T)(eqTR: Equivalence eqT)(f: Fin (lgtiMult (singletonM p t))), 
      eqT (ffctiMult (singletonM p t) f) t.
  Proof.
    reflexivity.
  Qed.

  Definition f_aux (T: Set)(f: Fin 0): T.
  Proof.
    inversion f.
  Defined.

  (* Definitions on ilistMult *)
  Definition iMnil(T: Set)(p: PropMult inf sup 0): ilistMult T inf sup:= 
    existS (ilistnMult T inf sup) 0 (exist _ (f_aux T) p).

  Definition iMconsn (T: Set)(n: nat)(t: T)(p: PropMult inf sup (S n))
    (i: ilistnMult T inf sup n): ilistnMult T inf sup (S n) := 
    exist _ (iconsn t (fctin i)) p.

  Definition iMcons (T: Set)(t: T)(i: ilistMult T inf sup)
    (p:PropMult inf sup (S (lgtiMult i))) : ilistMult T inf sup:= 
    existS (ilistnMult T inf sup) (S (lgtiMult i)) (iMconsn t p (fctiMult i)).

  Lemma singletonM_eq_iMcons_iMnil: forall (T: Set)(eqT: relation T)
    (eqTR: Equivalence eqT)(p: PropMult inf sup 1)(p': PropMult inf sup 0)(t: T), 
    imeq eqT (singletonM p t) (iMcons t (iMnil T p') p).
  Proof.
    intros T eqT eqTR p p' t.
    assert (h: lgtiMult (singletonM p t) = lgtiMult (iMcons t (iMnil T p') p)).
    reflexivity.
    apply (is_imeq _ _ _ h).
    intro f.
    rewrite <- (decode_Fin_unique _ _ (decode_Fin_match' f h)).
    rewrite (Fin_first_1 f).
    reflexivity.
  Qed.

  (* next nat on option nat *)
  Definition Sop (n: option nat): option nat.
  Proof.
    destruct n as [n|].
    exact (Some (S n)).
    exact None.
  Defined.

  Lemma Sop_Some: 
    forall (n: option nat)(x: nat), n = Some x -> Sop n = Some (S x).
  Proof.
    intros n x h.
    rewrite h.
    reflexivity.
  Qed.

  Lemma Sop_None: forall (n: option nat), n = None -> Sop n = None.
  Proof.
    intros n h.
    rewrite h.
    reflexivity.
  Qed.
  
  Definition propMultS (n: nat)(p: PropMult inf sup n): 
    PropMult inf (Sop sup) (S n).
  Proof.
    destruct sup as [s|] ;
    [destruct p as [p p2] ; split |] ;
    try apply (lt_le_weak _ _ (le_lt_n_Sm _ _ p)).
    apply (le_n_S _ _ p2).
  Qed.

  Lemma iMcons_ok: forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)(t: T)
    (i: ilistMult T inf sup)(f: Fin (lgtiMult i))(p: PropMult inf sup (S (lgtiMult i))),
    eqT (ffctiMult i f) (ffctiMult (iMcons t i p) (succ f)).
  Proof.
    unfold ffctiMult ; unfold fctin.
    unfold iMcons ;unfold iMconsn; unfold iconsn; unfold get_cons; simpl.
    intros T eqT eqTR t [[|n] i] f p.
    inversion f.
    reflexivity.
  Qed.

  Lemma iMcons_first: forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)
    (t: T)(i: ilistMult T inf sup)(p: PropMult inf sup (S (lgtiMult i))),
    eqT t (ffctiMult (iMcons t i p) (first (lgtiMult i))).
  Proof.
    reflexivity.
  Qed.

End manip_ilistMult.

Section Exemple.

Inductive A1: Set := 
  mk_A1 : ilist B1 -> C1 -> A1 
with B1 : Set := 
  mk_B1 : ilist C1 -> B1 
with C1 : Set := 
  mk_C1 : C1.

CoInductive A: Set := 
  mk_A : ilistMult B 0 None -> ilistMult C 1 (Some 1) -> A 
with B : Set := 
  mk_B : ilistMult C 1 (Some 10)-> B 
with C : Set := 
  mk_C : B -> B -> C.

End Exemple.








