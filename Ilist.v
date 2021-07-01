(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides an implementation of Ilist 
     It also provides various properties and lemmas about it.  *)

Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Fin.
Require Import ListEq.
Require Import Basics.
Require Import Tools.

Set Implicit Arguments.

Lemma decode_Fin_succ (n:nat)(f:Fin n): decode_Fin(succ f)=S(decode_Fin f).
Proof.
  reflexivity.
Qed.

Create HintDb evalDecode_FinDb.
Hint Rewrite <- decode_Fin_match': evalDecode_FinDb.
Hint Rewrite decode_code1_Id: evalDecode_FinDb.
Hint Rewrite <- decode_Fin_get_cons: evalDecode_FinDb.
Hint Rewrite decode_Fin_succ: evalDecode_FinDb.

Ltac decode_Fin_get_cons_S := (apply eq_add_S || apply lt_S_n || apply le_S_n); 
                              rewrite <- decode_Fin_get_cons.
Ltac evalDecode_Fin := repeat (autorewrite with evalDecode_FinDb || decode_Fin_get_cons_S).
Ltac decode_Fin_get_cons_S_Ass c := (apply eq_S in c || apply lt_n_S in c || apply le_n_S in c); 
                                    rewrite <- decode_Fin_get_cons in c.
Ltac evalDecode_Fin_Ass c := repeat (autorewrite with evalDecode_FinDb in c || decode_Fin_get_cons_S_Ass c).

Ltac treatFinPureDebug := (try (apply decode_Fin_unique)); 
                          evalDecode_Fin; 
                          try (reflexivity || apply decode_Fin_inf_n).
Ltac treatFinPure := treatFinPureDebug; fail.
Ltac treatFinAss := (try (apply decode_Fin_unique)); 
                    evalDecode_Fin; 
                    try (assumption || reflexivity || apply decode_Fin_inf_n); 
                    fail.
Ltac treatFin c := (try (apply decode_Fin_unique)); 
                   let h:= fresh in assert (h := c); 
                                    evalDecode_Fin_Ass h;
                                    evalDecode_Fin; 
                                    try (exact c || exact h || reflexivity || apply decode_Fin_inf_n); 
                                    clear h; 
                                    fail.
Ltac treatFinDebug c := (try (apply decode_Fin_unique)); 
                        let h:= fresh in assert (h := c); 
                                         evalDecode_Fin_Ass h;
                                         evalDecode_Fin; 
                                         try (exact c || exact h || reflexivity || apply decode_Fin_inf_n).
(* let h:= fresh makes it clear that a fresh identifier has to be created *)

(* In this file we define functions and sets that will act like lists 
   without being lists *)
Section ilistn_def_tools. 

  Variable T: Set. 
  (* Definition of the function *)
  Definition ilistn(n:nat) := Fin n -> T.
End ilistn_def_tools. 
 
(* We define a pair (n, ilistn n) that mimics the behaviour of lists *)
Section ilist_def_tools.

  (* Definition of the pair *)
  Definition ilist(T:Set) := {n:nat & ilistn T n}.

  (* Basic operations on ilist *)

(* important definition that is nothing but an abbreviation *)
  Definition mkilist (T: Set)(n: nat)(i: ilistn T n): ilist T := existT (fun n => ilistn T n) n i.

  Definition lgti(T: Set)(i: ilist T): nat:= projT1 i.

  Definition fcti(T: Set)(i: ilist T): ilistn T (lgti i) := projT2 i.

  Lemma lgti_mkilist (T: Set)(n: nat)(i: ilistn T n): lgti(mkilist i) = n.
  Proof.
    reflexivity.
  Qed.

  Create HintDb evalLgti.
  Hint Rewrite lgti_mkilist: evalLgti.


  (* Definition of the analogue for map on ilists *)
  Definition imap (T U:Set) (f:T->U) (l:ilist T): ilist U :=
    mkilist (fun i => f (fcti l i)).

  (* Analogue for forall on ilists *)
  Definition iall(T:Set)(p:T->Prop)(l: ilist T): Prop := 
    forall i, p (fcti l i).

  Lemma imap_lgti: forall (T U: Set)(i: ilist T)(f: T -> U), 
    lgti (imap f i) = lgti i.
  Proof.
    reflexivity.
  Qed.

  (* Definition of a more general relation on ilist *)
  Inductive ilist_rel (T:Set) (R: T->T->Prop) (l1 l2: ilist T):Prop :=
    is_ilist_rel: forall h: lgti l1 = lgti l2,
        (forall f:Fin(lgti l1), 
          R (fcti l1 f) (fcti l2 (rewriteFins h f: Fin(lgti l2)))) -> ilist_rel R l1 l2.
 
  Definition getNFin (n n': nat) (H: Fin n = Fin n'): nat := n'.
  
  Section prLeq.
    
    (* Proof that ilist_rel preserves equivalence *)
    Lemma ilist_rel_refl: forall (T:Set) (R: T->T->Prop)(Rrefl: Reflexive R)(l: ilist T), 
      ilist_rel R l l.
    Proof.
      intros T R Rrefl i.
      apply (is_ilist_rel R i i (refl_equal (lgti i))).
      intros f.
      reflexivity.
    Qed.

    Lemma ilist_rel_sym : 
      forall (T:Set) (R: T->T->Prop)(Rsym: Symmetric R)(l1 l2: ilist T), 
        ilist_rel R l1 l2 -> ilist_rel R l2 l1.
    Proof.
      intros T R R_sym l1 l2 [e H].
      apply (is_ilist_rel R l2 l1 (sym_eq e)).
      intro f.
      assert (H1 : f = rewriteFins e (rewriteFins (eq_sym e) f)) by treatFinPure.
      rewrite H1 at 1.
      apply R_sym, H.
    Qed.

    Lemma ilist_rel_trans :
      forall (T:Set) (R: T->T->Prop)(Rtrans: Transitive R)(l1 l2 l3: ilist T), 
      ilist_rel R l1 l2 -> ilist_rel R l2 l3 -> ilist_rel R l1 l3.
    Proof.
      intros T R R_trans l1 l2 l3 [e1 h1] [e2 h2].
      apply (is_ilist_rel R l1 l3 (trans_eq e1 e2)).
      intro f.
      assert (h3 : rewriteFins (eq_trans e1 e2) f = rewriteFins e2 (rewriteFins e1 f)) by treatFinPure.
      rewrite h3.
      apply (R_trans _ _ _ (h1 f) (h2 (rewriteFins e1 f))).
    Qed.

    Add Parametric Relation(T: Set)(R: T -> T -> Prop)(RRel: Equivalence R):
      (ilist T) (ilist_rel R)
      reflexivity proved by (ilist_rel_refl _)
      symmetry proved by (ilist_rel_sym _)
      transitivity proved by (ilist_rel_trans _)
      as ilist_relRel.
  End prLeq.

  Add Parametric Morphism (T: Set)(eqT: relation T)
    (eqTR : Equivalence eqT)(p: T -> Prop)
    (pM: Proper (eqT --> impl) p): (iall p)
  with signature (ilist_rel eqT ==> impl)
  as iallM.
  Proof.
    intros i1 i2 Hilist_rel H f.
    apply (ilist_rel_sym _) in Hilist_rel.
    destruct Hilist_rel as [Heq Hilist_rel].
    assert (H' := H (rewriteFins Heq f)).
    apply (pM _ _ (Hilist_rel f) H').
  Qed.

  Definition ilist_rel_lgti:
    forall (T: Set)(R : T -> T -> Prop)(l1 l2: ilist T)(h:ilist_rel R l1 l2),
    lgti l1= lgti l2.
  Proof.
    intros T R l1 l2 [e _].
    assumption.
  Defined.
  
  Lemma ilist_rel_R_i: forall (T:Set)(R: T -> T -> Prop)
    (l1 l2: ilist T)(h: lgti l1 = lgti l2)
    (H : (∀f : Fin (lgti l1), R (fcti l1 f)
    (fcti l2 (rewriteFins h f)))),
    (forall (i: Fin (lgti l2)), 
    (R (fcti l1 (rewriteFins (sym_eq h) i)) (fcti l2 i))).
  Proof.
    intros T R l1 l2 e h f.
    rewrite <- (rewriteFins_sym e f) at 2.
    apply (h (rewriteFins (sym_eq e) f)).
  Qed.

  Lemma ilist_rel_mon (T: Set)(R1 R2: relation T)(HypR: subrelation R1 R2)(l1 l2: ilist T):
    ilist_rel R1 l1 l2 -> ilist_rel R2 l1 l2.
  Proof.
    intros [H1 H2].
    apply (is_ilist_rel _ _ _ H1).
    intro i1.
    apply HypR, H2.
  Qed.

  Section Bij_ilist_list.
  Variable T: Set.
  Variable comp : T -> T -> Prop.
  Variable compRel: Equivalence comp.

  Add Parametric Morphism (i: ilist T) : (fcti(T:= T) i)
    with signature (eq(A:= Fin (lgti i))) ==> (comp)
  as fctiM.
  Proof.
    reflexivity.
  Qed.

  (* translation from ilist to list *)
  Definition ilist2list (i: ilist T) : list T :=
    map (fcti i) (makeListFin (lgti i)).
  
  Definition eq_comp_morph (n : nat) (f: Fin (n) -> T) := 
    Proper (eq(A:= Fin (n)) ==> comp) f.
  
  Definition fctiiM (i: ilist T): 
    Proper (eq(A:= Fin (lgti i)) ==> comp) (fcti i).
  Proof.
    red. intros f g H. rewrite H.
    reflexivity.
  Qed.

  Definition iM (n: nat)(i: ilistn T n): 
    Proper (eq(A:= Fin n) ==> comp) i.
  Proof.
    red. intros j k H. rewrite H.
    reflexivity.
  Qed.

  (* proof that this translation is correct *)
  Lemma ilist2list_all_elem_ilist_in_list: 
    forall(i: ilist T), iall (fun x => In x (ilist2list i)) i.
  Proof.
    intros i f.
    apply (in_map (fcti i)), all_Fin_n_in_makeListFin.
  Qed.

  Lemma ilist2list_all_elem_list_in_ilist: 
    forall (i: ilist T)(f: Fin(lgti i)), In(fcti i f) (ilist2list i).
  Proof.
    intros i f.
    apply (in_map (fcti i)), all_Fin_n_in_makeListFin.
  Qed.
    
  Lemma ilist2list_nth: 
    forall (t: T)(i: ilist T)(n: nat)(h: n < lgti i),
    fcti i (code_Fin1 h) = nth n (ilist2list i) (fcti i (code_Fin1 h)).
  Proof.
    intros t i n h.
    unfold ilist2list.
    rewrite map_nth, <- nth_makeListFin.
    reflexivity.
  Qed.

  Lemma ilist2list_nth': 
    forall (i: ilist T)(n: nat)(d: T)(h: n < lgti i),
    fcti i (code_Fin1 h) = nth n (ilist2list i) d.
  Proof.
    intros i n d h.
    unfold ilist2list.
    rewrite (nth_indep _ _ (fcti i (code_Fin1 h))).
    rewrite map_nth, <- nth_makeListFin.
    reflexivity.
    rewrite map_length, makeListFin_nb_elem_ok.
    assumption.
  Qed.

  Lemma length_ilist2list: forall (i: ilist T), 
    length (ilist2list i) = lgti i.
  Proof.
    intros i.
    unfold ilist2list.
    rewrite map_length.
    apply (makeListFin_nb_elem_ok).
  Qed.

  Lemma ilist2list_nth2: 
    forall (i: ilist T)(f: Fin (lgti i)),
    fcti i f = nth (decode_Fin f) (ilist2list i) (fcti i f).
  Proof.
    intros i f.
    unfold ilist2list.
    rewrite map_nth, <- (code1_decode_Id f), nth_makeListFin, code1_decode_Id  at 1.
    reflexivity.
  Qed.

  Lemma ilist2list_nth3: 
    forall (t: T)(i: ilist T)(f: Fin (lgti i)),
    fcti i f = nth (decode_Fin f) (ilist2list i) t.
  Proof.
    intros t i f.
    assert (H: decode_Fin f < length (ilist2list i)).
    rewrite length_ilist2list.
    apply decode_Fin_inf_n.
    rewrite (nth_indep (ilist2list i) t (fcti i f) H).
    apply ilist2list_nth2.
  Qed.

  Definition Fin0_T : forall (f: Fin 0), T.
  Proof. 
    intro f ; inversion f.
  Defined.

  Definition list2Fin_T: forall (l: list T)(f: Fin (length l)), T.
  Proof.
    intros [| h l] f.
    inversion f.
    exact (nth (decode_Fin f) (h :: l) h).
  Defined.

  Definition list2ilist (l: list T) : ilist T := mkilist (list2Fin_T l).

  Lemma lgti_length : forall (l: list T), 
    length l = lgti (list2ilist l).
  Proof.
    reflexivity.
  Qed.

  Lemma list2ilist_lgti_cons: forall (a: T) (l: list T), 
     S (lgti (list2ilist l)) = lgti (list2ilist (a :: l)).
  Proof.
    reflexivity.
  Qed.

  (* proof that this translation is correct *)
  Lemma list2ilist_all_elem_ilist_in_list: 
    forall (l: list T),iall (fun x => In x l) (list2ilist l).
  Proof.
    intros l f.
    elim (gt_eq_gt_dec (decode_Fin f) 0) ; [intros [H|e] |intros a] ; try inversion H ;
    destruct l as [| h l].
    inversion f.
    left.
    rewrite (decode_Fin_0_first _ e).
    reflexivity.
    inversion f.
    right.
    inversion a as [e | n H e]; 
    refine (match e in (_ = df) return 
      In match df with 0 => h | S m => nth m l h end l 
      with refl_equal => _ end) ;
    apply (nth_In _ _), lt_S_n ;
    rewrite e ;
    apply decode_Fin_inf_n.
  Qed.

  Definition inf_length_lgti: forall (n: nat)(l: list T)(h: n < length l),
    n < lgti (list2ilist l).
  Proof.
    intros n l h.
    rewrite lgti_length in h.
    assumption.
  Defined.

  Lemma list2ilist_nth: 
    forall (n: nat)(l: list T)(h: n < length l)(t: T),
    comp (nth n l t) (fcti (list2ilist l) (code_Fin1 (inf_length_lgti l h))).
  Proof.
    destruct n as [|n]; intros [| hd l] h t.
    inversion h.
    simpl.
    rewrite code_Fin1_Sn_0.
    reflexivity.
    inversion h.
    simpl in h.
    simpl nth.
    assert (h':= lt_le_S _ _ (lt_S_n _ _ h)).
    assert (H: decode_Fin (code_Fin1_Sn (lt_n_Sm_le _ (length l) (inf_length_lgti (hd :: l) h)))= S n).
    rewrite (code_Fin1_Sn_proofirr _ h').
    revert n h h'.
    induction (length l) as [| ll IHll] ; intros n h h'.
    inversion h'.
    rewrite code_Fin1_Sn_S.
    simpl.
    f_equal.
    set (h1 := le_S_n _ _ h').
    destruct n as [|n].
    rewrite code_Fin1_Sn_0.
    reflexivity.
    apply (IHll _ (lt_S_n _ _ h)).
    simpl.
    rewrite H.
    apply (nth_indep_comp _ l t hd h').
  Qed.
    
  Lemma list2ilist_nth2: 
    forall (l: list T)(f: Fin (lgti (list2ilist l)))(t: T),
    nth (decode_Fin f) l t = fcti (list2ilist l) f.
  Proof.
    intros [|hd l] f t.
    inversion f.
    simpl.
    simpl in f.
    elim (gt_eq_gt_dec (decode_Fin f) 0); [intros [H|e] | intros a].
    inversion H.
    rewrite e; reflexivity.
    inversion a as [e| n H e] ; assert (h:= decode_Fin_inf_n f) ; rewrite <- e in h.
    destruct l as [|hhd l].
    apply False_rec, (lt_irrefl _ h).
    reflexivity.
    apply (nth_indep_comp _ _ _ _ (lt_S_n _ _ h)).
  Qed.

  Lemma lgti_list2ilist: forall (l: list T), 
    lgti (list2ilist l) = length l.
  Proof.
    reflexivity.
  Qed.

  Lemma list2ilist_ilist2list_id : forall (i: ilist T), 
    ilist_rel eq (list2ilist (ilist2list i)) i.
  Proof.
    intros i.
    assert (h : lgti (list2ilist (ilist2list i)) = lgti i).
    rewrite lgti_list2ilist.
    apply length_ilist2list.
    apply (is_ilist_rel _ _ _ h).
    intro f.
    rewrite <- (list2ilist_nth2 _ f (fcti _ f)), (decode_Fin_match' f h), <- (ilist2list_nth3 _).
    reflexivity.
  Qed.

  Lemma list2Fin_T_first: forall (l: list T)(a: T)(x: Fin (length l)),
    list2Fin_T (a :: l) (first (length l)) = a.
  Proof.
    reflexivity.
  Qed.

  Lemma list2Fin_T_succ: forall (l: list T)(a: T)(x: Fin (length l)),
    (list2Fin_T (a :: l) (succ x)) = (list2Fin_T l x).
  Proof.
   simpl.
   induction l as [|hd l]; intros a f.
   inversion f.
   simpl.
   set (d := decode_Fin f) ; assert (h1 := decode_Fin_inf_n f : d < (length (hd :: l))).
   change (match d  with 0 => hd | S m => nth m l a end = match d with 0 => hd | S m => nth m l hd end ).
   revert h1 ; generalize d; clear d ; intros [|d] h1.
   reflexivity.
   apply nth_indep, lt_S_n, h1.
  Qed.

  Lemma list2Fin_T_succ_map: 
    forall (l: list T)(a: T)(lf: list (Fin (length l))), 
     map (fun x : Fin (length l) => list2Fin_T l x) lf = 
       map (fun x : Fin (length l) => list2Fin_T (a :: l) (succ x)) lf.
  Proof.
    intros l a ; induction lf as [| hd lf IH].
    reflexivity.
    change (list2Fin_T l hd :: map (fun x : Fin (length l) => list2Fin_T l x) lf = nth (decode_Fin hd) l a
     :: map (fun x : Fin (length l) => list2Fin_T (a :: l) (succ x)) lf).
    rewrite IH.
    rewrite (list2ilist_nth2 l).
    reflexivity.
  Qed.

  Lemma ilist2list_list2ilist_id: forall (l: list T), ilist2list (list2ilist l) = l.
  Proof.
    induction l as [|hd l].
    reflexivity.
    rewrite <- IHl at 2.
    unfold ilist2list, list2ilist.
    change (hd :: map (list2Fin_T (hd :: l)) (map (fun x => @succ _ x) (makeListFin (length l))) = 
      hd :: map (list2Fin_T l) (makeListFin (length l))).
    rewrite map_map.
    rewrite <- (list2Fin_T_succ_map l hd).
    reflexivity.
  Qed.

  Definition ilistM (n: nat)(i: ilistn T n): 
    Proper (eq(A:= Fin n) ==> comp) i.
  Proof.
    red. intros j k H. rewrite H.
    reflexivity.
  Qed.

  Definition ifilterB (P: T -> bool)(i: ilist T) := 
    list2ilist (filter P (ilist2list i)).

  End Bij_ilist_list.

  Lemma list2Fin_T_map : forall (T U: Set)(l: list T)(f: T -> U)(i: Fin (length (map f l)))
    (h: length (map f l) = length l), 
    list2Fin_T (map f l) i = f (list2Fin_T l (rewriteFins h i)).
  Proof.
    intros T U l f i h.
    destruct l as [|t l].
    inversion i.
    simpl.
    rewrite <- decode_Fin_match'.
    elim (zerop (decode_Fin i)) ; intros a.
    rewrite (decode_Fin_0_first _ a).
    reflexivity.
    inversion a ;
    apply map_nth.
  Qed.

  Lemma list2Fin_T_map_bis : forall (T U: Set)(l: list T)(f: T -> U)(i: Fin (length (map f l))),
    list2Fin_T (map f l) i = f (list2Fin_T l (rewriteFins (map_length f l) i)).
  Proof.
    intros T U l f i.
    destruct l as [|t l].
    inversion i.
    simpl in *|-*.
    rewrite <- decode_Fin_match'.
    set (n := decode_Fin i) ; 
    change (match n with | 0 => f t | S m => nth m (map f l) (f t) end = f match n with
      | 0 => t | S m => nth m l t end).
    destruct n as [|n].
    reflexivity.
    apply map_nth.
  Qed.

  Lemma list2Fin_T_makeListFin: forall (T: Set)(l: ilist T)(i: Fin (length (makeListFin (lgti l))))
    (h:  length (makeListFin (lgti l)) = lgti l), 
    list2Fin_T (makeListFin (lgti l)) i = rewriteFins h i.
  Proof.
    intros T [[|n] l] i h ; simpl in *|-* ; clear l ; 
    apply decode_Fin_unique ; unfold rewriteFins ; rewrite <- decode_Fin_match.
    inversion i.
    set (d := decode_Fin i) ; assert (h1 := decode_Fin_inf_n i : d< _) ; assert (h2:= refl_equal _: d = decode_Fin i).
    revert h1 h2 ; generalize d ; clear d ; intros [|d] h1 h2.
    reflexivity.
    assert (h3 : decode_Fin i > 0).
    rewrite <- h2.
    apply lt_0_Sn.
    assert (i' := get_cons i h3).
    rewrite map_length, makeListFin_nb_elem_ok in i'.
    apply lt_S_n in h1.
    rewrite (nth_indep _ (first n) (succ i') h1) , map_nth.
    rewrite map_length, makeListFin_nb_elem_ok in h1.
    rewrite <- (nth_makeListFin_def h1).
    change (S (decode_Fin (code_Fin1 h1)) = S d).
    f_equal.
    apply decode_code1_Id.
  Qed.

  Lemma list2Fin_T_makeListFin_bis: forall (T: Set)(l: ilist T)(i: Fin (length (makeListFin (lgti l)))), 
    list2Fin_T (makeListFin (lgti l)) i = rewriteFins (makeListFin_nb_elem_ok (lgti l)) i.
  Proof.
    intros T l i.
    destruct l as [n l] ; simpl in *|-* ; clear l.
    destruct n as [|n].
    inversion i.

    elim (zerop (decode_Fin i)) ; intros a.
    rewrite (decode_Fin_0_first _ a).
    simpl.
    apply decode_Fin_unique.
    unfold rewriteFins ; rewrite <- decode_Fin_match.
    reflexivity.

    simpl in *|-*.
    inversion a as [H|m _ H] ;
    [destruct n as [|n] | clear a ; revert m H;  induction n as [|n IH]; intros m H] ; 
    try (rewrite (Fin_first_1 i) in H ; inversion H) ; 
    apply decode_Fin_unique ; 
    unfold rewriteFins ; rewrite <- decode_Fin_match.
    assumption.
    
    destruct m as [|m].
    assumption.
    
    simpl.
    
    rewrite (nth_indep _ (first (S n)) (succ (first n))).
    rewrite map_nth.
    assert (H3 : decode_Fin i >= S (S m)).
    rewrite H.
    apply le_refl.
    simpl.
    simpl in i.
    set (i' := get_cons i  (lt_le_trans _ _ _ (lt_0_Sn (S m)) H3) : 
      Fin (S (length (List.map (@succ (S n)) (List.map (@succ n) (makeListFin n)))))).
    assert (H4 := decode_Fin_unique i (succ i') (decode_Fin_get_cons _ _)).
    set (i'' := rewriteFins (eq_S _ _ 
      (map_length (@succ (S n)) (List.map (@succ n) (makeListFin n)))) i').
    assert (H5 : decode_Fin i'' = decode_Fin i').
    unfold i'', rewriteFins ; apply (sym_eq (decode_Fin_match _ _ )).
    
    rewrite (IH i'').
    unfold rewriteFins ; rewrite <- decode_Fin_match.
    rewrite H5, H4.
    reflexivity.

    rewrite H5.
    apply eq_add_S.
    change (S (S m) = decode_Fin (succ i')).
    rewrite <- H4.
    assumption.
    
    do 2 apply lt_S_n ; rewrite H.
    apply decode_Fin_inf_n.
  Qed.

  Lemma list2ilist_app_lgti (T: Set)(t: T)(l1 l2 : list T) :
    S (lgti (list2ilist (l1 ++ l2))) = lgti (list2ilist (l1 ++ t :: l2)).
  Proof.
    simpl.
    do 2 rewrite app_length.
    apply plus_n_Sm.
  Qed.

  Lemma list2ilist_ilist2list_id_bis(T: Set) : forall (i: ilist T), 
    ilist_rel eq  i (list2ilist (ilist2list i)).
  Proof.
    intros i.
    assert (h : lgti i = lgti (list2ilist (ilist2list i))).
    rewrite lgti_list2ilist.
    apply sym_eq, length_ilist2list.
    apply (is_ilist_rel _ _ _ h).
    intro f.
    simpl.
    unfold ilist2list.
    rewrite list2Fin_T_map_bis, list2Fin_T_makeListFin_bis.
    f_equal.
    apply decode_Fin_unique.
    repeat rewrite <- decode_Fin_match'.
    reflexivity.
  Qed.
	
  Section iappend.
    Definition rightFin (n1 n2 : nat)(i: Fin (n1 + n2))(h: n1 <= decode_Fin i) : Fin n2.
    Proof.
      assert (h1 : decode_Fin i - n1 < n2).
      apply (plus_lt_reg_l _ _ n1).
      rewrite <- le_plus_minus ; try assumption.
      apply decode_Fin_inf_n.
      exact (code_Fin1 h1).
    Defined.
    
    Lemma rightFin_decode_Fin : forall (n1 n2 :nat)(i: Fin (n1 + n2))(h: n1 <= decode_Fin i), 
      decode_Fin (rightFin _ _ h) + n1 = decode_Fin i.
    Proof.
      intros n1 n2 i h.
      unfold rightFin.
      rewrite decode_code1_Id.
      rewrite plus_comm.
      apply sym_eq, le_plus_minus,h.
    Qed.

    Definition iappend (X: Set)(l1 l2 : ilist X) : ilist X.
    Proof.
      destruct l1 as [n1 l1] ; destruct l2 as [n2 l2].
      apply (existT (ilistn X) (n1 + n2)).
      intro i.
      elim (le_lt_dec n1 (decode_Fin i)); intros a.
      exact (l2 (rightFin _ _ a)).
      exact (l1 (code_Fin1 a)).
    Defined.
    
    Lemma iappend_lgti (X: Set)(l1 l2 : ilist X) : lgti (iappend l1 l2) = lgti l1 + lgti l2.
    Proof.
      destruct l1 as [n1 l1] ; destruct l2 as [n2 l2].
      reflexivity.
    Qed.
    
    Lemma iappend_left (X: Set)(l1 l2 : ilist X)(i: Fin (lgti (iappend l1 l2)))
      (h: decode_Fin i < lgti l1) :  fcti (iappend l1 l2) i = fcti l1 (code_Fin1 h).
    Proof.
      destruct l1 as [n1 l1].
      destruct l2 as [n2 l2].
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec n1 (decode_Fin i)) ; intros a.
      apply False_rec, (lt_irrefl n1), (le_lt_trans _ (decode_Fin i)) ; assumption.
      f_equal.
      apply decode_Fin_unique.
      do 2 rewrite decode_code1_Id.
      reflexivity.
    Qed.

    Lemma iappend_right (X: Set)(l1 l2 : ilist X)(i: Fin (lgti(iappend l1 l2)))
      (h: lgti l1 <= decode_Fin (rewriteFins (iappend_lgti _ _) i)) :  
      fcti (iappend l1 l2) i = fcti l2 (rightFin _ (rewriteFins (iappend_lgti _ _) i) h).
    Proof.
      destruct l1 as [n1 l1].
      destruct l2 as [n2 l2].
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec n1 (decode_Fin i)) ; intros a.
      f_equal.
      apply decode_Fin_unique.
      unfold rightFin ; do 2 rewrite decode_code1_Id.
      rewrite <- decode_Fin_match'.
      reflexivity.
      
      apply False_rec, (lt_irrefl n1), (le_lt_trans _ (decode_Fin i)).
      rewrite <- decode_Fin_match' in h.
      assumption.
      assumption.
    Qed.


    Lemma iappend_append (X: Set)(l1 l2 : ilist X) : 
      ilist_rel eq (iappend l1 l2) (list2ilist ((ilist2list l1) ++ (ilist2list l2))).
    Proof.
      assert (h1 : lgti (iappend l1 l2) = lgti (list2ilist (ilist2list l1 ++ ilist2list l2))).
      rewrite lgti_list2ilist, app_length, length_ilist2list, length_ilist2list.
      apply iappend_lgti.
      apply (is_ilist_rel _ _ _ h1).
      
      intros i.
      rewrite <- (list2ilist_nth2 _ _ (fcti (iappend l1 l2) i)), <- decode_Fin_match'.
      elim (le_lt_dec (lgti l1) (decode_Fin i)) ; intros a.
      assert (b := a).
      rewrite (decode_Fin_match' i (iappend_lgti l1 l2)) in b.
      rewrite app_nth2 ; rewrite length_ilist2list ; try assumption.
      rewrite (iappend_right _ _ _ b).
      unfold rightFin, eq_ind, eq_rect.
      set (h2 := plus_lt_reg_l _ _ _ (match le_plus_minus (lgti l1)
      (decode_Fin (rewriteFins (iappend_lgti l1 l2) i)) b in _=y return y < lgti l1 + lgti l2 with 
      eq_refl => decode_Fin_inf_n (rewriteFins (iappend_lgti l1 l2) i) end)).
      rewrite (decode_Fin_match' i (iappend_lgti l1 l2)).
      apply ilist2list_nth'.
      
      rewrite (iappend_left _ _ _ a).
      rewrite app_nth1.
      apply ilist2list_nth'.
      rewrite length_ilist2list ; assumption.
    Qed.
    
    Lemma append_iappend (T: Set)(l1 l2 : ilist T) : 
      ilist2list (iappend l1 l2) = (ilist2list l1) ++ (ilist2list l2).
    Proof.
      apply eq_nth_cor'.
      rewrite app_length.
      do 3 rewrite length_ilist2list.
      apply iappend_lgti.
      intros n d h1.
      rewrite length_ilist2list in h1.
      
      rewrite <- (ilist2list_nth' _ _ h1).
      elim (le_lt_dec (lgti l1) n) ; intros b.
      rewrite app_nth2; rewrite length_ilist2list; try assumption.
      
      assert (h2 : n- lgti l1 < lgti l2).
      rewrite <- (minus_plus (lgti l1) (lgti l2)).
      rewrite <- iappend_lgti.
      apply le_S_gt.
      rewrite minus_Sn_m ; try assumption.
      apply minus_le_compat_r.
      apply gt_le_S.
      assumption.
      rewrite <- (ilist2list_nth' _ _ h2).
      
      assert (h3 : lgti l1 ≤ decode_Fin (rewriteFins (iappend_lgti l1 l2) (code_Fin1 h1))).
      rewrite <- decode_Fin_match', decode_code1_Id.
      assumption.
      rewrite (iappend_right _ _ _ h3).
      f_equal.
      apply decode_Fin_unique.
      unfold rightFin ; do 2 rewrite decode_code1_Id.
      rewrite <- decode_Fin_match'.
      rewrite decode_code1_Id.
      reflexivity.
      
      assert (c := b) ; rewrite <- (decode_code1_Id h1) in c.
      rewrite (iappend_left _ _ _ c).
      rewrite app_nth1.
      rewrite <- (ilist2list_nth' _ _ b).
      f_equal.
      apply decode_Fin_unique.
      do 3 rewrite decode_code1_Id.
      reflexivity.
      
      rewrite length_ilist2list; try assumption.
    Qed.
      
    Lemma iappend_ilist_rel (X: Set)(RelX : relation X)(ls ls' rs rs': ilist X): 
      ilist_rel RelX ls ls' -> ilist_rel RelX rs rs' -> 
      ilist_rel RelX (iappend ls rs) (iappend ls' rs').
    Proof.
      intros [h1 H1] [h2 H2].
      assert (h3 : lgti (iappend ls rs) = lgti (iappend ls' rs')).
      do 2 rewrite iappend_lgti.
      rewrite h1, h2.
      reflexivity.
      apply (is_ilist_rel _ _ _ h3).
      intro i.
      elim (le_lt_dec (lgti ls) (decode_Fin i)) ; intros a ; assert (b := a); 
      rewrite (decode_Fin_match' i h3), h1 in b.
      rewrite (decode_Fin_match' i (iappend_lgti ls rs)) in a.
      rewrite (iappend_right _ _ _ a).
      rewrite (decode_Fin_match' _ (iappend_lgti ls' rs')) in b. 
      rewrite (iappend_right _ _ _ b).
      assert (H3 : rightFin (lgti rs') (rewriteFins (iappend_lgti ls' rs') (rewriteFins h3 i)) b = 
        rewriteFins h2 (rightFin (lgti rs) (rewriteFins (iappend_lgti ls rs) i) a)).
      apply decode_Fin_unique.
      rewrite <- decode_Fin_match'.
      apply (plus_reg_l _ _ (lgti ls')).
      rewrite plus_comm, rightFin_decode_Fin, <- decode_Fin_match', <- decode_Fin_match'.
      rewrite <- h1.
      rewrite plus_comm, rightFin_decode_Fin, <- decode_Fin_match'.
      reflexivity.
      rewrite H3.
      apply H2.
      
      rewrite (iappend_left _ _ _ a).
      rewrite (iappend_left _ _ _ b).
      assert (H3 : code_Fin1 b = rewriteFins h1 (code_Fin1 a)) by treatFinPure.
      rewrite H3.
      apply H1.
    Qed.

  End iappend.


  Section ilist_rel_ListEq.

  (* equivalence between ilist_rel and ListEq *)
  Lemma ilist_rel_ListEq_eq: 
    forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)(i1 i2: ilist T), 
    ilist_rel eqT i1 i2 <-> ListEq eqT (ilist2list i1) (ilist2list i2).
  Proof.
    intros T eqT eqTRel i1 i2 ; split ; intros H ;
    destruct i1 as [n i1]; destruct i2 as [n2 i2].
    inversion H as [e h] ; simpl in e, h.
    assert (e' := e) ; revert i2 e H h ; rewrite <- e' ; intros i2 e H h ; clear e' n2.
    assert (h' : forall f, eqT (i1 f) (i2 f)).
    intro f. 
    rewrite (decode_Fin_unique _ _ (decode_Fin_match f e) : f = rewriteFins e f) at 2 ; apply h.
    apply ListEq_map_f_g, h'.

    unfold ilist2list in H.
    simpl in H.
    assert (H1 := ListEq_length H).
    do 2 (rewrite map_length, makeListFin_nb_elem_ok in H1).
    revert i2 H ; rewrite <- H1 ; intros i2 H ; clear H1 n2.
    apply (is_ilist_rel _ _ _ (refl_equal n : lgti (existT _ _ i1) = lgti (existT _ _ i2))) ; simpl.
    intro f.
    apply (ListEq_eq eqTRel _ _ _ H _ (all_Fin_n_in_makeListFin f)).
  Qed.

  Lemma ListEq_ilist_rel_eq: 
    forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)(l1 l2: list T), 
    ilist_rel eqT (list2ilist l1) (list2ilist l2) <-> ListEq eqT l1 l2.
  Proof.
    intros T eqT eqTR l1 l2.
    rewrite <- (ilist2list_list2ilist_id l1), <- (ilist2list_list2ilist_id l2) at 2.
    apply (ilist_rel_ListEq_eq eqTR).
  Qed.

  Lemma map_ext_in (T U : Set)(f1 f2 : T -> U)(l: list T) :
    map f1 l = map f2 l -> forall t, In t l -> f1 t = f2 t.
  Proof.
    intros H1 t H2.
    induction l as [|tt l IH].
    inversion H2.
    inversion H1.
    destruct H2 as [H2|H2].
    rewrite <- H2.
    assumption.
    apply IH ; assumption.
  Qed.

  Lemma ilist_rel_eq: 
    forall (T: Set)(i1 i2: ilist T), ilist_rel eq i1 i2 <-> ilist2list i1 = ilist2list i2.
  Proof.
    intros T i1 i2 ; split ; intros H ;
    destruct i1 as [n i1]; destruct i2 as [n2 i2].
    inversion H as [e h] ; simpl in e, h.
    assert (e' := e) ; revert i2 e H h ; rewrite <- e' ; intros i2 e H h ; clear e' n2.
    unfold ilist2list.
    simpl.
    apply map_ext.
    intro f. 
    rewrite (decode_Fin_unique _ _ (decode_Fin_match f e) : f = rewriteFins e f) at 2 ; apply h.

    unfold ilist2list in H.
    simpl in H.
    fold (mkilist i1) (mkilist i2).
    assert (H1 : n = n2).
    rewrite <- (makeListFin_nb_elem_ok n), <- (makeListFin_nb_elem_ok n2).
    rewrite <- (map_length i1 (makeListFin n) : length (map _ _) = _), <- (map_length i2 (makeListFin n2)).
    rewrite H.
    reflexivity.
    revert i2 H ; rewrite <- H1 ; intros i2 H ; clear H1 n2.
    apply (is_ilist_rel _ _ _ (refl_equal n : lgti (mkilist i1) = lgti (mkilist i2))) ; simpl.
    intro f.
    apply (map_ext_in _ _ _ H).
    apply all_Fin_n_in_makeListFin.
  Qed.


  End ilist_rel_ListEq.

  Add Parametric Morphism (T: Set)(eqT: relation T)
    (eqTR: Equivalence eqT): (ilist2list(T:= T))
    with signature (ilist_rel eqT) ==> (ListEq eqT)
  as ilist2listM.
  Proof.
    intros x y h.
    apply (ilist_rel_ListEq_eq eqTR x y).
    assumption.
  Qed.

  Add Parametric Morphism (T: Set)(eqT: relation T)
    (eqTR: Equivalence eqT): (list2ilist(T:= T))
    with signature (ListEq eqT) ==> (ilist_rel eqT)
  as list2ilistM.
  Proof.
    intros x y h.
    apply (ListEq_ilist_rel_eq eqTR x y).
    assumption.
  Qed.

  Lemma map_imap_ilist_list: forall (T U: Set)(i: ilist T)(f: T -> U)
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Proper (compT ==> compU) f), 
    ilist_rel compU (imap f i) (list2ilist (map f (ilist2list i))).
  Proof.
    intros T U i f compT compTRel compU compURel fM.
    assert (H: lgti (imap f i) = lgti (list2ilist (map f (ilist2list i)))).
    simpl.
    rewrite map_length.
    apply (sym_eq (length_ilist2list i)).
    apply (is_ilist_rel _ _ _ H); intro fi.
    destruct i as [ [|n] i].
    inversion fi.
    simpl.
    rewrite <- (code1_decode_Id fi) at 1.
    elim (zerop (decode_Fin (rewriteFins H fi))); intros a.
    refine (match (sym_eq a) in (_ = df) return 
    compU _ match df with 0 => f (i (first n)) | S m => _ end
    with refl_equal => _ end).
    rewrite <- (decode_Fin_match' _ H) in a.
    rewrite code1_decode_Id, (decode_Fin_0_first _ a).
    reflexivity.

    inversion a as [e | m H1 e];
    rewrite <- (decode_Fin_match' _ H) in e ; rewrite code1_decode_Id.
    destruct n as [|n].
    rewrite (Fin_first_1 fi) in e.
    inversion e.
    rewrite (refl_equal _: 1 = decode_Fin (succ (first n))) in e.
    apply decode_Fin_unique in e.
    simpl ; rewrite e; reflexivity.

    assert (H2 :m < n).
    apply (lt_S_n m n).
    rewrite e.
    apply decode_Fin_inf_n.
    rewrite (map_map_nth_comp compTRel compURel i fM).
    destruct n as [|n].
    inversion H2.
    rewrite (nth_indep _ (first (S n)) (succ (first n))), map_nth, <- (nth_makeListFin_def H2).
    rewrite (decode_Fin_unique _ _ (trans_eq  (eq_S _ _ (decode_code1_Id H2) : decode_Fin (succ _) = _) e)).
    reflexivity.

    rewrite map_length, makeListFin_nb_elem_ok.
    assumption.
  Qed.

  Lemma list2Fin_T_succ_map_f: 
    forall (T U: Set) (l: list T)(a: T)(lf: list (Fin (length l)))(f: T -> U)
    (compT: relation T)(compU: relation U)(compURel: Equivalence compU)
    (fM: Proper (compT ==> compU) f), 
     ListEq compU (map (fun x : Fin (length l) => f( list2Fin_T l x)) lf)
       (map (fun x : Fin (length l) => f(list2Fin_T (a :: l) (succ x))) lf).
  Proof.
    intros T U l a lf f compT compU compURel fM.
    induction lf as [| hd lf IHlf].
    apply ListEq_nil.
    apply ListEq_cons.
    rewrite list2Fin_T_succ.
    reflexivity.
    apply IHlf.
  Qed.

  Lemma imap_cons: forall (T U: Set)(a: T)(l: list T)(f: T -> U)
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Proper (compT ==> compU) f), 
    ListEq compU (ilist2list (imap f (list2ilist (a :: l)))) 
      (f a :: (ilist2list (imap f (list2ilist l)))).
  Proof.
    intros T U a l f compT compTRel compU compURel fM .
    rewrite (map_imap_ilist_list _ _ _ fM), ilist2list_list2ilist_id.
    simpl.
    apply ListEq_cons.
    reflexivity.
    do 2 (rewrite (map_map_ListEq compURel)).
    unfold ilist2list, list2ilist.
    simpl.
    rewrite (list2Fin_T_succ_map_f l a _ compURel fM).
    reflexivity.
  Qed.

  Lemma imap_map_list_ilist: forall (T U: Set)(l: list T)(f: T -> U)
    (compT: relation T)(compTRel: Equivalence compT)
    (compU: relation U)(compURel: Equivalence compU)
    (fM: Proper (compT ==> compU) f), 
    ListEq compU (map f l) (ilist2list (imap f (list2ilist l))).
  Proof.
    intros T U l f compT compTRel compU compURel fM.
    induction l as [|hd l IHl].
    reflexivity.
    rewrite (imap_cons _ _ _ _ _).
    apply ListEq_cons.
    reflexivity.
    assumption.
  Qed.

   Definition ifold_left (A B : Set) (f : A → B → A) 
     (l : ilist B) (a0 : A) : A :=
     fold_left f (ilist2list l) a0.

Section manip_ilist.

  (* various definitions and functions for ilist manipulation  *)
  Definition singleton(T: Set) (t: T): ilist T := 
    mkilist(n:=1) (fun i => t).
  
  Lemma singleton_lgti: forall (T: Set)(t: T), 
    lgti (singleton t) = 1.
  Proof.
    reflexivity.
  Qed.
  
  Lemma singleton_ok: forall (T: Set)(t: T)
    (eqT: relation T)(eqTR: Equivalence eqT)(f: Fin (lgti (singleton t))), 
      eqT (fcti (singleton t) f) t.
  Proof.
    reflexivity.
  Qed.

  Definition iniln: forall (T: Set), ilistn T 0.
  Proof.
    intros T f.
    inversion f.
  Defined.

  Definition inil(T: Set): ilist T := mkilist(n:=0) (iniln T).

  Definition iconsn : forall (T: Set)(n: nat)(t: T)(i: ilistn T n), ilistn T (S n).
  Proof.
    intros T n t i f.
    inversion f as [k h |k f' h].
    exact t.
    exact (i f').
  Defined.

  Definition icons (T: Set)(t: T)(i: ilist T): ilist T := 
    mkilist (fun f => iconsn t (fcti i) f).

  Lemma singleton_eq_icons_inil: forall (T: Set)(eqT: relation T)
    (eqTR: Equivalence eqT)(t: T), 
    ilist_rel eqT (singleton t) (icons t (inil T)).
  Proof.
    intros T eqT eqTR t.
    apply (is_ilist_rel _ _ _ (refl_equal _ :  lgti (singleton t) = lgti (icons t (inil T)))).
    intro f.
    rewrite (Fin_first_1 f).
    reflexivity.
  Qed.
  
  Lemma icons_ok: forall (T: Set)(t: T)(i: ilist T)(f: Fin (lgti i)),
    fcti i f = fcti (icons t i) (succ f).
  Proof.
    reflexivity.
  Qed.

  Lemma icons_first: forall (T: Set)(eqT: relation T)(eqTR: Equivalence eqT)
    (t: T)(i: ilist T),
    eqT t (fcti (icons t i) (first (lgti i))).
  Proof.
    reflexivity.
  Qed.

  Definition iheadOp: forall (T: Set)(i: ilist T), option T.
  Proof.
    intros T [[|n] i].
    exact None.
    exact (Some (i (first n))).
  Defined.

  Definition ihead: forall  (T: Set)(i: ilist T)(d: T), T.
  Proof.
    intros T [[|n] i] t.
    exact t.
    exact (i (first n)).
  Defined.

  Definition itail: forall (T: Set)(i: ilist T), ilist T.
  Proof.
    intros T [[|n] i].
    exact (inil T).
    exact (mkilist (fun f => i (succ f))).
  Defined.

  Lemma lgti_itail: forall (T: Set)(i: ilist T), 
   lgti i = 0 \/ lgti i = S (lgti (itail i)).
  Proof.
    intros T [[|n] i] ; [left |right] ; reflexivity.
  Qed.

  Lemma ihead_itail_ok :
    forall (T: Set)(d: T)(i: ilist T),
    lgti i >= 1 -> ilist_rel eq i (icons (ihead i d) (itail i)).
  Proof.
    intros T d [[|n] l] h.
    inversion h.
    fold (mkilist l) in *|-*.
    simpl.
    clear h.
    assert (e := refl_equal _ : lgti (mkilist l) = 
      lgti (icons (l (first n)) (mkilist (fun f : Fin n => l (succ f))))).
    apply (is_ilist_rel _ _ _ e).
    simpl.
    intro i.
    set (i' := rewriteFins e i) ; change (l i = iconsn (l (first n)) (fun f : Fin n => l (succ f)) i').
    assert ( h1 : i' = i). unfold i' ; treatFinPure.
    rewrite h1 ; clear h1.
    elim (zerop (decode_Fin i)); intro a.
    rewrite (decode_Fin_0_first _ a).
    reflexivity.
    assert (H1 : succ (get_cons i a) = i) by treatFinPure.
    rewrite <- H1.
    reflexivity.
  Qed.

  Lemma itail_lgti_eq : forall (T: Set)(i1 i2: ilist T), 
    lgti i1 = lgti i2 -> lgti (itail i1) = lgti (itail i2).
  Proof.
    intros T [n1 i1] [n2 i2] e.
    destruct n1 as [|n1] ; destruct n2 as [|n2] ; try inversion e.
    reflexivity.
    assumption.
  Qed.
    
  Lemma itail_ilist_rel : forall (T: Set)(RelT : relation T)(i1 i2: ilist T), 
    ilist_rel RelT i1 i2 -> ilist_rel RelT (itail i1) (itail i2).
  Proof.
    intros T RelT i1 i2 [e H].
    apply (is_ilist_rel _ _ _ (itail_lgti_eq _ _ e)).
    intro f.
    destruct i1 as [[|n1] i1].
    inversion f.
    destruct i2 as [[|n2] i2].
    inversion e.
    simpl in e, H, f.
    simpl.
    assert (h: succ (rewriteFins (itail_lgti_eq (mkilist i1)
      (mkilist i2) e) f) = (rewriteFins e (succ f))).
    treatFinPure.
    assert (H':= H (succ f)).
    rewrite <- h in H'.
    assumption.
  Qed.

  Lemma imap_ilist_rel(T U: Set)(RelT: relation T)(RelU : relation U)(RelUEq: Equivalence RelU)(f: T -> U)
    (fM: Proper (RelT ==> RelU) f): 
    forall l1 l2 , ilist_rel RelT l1 l2 -> ilist_rel RelU (imap f l1) (imap f l2).
  Proof.
    intros l1 l2 [h H].
    assert (h' := h).
    rewrite <- (imap_lgti l1 f), <- (imap_lgti l2 f) in h'.
    apply (is_ilist_rel _ _ _ h').
    simpl.
    intro i.
    rewrite (H i).
    assert (Hi: rewriteFins h i = rewriteFins h' i).
    apply decode_Fin_unique ; unfold rewriteFins ; do 2 rewrite <- decode_Fin_match ; reflexivity.
    rewrite Hi.
    reflexivity.
  Qed.

   Lemma imap_icons (T U: Set)(RelU: relation U)(EqU: Equivalence RelU)(f: T -> U)(l: ilist T)(t: T): 
       ilist_rel eq (imap f (icons t l))(icons (f t) (imap f l)).
   Proof.
     assert (h:= refl_equal _: lgti (imap f (icons t l))  = lgti (icons (f t) (imap f l))).
     apply (is_ilist_rel _ _ _ h).
     simpl.
     intro i.
     destruct l as [n l].
     simpl in *|-*.
     assert (h1 : rewriteFins h i = i) by treatFinPure.
     rewrite h1 ; clear h h1.
     elim (zerop (decode_Fin i)) ; intros a.
     rewrite (decode_Fin_0_first _ a).
     reflexivity.
     assert (h1 : i = succ (get_cons i a)) by treatFinPure.
     rewrite h1 ; clear h1.
     reflexivity.
   Qed.

  Lemma inil_nil (T: Set)(RelT : relation T) : ilist_rel eq (inil T) (list2ilist nil).
  Proof.
    apply (is_ilist_rel _ _ _ (refl_equal _)).
    intro i.
    inversion i.
  Qed.

  Lemma nil_inil (T: Set)(RelT : relation T) : ilist2list (inil T) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma icons_cons (T: Set)(t: T)(l: ilist T) : ilist_rel eq (icons t l) (list2ilist (t :: (ilist2list l))).
  Proof.
    assert (h : lgti (icons t l) = lgti (list2ilist (t :: ilist2list l))).
    simpl.
    rewrite length_ilist2list.
    reflexivity.
    apply (is_ilist_rel _ _ _ h).
    simpl.
    intro i.
    rewrite <- decode_Fin_match'.
    elim (zerop (decode_Fin i)) ; intro a.
    rewrite a, (decode_Fin_0_first _ a).
    reflexivity.
    rewrite (decode_Fin_unique _ _ (decode_Fin_get_cons _ a : _ = decode_Fin (succ _))).
    simpl.
    rewrite (nth_indep _ _ (fcti l (get_cons i a))).
    apply ilist2list_nth2.
    rewrite length_ilist2list.
    apply decode_Fin_inf_n.
  Qed.
    
  Lemma cons_icons (T: Set)(t: T)(l: list T) : 
    ilist2list (icons t (list2ilist l)) = t :: l.
  Proof.
    unfold ilist2list.
    simpl.
    f_equal.
    rewrite map_map.
    simpl.
    clear t.
    destruct l as [|t l].
    reflexivity.
    simpl.
    f_equal.
    rewrite map_map.
    simpl.
    induction l as [|t' l IH].
    reflexivity.
    simpl.
    f_equal.
    rewrite map_map.
    simpl.
    apply IH.
  Qed.

    
  Lemma cons_icons' (T: Set)(t: T)(l: ilist T) : 
    ilist2list (icons t l) = t :: (ilist2list l).
  Proof.
    unfold ilist2list.
    simpl.
    rewrite map_map.
    reflexivity.
  Qed.

  Lemma iappend_icons_ilist_rel_cor (X: Set)(RelX : relation X)(ls ls' rs rs': ilist X)(x x': X): 
    ilist_rel RelX ls ls' -> ilist_rel RelX rs rs' -> RelX x x' -> 
    ilist_rel (RelX) (iappend ls (icons x rs)) (iappend ls' (icons x' rs')).
  Proof.
    intros H1 [h H2] H3.
    apply iappend_ilist_rel.
    apply H1.
    assert (h' : lgti (icons x rs) = lgti (icons x' rs')).
    simpl.
    f_equal; assumption.
    apply (is_ilist_rel _ _ _ h').
    intro i.
    elim (zerop (decode_Fin i)) ; intros a.
    rewrite (decode_Fin_0_first _ a).
    assert (H4 : rewriteFins h' (first (lgti rs)) = first (lgti rs')) by treatFinPure.
    rewrite H4.
    assumption.
    rewrite <- (get_cons_ok1 _ a).
    assert (H4 : rewriteFins h' (succ (get_cons i a)) = succ (rewriteFins h (get_cons i a))).
    apply decode_Fin_unique.
    simpl.
    do 2 rewrite <- decode_Fin_match'.
    reflexivity.
    rewrite H4.
    apply H2.
  Qed.
  
End manip_ilist.

Lemma imap_apply: forall (T U: Set)(i: ilist U)(m: U -> T)(f: Fin (lgti i)), 
  fcti (imap m i) f = m (fcti i f).
Proof.
  reflexivity.
Qed.

  Section left_and_right_siblings.
  
    Definition left_sib (X: Set)(l: ilist X)(i: Fin (lgti l)) : ilist X.
    Proof.
      apply (@mkilist X (decode_Fin i)).
      intro i'.
      exact (fcti l (code_Fin1 (lt_trans _ _ _ (decode_Fin_inf_n i') (decode_Fin_inf_n i)))).
    Defined.
    
    Lemma left_sib_lgti (X: Set)(l: ilist X)(i: Fin (lgti l)) : lgti (left_sib l i) = decode_Fin i.
    Proof.
      reflexivity.
    Qed.
    
    Definition right_sib (X: Set)(l: ilist X)(i: Fin (lgti l)) : ilist X.
    Proof.
      apply (@mkilist X (lgti l - (S (decode_Fin i)))).
      intro i'.
      assert (h : S (decode_Fin i) + decode_Fin i' < lgti l).
      rewrite (le_plus_minus _ (lgti l) (gt_le_S _ _ (decode_Fin_inf_n i))).
      apply (plus_gt_compat_l _ _ (S (decode_Fin i))), decode_Fin_inf_n.
      exact (fcti l (code_Fin1 h)).
    Defined.
    
    Lemma right_sib_lgti (X: Set)(l: ilist X)(i: Fin (lgti l)) : 
      lgti (right_sib l i) = lgti l - S (decode_Fin i).
    Proof.
      reflexivity.
    Qed.
    
    Lemma left_sib_right_sib_lgti (X: Set)(l: ilist X)(i: Fin (lgti l)) : 
      S (lgti (left_sib l i) + lgti (right_sib l i)) = lgti l.
    Proof.
      simpl.
      rewrite <- plus_Sn_m.
      apply sym_eq, (le_plus_minus _ _ (gt_le_S _ _ (decode_Fin_inf_n i))).
    Qed.

    Lemma left_sib_right_sib (T: Set)(l: ilist T)(i: Fin (lgti (l))) : 
      ilist2list (left_sib l i) ++ (fcti l i) :: ilist2list (right_sib l i) = ilist2list l.
    Proof.
      apply eq_nth_cor'.
      rewrite app_length.
      simpl.
      repeat rewrite length_ilist2list.
      rewrite <- plus_n_Sm.
      apply left_sib_right_sib_lgti.
      
      intros n d h .
      rewrite app_length in h ; simpl in h ; rewrite <- plus_n_Sm, <- plus_Sn_m in h.
      do 2 rewrite length_ilist2list in h.
      assert (a : n < lgti l).
      rewrite <- (left_sib_right_sib_lgti l i) ; assumption.
      clear h.
      rewrite <- (ilist2list_nth' _ _ a).
      
      elim (le_lt_dec (decode_Fin i) n) ; intros b.
      rewrite app_nth2 ;
      rewrite length_ilist2list, left_sib_lgti ; try assumption.
      simpl.
      set (x := n - decode_Fin i).
      assert (h1 := refl_equal _ : n - decode_Fin i = x).
      destruct x as [|x].
      f_equal.
      apply decode_Fin_unique.
      rewrite decode_code1_Id.
      apply sym_eq, (minus_n_m_0 b h1).
      
      assert (h2 : x < lgti (right_sib l i)).
      apply lt_S_n.
      rewrite <- h1.
      rewrite right_sib_lgti.
      rewrite minus_Sn_m, Sn_Sm_eq_n_m.
      apply le_S_gt.
      rewrite minus_Sn_m; try assumption.
      apply minus_le_compat_r.
      apply gt_le_S, a.
      apply gt_le_S, decode_Fin_inf_n.
      
      rewrite <- (ilist2list_nth' _ _ h2).
      simpl.
      f_equal.
      apply decode_Fin_unique.
      repeat rewrite decode_code1_Id.
      rewrite plus_n_Sm, <-h1.
      apply sym_eq, le_plus_minus ; assumption.
      
      rewrite app_nth1.
      assert (h1 : n < lgti (left_sib l i)).
      rewrite left_sib_lgti; assumption.
      
      rewrite <- (ilist2list_nth' _ _ h1).
      simpl.
      f_equal.
      treatFinPure.
      rewrite length_ilist2list ; assumption.
    Qed.

    Lemma left_sib_right_sib_cor (T: Set)(l: ilist T)(i: Fin (lgti (l))) : 
      ilist_rel eq (iappend (left_sib l i) (icons (fcti l i) (right_sib l i))) l.
    Proof.
      apply ilist_rel_eq.
      rewrite append_iappend.
      rewrite cons_icons'.
      apply left_sib_right_sib.
    Qed.

    Lemma left_sib_right_sib_cor': forall (X: Set)(RelX : relation X)(Rrefl : Reflexive RelX)(l: ilist X)
      (i: Fin (lgti l)),  ilist_rel RelX l (iappend (left_sib l i) (icons (fcti l i) (right_sib l i))).
    Proof.
      intros X RelX Rrefl l i.
      assert (h : lgti l = lgti (iappend (left_sib l i) (icons (fcti l i) (right_sib l i)))).
      rewrite iappend_lgti.
      change (lgti (icons (fcti l i) (right_sib l i))) with (S (lgti (right_sib l i))).
      rewrite <- plus_n_Sm.
      rewrite left_sib_right_sib_lgti.
      reflexivity.
      apply (is_ilist_rel _ _ _ h).
      intro i'.
      elim (le_lt_dec (lgti (left_sib l i)) (decode_Fin i') ) ; intros a.
      rewrite (decode_Fin_match' i' h), (decode_Fin_match' _   (iappend_lgti _ _)) in a.
      rewrite (iappend_right _ _ _ a).
      set (i1 := rightFin (lgti (icons (fcti l i) (right_sib l i))) (rewriteFins
        (iappend_lgti (left_sib l i) (icons (fcti l i) (right_sib l i))) (rewriteFins h i')) a).
      elim (zerop (decode_Fin i1)) ; intros b.
      rewrite (decode_Fin_0_first _ b).
      simpl.
      assert (i = i').
      apply decode_Fin_unique.
      simpl in a.
      assert (H1 := rightFin_decode_Fin _ _ a).
      do 2 rewrite <- decode_Fin_match' in H1.
      rewrite <- H1.
      change (decode_Fin i = decode_Fin i1 + decode_Fin i).
      rewrite b.
      symmetry.
      apply plus_O_n.
      rewrite H.
      apply Rrefl.
      
      rewrite <- (get_cons_ok1 _ b).
      change (RelX (fcti l i') (fcti (right_sib l i) (get_cons i1 b))).
      simpl.
      assert (i' = (code_Fin1 (eq_ind_r (lt _) (plus_gt_compat_l _ _ _ (decode_Fin_inf_n (get_cons _ b)))
           (le_plus_minus _ _ (gt_le_S _ _ (decode_Fin_inf_n i)))))).
      apply decode_Fin_unique.
      rewrite decode_code1_Id.
      rewrite plus_Sn_m, plus_n_Sm.
      rewrite <- decode_Fin_get_cons.
      change (decode_Fin i) with (lgti (left_sib l i)).
      unfold i1.
      rewrite plus_comm.
      rewrite rightFin_decode_Fin.
      do 2 rewrite <- decode_Fin_match'.
      reflexivity.
      rewrite H.
      apply Rrefl.

      rewrite (decode_Fin_match' i' h) in a.
      rewrite (iappend_left _ _ _ a).
      simpl.
      assert (code_Fin1 (lt_trans _ _ _ (decode_Fin_inf_n (code_Fin1 a)) (decode_Fin_inf_n i)) = i').
      apply decode_Fin_unique.
      do 2 rewrite decode_code1_Id.
      apply sym_eq, decode_Fin_match'.
      rewrite <- H at 1.
      apply Rrefl.
    Qed.

    Lemma left_sib_ilist_rel (X: Set)(RelX : relation X)(xs xs': ilist X)(i: Fin (lgti xs))(h: lgti xs = lgti xs'): 
      ilist_rel RelX xs xs' -> ilist_rel RelX (left_sib xs i) (left_sib xs' (rewriteFins h i)).
    Proof.
      intros [h1 H1].
      assert (h2 : lgti (left_sib xs i) = lgti (left_sib xs' (rewriteFins h i))).
      apply decode_Fin_match'.
      apply (is_ilist_rel _ _ _ h2).
      intro i'.
      simpl.
      assert (H2 : code_Fin1 (lt_trans _ _ _ (decode_Fin_inf_n (rewriteFins h2 i')) 
        (decode_Fin_inf_n (rewriteFins h i))) = rewriteFins h1 (code_Fin1
        (lt_trans _ _ _ (decode_Fin_inf_n i') (decode_Fin_inf_n i)))) by treatFinPure.
      simpl in H2.
      rewrite H2.
      apply H1.
    Qed.
    
    Lemma right_sib_ilist_rel (X: Set)(RelX : relation X)(xs xs': ilist X)(i: Fin (lgti xs))(h: lgti xs = lgti xs'): 
      ilist_rel RelX xs xs' -> ilist_rel RelX (right_sib xs i) (right_sib xs' (rewriteFins h i)).
    Proof.
      intros [h1 H1].
      assert (h2 : lgti (right_sib xs i) = lgti (right_sib xs' (rewriteFins h i))).
      simpl.
      rewrite <- decode_Fin_match', <- h1.
      reflexivity.
      apply (is_ilist_rel _ _ _ h2).
      intro i'.
      simpl.
      set (i1 := code_Fin1 (eq_ind_r (lt _) (plus_gt_compat_l _ _ _ (decode_Fin_inf_n i'))
           (le_plus_minus _ _ (gt_le_S _ _ (decode_Fin_inf_n i))))).
      assert (code_Fin1 (eq_ind_r (lt _) (plus_gt_compat_l _ _ _ (decode_Fin_inf_n (rewriteFins h2 i')))
           (le_plus_minus _ _  (gt_le_S _ _  (decode_Fin_inf_n (rewriteFins h i))))) = rewriteFins h1 i1).
      apply decode_Fin_unique.
      unfold i1.
      rewrite decode_code1_Id.
      do 3 rewrite <- decode_Fin_match'.
      rewrite decode_code1_Id.
      apply plus_Sn_m.
      assert (H1' := H1 i1).
      rewrite <- H in H1'.
      assumption.
    Qed.
    
    Lemma left_sib_iappend (X: Set)(l1 l2 : ilist X)(t: X)(n: nat)
      (h: n < lgti (iappend l1 (icons t l2))): n = lgti l1 -> 
      ilist_rel eq l1 (left_sib (iappend l1 (icons t l2)) (code_Fin1 h)).
    Proof.
      intros H1.
      assert (h1 : lgti l1 = lgti (left_sib (iappend l1 (icons t l2)) (code_Fin1 h))).
      simpl.
      rewrite decode_code1_Id.
      symmetry ; assumption.
      apply (is_ilist_rel _ _ _ h1).
      intro i.
      simpl.
      assert (h2 : decode_Fin ((code_Fin1 (lt_trans _ _ _
        (decode_Fin_inf_n (rewriteFins h1 i)) (decode_Fin_inf_n (code_Fin1 h))))) < lgti l1).
      rewrite decode_code1_Id, <- decode_Fin_match'.
      apply decode_Fin_inf_n.
      assert (H3 : i = code_Fin1 h2) by treatFinPure.
      rewrite H3 at 1.
      symmetry.
      apply (iappend_left _ _ _ h2).
    Qed.
    
    Lemma right_sib_iappend (X: Set)(l1 l2 : ilist X)(t: X)(n: nat)
      (h: n < lgti (iappend l1 (icons t l2))): n = lgti l1 -> 
      ilist_rel eq l2 (right_sib (iappend l1 (icons t l2)) (code_Fin1 h)).
    Proof.
      intros H1.
      assert (h1 : lgti l2 = lgti (right_sib (iappend l1 (icons t l2)) (code_Fin1 h))).
      simpl.
      rewrite decode_code1_Id.
      rewrite iappend_lgti.
      simpl.
      rewrite <- plus_n_Sm, <- plus_Sn_m.
      rewrite H1.
      apply sym_eq, minus_plus.
      apply (is_ilist_rel _ _ _ h1).
      intro i.
      simpl.
      assert (h2 : lgti l1 <= decode_Fin (rewriteFins (iappend_lgti l1 _)
        (code_Fin1 (eq_ind_r (lt _) (plus_gt_compat_l _ _ _ (decode_Fin_inf_n (rewriteFins h1 i)))
        (le_plus_minus _ _ (gt_le_S _ _  (decode_Fin_inf_n (code_Fin1 h)))))))).
      do 2 (rewrite <- decode_Fin_match', decode_code1_Id).
      rewrite H1.
      rewrite plus_Sn_m, plus_n_Sm.
      apply le_plus_l.
      assert (H3 := iappend_right _ _ _ h2).
      assert (H4 : rightFin _ (rewriteFins (iappend_lgti l1 (icons t l2))
             (code_Fin1 (eq_ind_r  (lt _) (plus_gt_compat_l _ _ _ (decode_Fin_inf_n (rewriteFins h1 i)))
             (le_plus_minus _ _ (gt_le_S _ _ (decode_Fin_inf_n (code_Fin1 h))))))) h2 = succ i).
      apply decode_Fin_unique.
      apply (plus_reg_l _ _ (lgti l1)).
      rewrite plus_comm.
      rewrite rightFin_decode_Fin, <- decode_Fin_match', decode_code1_Id, decode_code1_Id, <- decode_Fin_match', H1.
      apply plus_n_Sm.
      rewrite H4 in H3.
      clear H4.
      change (fcti (icons t l2) (succ i)) with (fcti l2 i) in H3.
      apply sym_eq, H3.
    Qed.
    
    Lemma middle_iappend (X: Set)(l1 l2 : ilist X)(t: X)(n: nat)
      (h: n < lgti (iappend l1 (icons t l2))): n = lgti l1 -> t = (fcti (iappend l1 (icons t l2)) (code_Fin1 h)).
    Proof.
      intros H.
      assert (h1 : lgti l1 <= decode_Fin (rewriteFins (iappend_lgti l1 (icons t l2)) (code_Fin1 h))).
      rewrite <- decode_Fin_match', decode_code1_Id.
      rewrite H ; apply le_refl.
      rewrite (iappend_right _ _ _ h1).
      assert (H2 : 
        rightFin (lgti (icons t l2)) (rewriteFins (iappend_lgti l1 (icons t l2)) (code_Fin1 h)) h1 = first _).
      apply decode_Fin_unique, (plus_reg_l _ _ (lgti l1)).
      rewrite plus_comm.
      rewrite rightFin_decode_Fin, <- decode_Fin_match', decode_code1_Id, H.
      apply plus_n_O.
      rewrite H2.
      reflexivity.
    Qed.

  End left_and_right_siblings.
  
  Section ilflatten.
  
    Definition ilflatten (X: Set)(l: ilist (list X)): list X.
    Proof.
      destruct l as [n l].
      induction n as [|n IH].
      exact nil.
      exact (l (first n) ++ (IH (fun i => l (succ i)))).
    Defined.
    
    Lemma ilflatten_mkilist (X: Set)(n: nat)(l: ilistn (list X) n)(i: Fin n): incl (l i) (ilflatten (mkilist l)).
    Proof.
      induction n as [|n IH].
      inversion i.
      elim (zerop (decode_Fin i)) ; intros a.
      rewrite (decode_Fin_0_first _ a).
      apply incl_appl.
      apply incl_refl.
      rewrite <- (get_cons_ok1 _ a).
      apply incl_appr.
      change (incl ((fun x => l (succ x)) (get_cons i a)) (ilflatten (mkilist (fun x => l (succ x))))).
      apply IH.
    Qed.
    
    Lemma ilflatten_ilist_rel(X: Set)(l l': ilist (list X)): ilist_rel eq l l' -> ilflatten l = ilflatten l'.
    Proof.
      intros [h H].
      destruct l as [n l] ; destruct l' as [n' l'].
      simpl in h.
      revert l' H ; rewrite <- h ; clear n' h  ; intros l' H.
      simpl in H.
      induction n as [|n IH].
      reflexivity.
      simpl.
      rewrite H.
      f_equal.
      apply IH.
      intro i ; apply H.
    Qed.
  End ilflatten.
   
  Section ilist_rel_dec.

    Lemma ilist_rel_nil (T: Set)(l1 l2 : ilistn T 0) : 
      ilist_rel eq (mkilist l1) (mkilist l2).
    Proof.
      apply (is_ilist_rel  _ _ _ (refl_equal _: lgti (mkilist l1) = lgti (mkilist l2))).
      intro i ; inversion i.
    Qed.

   Lemma fRel: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(n: nat)
     (i: ilistn T n)(f1 f2: Fin n), f1 = f2 -> RelT (i f1) (i f2).
   Proof.
     intros T RelT EqT n i f1 f2 e.
     rewrite e ; reflexivity.
   Qed.

    Lemma ilist_rel_dec (T: Set)(RelT: relation T)(Req : Equivalence RelT)
      (Rdec : forall t1 t2, {RelT t1 t2}+{not (RelT t1 t2)}): 
      forall l1 l2, {ilist_rel RelT l1 l2}+{not (ilist_rel RelT l1 l2)}.
    Proof.
      intros [n1 l1] [n2 l2].
      elim (eq_nat_dec n1 n2) ; intros H.
      revert l2.
      rewrite <- H.
      intros l2 ; clear n2 H.
      fold (mkilist l1) (mkilist l2) in *|-*.
      induction n1 as [|n1 IH].
      left.
      apply (ilist_rel_mon (@eq_subrelation _ RelT _)).
      apply ilist_rel_nil.
      destruct (Rdec (l1 (first n1)) (l2 (first n1))) as [H1 | H1].
      destruct (IH (fun x => l1 (succ x)) (fun x => l2 (succ x))) as [H2 | H2].
      left.
      apply (is_ilist_rel  _ _ _ (refl_equal _: lgti (mkilist l1) = lgti (mkilist l2))).
      simpl.
      intro i.
      elim (zerop (decode_Fin i)) ; intros H3.
      rewrite (decode_Fin_0_first _ H3) in *|-* ; clear i H3.
      assumption.
      destruct H2 as [H2 H4].
      simpl in *|-*.
      assert (H5 := H4 (get_cons _ H3)).
      assert (H6 : rewriteFins H2 (get_cons i H3) = get_cons i H3) by treatFinPure.
      rewrite H6 in H5 ; clear H2 H4 H6.
      rewrite (decode_Fin_unique _ _(decode_Fin_get_cons _ _ : decode_Fin i = decode_Fin (succ (get_cons i H3)))).
      assumption.
      
      right.
      intros [H3 H4] ; apply H2.
      apply (is_ilist_rel  _ _ _ (refl_equal _: 
      lgti (mkilist (fun x => l1 (succ x))) = lgti (mkilist (fun x => l2 (succ x))))).
      simpl in *|-*.
      intro i ; rewrite (H4 (succ i)).
      apply fRel ; try assumption.
      treatFinPure.
      
      right.
      intros [H2 H3] ; apply H1.
      rewrite (H3 (first n1)).
      apply fRel ; try assumption.
      treatFinPure.
      
      right.
      intros [H1 _].
      contradiction.
    Qed.
  End ilist_rel_dec.  
End ilist_def_tools.
