(** Paths.v Version 1.2 February 2012 *)
(** runs under V8.4beta, tested with version trunk 15623 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of exploration of the graphs
    with paths *)

Require Import List.
Require Import Setoid.

Require Import Tools.
Require Import Fin.
Require Import Ilist.
Require Import IlistPerm.
Require Import Graphs.
Require Import Utf8.

Set Implicit Arguments.

Section GeqPath.
    
    Definition label_path (T: Set)(l: list nat): forall (g: Graph T), option T.
    Proof.
      induction l as [| a l IH].
      intros [t _].
      exact (Some t).
      intros [_ [n ln]].
      elim (le_lt_dec n a) ; intros h.
      exact None.
      exact (IH (ln (code_Fin1 h))).
    Defined.
    
    Definition graph_test: Graph nat.
    Proof. 
      apply (mk_Graph 0).
      set (n00 := mk_Graph 5 (singleton (mk_Graph 6 (inil _)))).
      assert (sn1 : ilistn (Graph nat) 2).
      set (n11 := mk_Graph 4 (inil _)).
      set (n10 := mk_Graph 3 (singleton  n11)).
      exact (fun f => match f with first _ => n10 | succ _ _ => n11 end).
      apply (@mkilist _ 2 (fun f => match f with first _ => mk_Graph 1 (singleton n00) | 
        succ _ _ => mk_Graph 2 (mkilist sn1) end)).
    Defined.
    
    Lemma label_path_test1 : label_path nil graph_test = Some 0.
    Proof. 
      reflexivity.
    Qed.

    Lemma label_path_test2 : label_path (0 :: 0 :: 0 :: nil) graph_test = Some 6.
    Proof.
      reflexivity.
    Qed.

    Lemma label_path_test3 : label_path (1 :: nil) graph_test = Some 2.
    Proof.
      reflexivity.
    Qed.

    Lemma label_path_test4 : label_path (1 :: 1 :: nil) graph_test = 
      label_path (1 :: 0 :: 0 :: nil) graph_test.
    Proof.
      reflexivity.
    Qed.

    Lemma label_path_test5 : label_path (1 :: 2 :: nil) graph_test = None.
    Proof.
      reflexivity.
    Qed.
        
    Lemma label_path_test6 : label_path (2 :: nil) graph_test = None.
    Proof.
      reflexivity.
    Qed.

    Definition GeqPath (T: Set)(RelT: relation T)(g1 g2: Graph T): Prop := 
      forall l: list nat, RelOp RelT (label_path l g1) (label_path l g2).

    Lemma label_path_sons (T: Set)(RelT : relation T)(g: Graph T)(n: nat)(h: n < lgti (sons g)):
      label_path (n :: nil) g = Some (label (fcti (sons g) (code_Fin1 h))).
    Proof.
      destruct g as [t [ng ln]].
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec ng n) ; intros a.
      apply False_rec, (lt_irrefl _ (lt_le_trans _ _ _ h a)).
      assert (H: code_Fin1 a = code_Fin1 h).
      apply decode_Fin_unique ; do 2 rewrite decode_code1_Id.
      reflexivity.
      rewrite H.
      set (g := ln (code_Fin1 h)) ; destruct g as [tg sg].
      reflexivity.
    Qed.

    Lemma label_path_sons_gene (T: Set)(RelT : relation T)(g: Graph T)(n: nat)(l: list nat)
      (h: n < lgti (sons g)): label_path (n :: l) g = label_path l (fcti (sons g) (code_Fin1 h)).
    Proof.
      destruct g as [t [n' ln]].
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec n' n) ; intros a.
      apply False_rec, (lt_irrefl n'), (le_lt_trans _ _ _ a h).
      do 2 f_equal.
      treatFinPure.
    Qed.

    Lemma label_path_inf_n (T: Set)(RelT : relation T)(g: Graph T)(n: nat)(t: T):
      label_path (n :: nil) g = Some t -> n < lgti (sons g).
    Proof.
      destruct g as [gt [ng ln]].
      simpl in *|-*.
      elim (le_lt_dec ng n) ; intros H a.
      inversion a.
      assumption.
    Qed.

    Lemma label_path_inf_n_rel (T: Set)(RelT : relation T)(g: Graph T)(n: nat)(t: T):
      RelOp RelT (label_path (n :: nil) g) (Some t) -> n < lgti (sons g).
    Proof.
      destruct g as [gt [ng ln]].
      simpl in *|-*.
      elim (le_lt_dec ng n) ; intros H a.
      inversion a.
      assumption.
    Qed.

    Lemma label_path_inf_n_rel_sym (T: Set)(RelT : relation T)(g: Graph T)(n: nat)(t: T):
      RelOp RelT (Some t) (label_path (n :: nil) g) -> n < lgti (sons g).
    Proof.
      destruct g as [gt [ng ln]].
      simpl in *|-*.
      elim (le_lt_dec ng n) ; intros H a.
      inversion a.
      assumption.
    Qed.
    
    Lemma GeqPath_lgti (T: Set)(RelT: relation T)(g1 g2: Graph T): 
      GeqPath RelT g1 g2 -> lgti (sons g1) = lgti (sons g2).
    Proof.
      intros H.
      destruct g1 as [t1 [[|n1] ln1]] ;  destruct g2 as [t2 [[|n2] ln2]] ; 
      fold (mkilist ln1) (mkilist ln2) in *|-* ; 
      simpl ; unfold GeqPath in H.

      reflexivity.

      assert (H' := H (n2 :: nil)).
      rewrite (label_path_sons RelT (mk_Graph t2 (mkilist ln2)) (lt_n_Sn n2)) in H'.
      inversion H'.
      assert (H' := H (n1 :: nil)).
      rewrite (label_path_sons RelT (mk_Graph t1 (mkilist ln1)) (lt_n_Sn n1)) in H'.
      inversion H'.

      assert (H1 := H (n1 :: nil)).
      rewrite (label_path_sons RelT (mk_Graph t1 (mkilist ln1)) (lt_n_Sn n1)) in H1.
      assert (H1lgti := label_path_inf_n_rel_sym RelT _ _ _ H1).
      assert (H2 := H (n2 :: nil)).
      rewrite (label_path_sons RelT (mk_Graph t2 (mkilist ln2)) (lt_n_Sn n2)) in H2.
      assert (H2lgti := label_path_inf_n_rel RelT _ _ _ H2).
      rewrite (le_antisym _ _ (lt_n_Sm_le _ _ H1lgti) (lt_n_Sm_le _ _ H2lgti)).
      reflexivity.
    Qed.

    Lemma GeqPath_refl (T: Set)(RelT: relation T)(Req: Equivalence RelT)(g: Graph T): 
      GeqPath RelT g g.
    Proof.
      intros l ; destruct g as [t [n ln]].
      apply (RelOp_refl _).
    Qed.

    Lemma GeqPath_sym (T: Set)(RelT: relation T)(Req: Equivalence RelT)(g1 g2: Graph T): 
      GeqPath RelT g1 g2 -> GeqPath RelT g2 g1.
    Proof.
      intros H l ; destruct g1 as [t1 [n1 ln1]] ; destruct g2 as [t2 [n2 ln2]].
      apply (RelOp_sym _), (H l).
    Qed.

    Lemma GeqPath_trans (T: Set)(RelT: relation T)(Req: Equivalence RelT)(g1 g2 g3: Graph T): 
      GeqPath RelT g1 g2 -> GeqPath RelT g2 g3 -> GeqPath RelT g1 g3.
    Proof.
      intros H1 H2 l ; destruct g1 as [t1 [n1 ln1]] ; destruct g2 as [t2 [n2 ln2]] ; 
        destruct g3 as [t3 [n3 ln3]].
      apply (RelOp_trans _ _ (label_path l
       (mk_Graph t2 (existT (fun n : nat => ilistn (Graph T) n) n2 ln2)))).
      apply (H1 l).
      apply (H2 l).
    Qed.

    Add Parametric Relation (T: Set)(RelT: relation T)(Req: Equivalence RelT): 
        (Graph T) (GeqPath RelT)
      reflexivity proved by (GeqPath_refl Req)
      symmetry proved by (GeqPath_sym Req)
      transitivity proved by (GeqPath_trans Req)
      as GeqPathRel.

    Lemma GeqPath_Geq (T: Set)(RelT: relation T)(g1 g2: Graph T): 
      GeqPath RelT g1 g2 -> Geq RelT g1 g2.
    Proof.
      revert g1 g2 ; cofix Hc ; intros [t1 [n1 ln1]] [t2 [n2 ln2]] H ; 
      fold (mkilist ln1) (mkilist ln2) in *|-*.
      apply Geq_intro  ; simpl in *|-*.
      unfold GeqPath in H.
      apply (H nil).
      assert (h1 := GeqPath_lgti H : lgti (mkilist ln1) = lgti (mkilist ln2)).
      apply (is_ilist_rel _ _ _ h1).
      simpl in *|-*.
      intro f.
      apply Hc.
      intro l.
      assert (H' := H ((decode_Fin f) :: l)).
      rewrite (label_path_sons_gene RelT _ _ (decode_Fin_inf_n f : 
        decode_Fin f < lgti (sons (mk_Graph t1 (mkilist ln1))))) 
        in H'.
      assert (H1 := decode_Fin_inf_n f).
      rewrite h1 in H1.
      change n2 with (lgti (sons (mk_Graph t2 (mkilist ln2)))) in H1.
      rewrite (label_path_sons_gene RelT _ _ H1) in H'.
      simpl in H'.
      rewrite code1_decode_Id in H'.
      assert (H2 : code_Fin1 H1 = rewriteFins h1 f) by treatFinPure.
      rewrite <- H2.
      assumption.
    Qed.
    
    Lemma Geq_GeqPath (T: Set)(RelT: relation T)(g1 g2: Graph T): 
      Geq RelT g1 g2 -> GeqPath RelT g1 g2.
    Proof.
      intros H l ; revert g1 g2 H ; induction l as [|n q IH] ;
      intros _ _ [[t1 [n1 ln1]] [t2 [n2 ln2]] h1 [h3 h4]].
      assumption.
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      assert (h5 := h3) ; revert ln2 h3 h4 ; rewrite <- h5 ; clear n2 h5 ; intros ln2 h3 h4.
      elim (le_lt_dec n1 n) ; intros a.
      reflexivity.
      apply IH.
      assert (h5 : code_Fin1 a = rewriteFins h3 (code_Fin1 a)) by treatFinPure.
      rewrite h5 at 2.
      apply h4.
    Qed.

    Definition getGraph_path (T: Set)(l: list nat)(g: Graph T): option (Graph T).
    Proof.
      revert g.
      induction l as [|n l IH].
      intros g ; exact (Some g).
      intros [labg [lgtig sonsg]].
      elim (le_lt_dec lgtig n) ; intros a.
      exact None.
      exact (IH (sonsg (code_Fin1 a))).
    Defined. 
     
    Lemma getGraph_path_labelpath_None (T: Set)(l: list nat)(g: Graph T) : 
      getGraph_path l g = None -> label_path l g = None.
    Proof.
      revert g ; induction l as [|n l IH] ; intros [labg [lgtig sonsg]].
      intro H ; inversion H.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgtig n) ; intros a.
      reflexivity.
      apply IH.
    Qed.
      
    Lemma labelpath_getGraph_path_None (T: Set)(l: list nat)(g: Graph T) : 
      label_path l g = None -> getGraph_path l g = None.
    Proof.
      revert g ; induction l as [|n l IH] ; intros [labg [lgtig sonsg]].
      intro H ; inversion H.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgtig n) ; intros a.
      reflexivity.
      apply IH.
    Qed.

    Lemma getGraph_path_labelpath_Some (T: Set)(l: list nat)(g: Graph T)(RelT: relation T): 
      (exists g', RelOp (Geq RelT) (getGraph_path l g) (Some g')) -> 
      exists lab, RelOp RelT (label_path l g) (Some lab).
    Proof.
      revert g ; induction l as [|n l IH] ; intros [labg [lgtig sonsg]].
      intros [[labg' sonsg'] H].
      exists labg'.
      inversion H as [g1 g2 H1 H2 h1 h2] ; clear g1 g2 h1 h2.
      simpl in *|-*.
      assumption.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgtig n) ; intros a.
      intros [g' H].
      inversion H.
      intros [[labg' sonsg'] H].
      apply IH.
      exists (mk_Graph labg' sonsg'); assumption.
    Qed.

    Lemma labelpath_getGraph_path_Some (T: Set)(l: list nat)(g: Graph T)(RelT: relation T)
      (EqT: Equivalence RelT): (exists lab, RelOp RelT (label_path l g) (Some lab)) ->
      (exists g', RelOp (Geq RelT) (getGraph_path l g) (Some g')).
    Proof.
      revert g ; induction l as [|n l IH] ; intros [labg [lgtig sonsg]].
      intros [lab H].
      simpl in *|-*.
      exists (mk_Graph lab (existT (fun n : nat => ilistn (Graph T) n) lgtig sonsg)).
      apply Geq_intro.
      simpl.
      assumption.
      simpl.
      apply (ilist_rel_refl (Geq_refl _)).
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgtig n) ; intros a.
      intros [lab H] ; inversion H.
      intros [lab H].
      apply IH.
      exists lab ; assumption.
    Qed.

    Lemma getGraph_path_GinG (T: Set)(g g': Graph T)(RelT: relation T): 
      Graph_in_Graph RelT g' g -> exists l, RelOp (Geq RelT) (Some g') (getGraph_path l g).
    Proof.
      intro H.
      induction H as [[lab1 [lgti1 sons1]] i1 H3|[lab1 [lgti1 sons1]] i1 H3 [l IH]].
      exists (decode_Fin i1 :: nil).
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 (decode_Fin i1)) ; intros a.
      apply (lt_irrefl _ (le_lt_trans _ _ _ a (decode_Fin_inf_n i1))).
      assert (h: code_Fin1 a = i1).
      apply decode_Fin_unique, decode_code1_Id.
      rewrite h ; assumption.
      exists (decode_Fin i1 :: l).
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 (decode_Fin i1)) ; intros a.
      apply (lt_irrefl _ (le_lt_trans _ _ _ a (decode_Fin_inf_n i1))).
      assert (h: code_Fin1 a = i1).
      apply decode_Fin_unique, decode_code1_Id.
      rewrite h.
      apply IH.
    Qed.

    Lemma getGraph_path_GinG2 (T: Set)(g g': Graph T)(RelT: relation T): 
      Graph_in_Graph RelT g' g -> 
      exists n, exists l, RelOp (Geq RelT) (Some g') (getGraph_path (n :: l) g).
    Proof.
      intro H.
      induction H as [[lab1 [lgti1 sons1]] i1 H3|[lab1 [lgti1 sons1]] i1 H3 [n [l IH]]].
      exists (decode_Fin i1) ; exists nil.
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 (decode_Fin i1)) ; intros a.
      apply (lt_irrefl _ (le_lt_trans _ _ _ a (decode_Fin_inf_n i1))).
      assert (h: code_Fin1 a = i1).
      apply decode_Fin_unique, decode_code1_Id.
      rewrite h ; assumption.
      exists (decode_Fin i1); exists (n :: l).
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 (decode_Fin i1)) ; intros a.
      apply (lt_irrefl _ (le_lt_trans _ _ _ a (decode_Fin_inf_n i1))).
      assert (h: code_Fin1 a = i1).
      apply decode_Fin_unique, decode_code1_Id.
      rewrite h.
      apply IH.
    Qed.

    Lemma getGraph_path_GinG3 (T: Set)(g g': Graph T)(RelT: relation T): 
      Graph_in_Graph RelT g' g -> 
      exists l, RelOp (Geq RelT) (Some g') (getGraph_path l g) /\ 0 < length l.
    Proof.
      intro H.
      destruct (getGraph_path_GinG2 H) as [n [l H1]].
      exists (n :: l).
      split.
      assumption.
      apply lt_O_Sn.
    Qed.

    Lemma getGraph_path_Some_in (T: Set)(g: Graph T)(l: list nat)(RelT: relation T)
      (EqT: Equivalence RelT) : (exists g', RelOp (Geq RelT) (getGraph_path l g) (Some g')) ->
      (exists g', RelOp (Geq RelT) (getGraph_path l g) (Some g') /\ 
        (Graph_in_Graph RelT g' g \/ Geq RelT g g')).
    Proof.
      intros [g' H].
      exists g'.
      split.
      assumption.
      destruct l as [|n l].
      simpl in H.
      right; assumption.
      left.
      simpl in H.
      destruct g as [labg [lgtig sonsg]].
      unfold sumbool_rec, sumbool_rect in H.
      revert H.
      elim (le_lt_dec lgtig n).
      intros a H.
      inversion H.
      revert labg lgtig sonsg n g'.
      induction l as [|n' l IH] ;
      intros labg lgtig sonsg n [labg' sonsg'] a H.
      simpl in H.
      apply (is_Graph_in_Graph_dir _ 
        (code_Fin1 a : Fin (lgti (sons (mk_Graph labg (existT _ lgtig sonsg)))))).
      apply (Geq_sym _ H).
      
      apply (is_Graph_in_Graph_indir _ 
        (code_Fin1 a : Fin (lgti (sons (mk_Graph labg (existT _ lgtig sonsg)))))).
      simpl.
      revert H.
      set (g := sonsg (code_Fin1 a)).
      set (g' := (mk_Graph labg' sonsg')).
      destruct g as [labg2 [lgtig2 sonsg2]].
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgtig2 n') ; intros b H.
      inversion H.
      apply (IH _ _ _ _ _ _  H).
   Qed.

    Lemma getGraph_path_Some_in2 (T: Set)(g: Graph T)(l: list nat)(RelT: relation T)
      (EqT: Equivalence RelT) (g': Graph T): (RelOp (Geq RelT) (getGraph_path l g) (Some g')) ->
      Graph_in_Graph RelT g' g \/ Geq RelT g g'.
    Proof.
      intros H.
      assert (H1 := getGraph_path_Some_in g l EqT).
      destruct H1 as [g'' [H1 [H2 |H2]]] ; 
      try assert (H3 := RelOp_trans (Geq_trans _) _ _ _ (RelOp_sym (Geq_sym _) _ _ H) H1).
      exists g'.
      assumption.
      left.
      apply (Graph_in_GraphM2 EqT (Geq_sym _ H3) H2).
      right.
      apply (Geq_trans _ H2 (Geq_sym _ H3)).
   Qed.

    Lemma getGraph_path_Some_cons_in (T: Set)(g: Graph T)(n: nat)(l: list nat)(RelT: relation T)
      (EqT: Equivalence RelT) (g': Graph T): 
      (RelOp (Geq RelT) (getGraph_path (n::l) g) (Some g')) -> Graph_in_Graph RelT g' g.
    Proof.
      revert g n g'.
      induction l as [| n' l IH] ; 
      intros [labg [lgtig sonsg]] n g' ;
      simpl ; unfold sumbool_rec, sumbool_rect; elim (le_lt_dec lgtig n) ; intros a H.
      inversion H.
      apply (is_Graph_in_Graph_dir _ 
        (code_Fin1 a : Fin (lgti (sons (mk_Graph labg (existT _ lgtig sonsg))))) (Geq_sym _ H)).
      inversion H.
      apply (is_Graph_in_Graph_indir _ 
        (code_Fin1 a : Fin (lgti (sons (mk_Graph labg (existT _ lgtig sonsg))))) (IH _ _ _ H)).
   Qed.

   Lemma getGraph_path_Some_cons_in2 (T: Set)(g: Graph T)(l: list nat)(RelT: relation T)
      (EqT: Equivalence RelT) (g': Graph T): (RelOp (Geq RelT) (getGraph_path l g) (Some g')) ->
      length l > 0 -> Graph_in_Graph RelT g' g.
   Proof.
     intros h1 h2.
     destruct l as [|n l].
     apply False_rec, (lt_irrefl _ h2).
     apply (getGraph_path_Some_cons_in _ n l EqT _ h1).
   Qed.

End GeqPath.

Section GeqPermPath. 
    Variable T: Set.
    Variable RelT: relation T.
    Variable Req: Equivalence RelT.

    (* Definitions that two paths through two graphs are equivalent *)
    Definition EquivPaths (l1 : list nat)(g1: Graph T)(l2 : list nat)(g2 : Graph T): Prop.
    Proof.
      revert g1 g2 l2 ; induction l1 as [|n1 l1 IH] ; intros [lab1 sons1] [lab2 sons2] [|n2 l2].
      (* empty paths: we must check that the labels are equivalent
         and that the labels of the sons are permutations *)
      exact (RelT lab1 lab2 /\ IlistPerm3 RelT (imap (@label _) sons1) (imap (@label _) sons2)).
      (* one path is empty but the other is not ==> not equivalent *) 
      exact False.
      (* one path is empty but the other is not ==> not equivalent *) 
      exact False.
      (* both paths are not empty *)
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2].
      (* We check that both index are indeed index of the concerned ilist *)
      elim (le_lt_dec lgti1 n1) ; intros a ;
      elim (le_lt_dec lgti2 n2) ; intros b.
      (* both indexes are not correct ==> equivalent ? *)
      exact True.
      (* one is index but the other not ==> not equivalent *)
      exact False.
      (* one is index but the other not ==> equivalent *)
      exact False.
      (* both are good indexes : we must check that the labels of respective nodes are equivalent
         and that the rest of the paths are equivalent *)
      set (g1' := ln1 (code_Fin1 a)) ; set (g2' := ln2 (code_Fin1 b)).
      exact (RelT (label g1') (label g2') /\ (IH g1' g2' l2)).
    Defined.

    Lemma EquivPaths_refl : forall l g, EquivPaths l g l g.
    Proof.
      induction l as [|n l IH] ; intros [lab1 sons1].
      split.
      reflexivity.
      apply (IlistPerm3_refl Req).
      destruct sons1 as [lgti1 ln1].
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n) ; intros a.
      reflexivity.
      split.
      reflexivity.
      apply IH.
    Qed.
   
    Lemma EquivPaths_sym : forall l1 l2 g1 g2, EquivPaths l1 g1 l2 g2 -> EquivPaths l2 g2 l1 g1.
    Proof.
      induction l1 as [|n1 l1 IH] ; intros [|n2 l2] [lab1 sons1] [lab2 sons2] H.
      destruct H as [H1 H2].
      split ; [symmetry | apply (IlistPerm3_sym Req)] ; assumption.
      destruct H.
      destruct H.
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2].
      revert H.
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n1) ; intros a ; elim (le_lt_dec lgti2 n2) ; intros b H ; 
      try assumption.
      destruct H as [H1 H2].
      split ; [symmetry |apply IH] ; assumption.
    Qed.
   
    Lemma EquivPaths_trans : forall l1 l2 l3 g1 g2 g3, 
      EquivPaths l1 g1 l2 g2 -> EquivPaths l2 g2 l3 g3 -> EquivPaths l1 g1 l3 g3.
    Proof.
      induction l1 as [|n1 l1 IH] ;
      intros [|n2 l2] [|n3 l3] [lab1 sons1] [lab2 sons2] [lab3 sons3] H1 H2 ; 
      try apply H1 ; try apply H2.
      destruct H1 as [H11 H12] ; destruct H2 as [H21 H22].
      split.
      transitivity lab2 ; assumption.
      apply IlistPerm4_IlistPerm3_eq.
      apply IlistPerm3_IlistPerm4_eq in H22.
      apply IlistPerm3_IlistPerm4_eq in H12.
      apply (IlistPerm4_trans Req H12 H22).
      inversion H2.
      inversion H2.
      
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2] ; 
      destruct sons3 as [lgti3 ln3].
      revert H1 H2.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n1) ; intros a ; elim (le_lt_dec lgti2 n2) ; intros b ; 
      elim (le_lt_dec lgti3 n3) ; intros c H1 H2 ; try assumption. 
      reflexivity.
      inversion H1.
      destruct H1 as [H11 H12] ; destruct H2 as [H21 H22].
      split.
      transitivity (label (ln2 (code_Fin1 b))) ; assumption.
      apply (IH _ _ _ _ _ H12 H22).
    Qed.

    Lemma EquivPaths_nil : forall g1 g2 l, EquivPaths nil g1 l g2 -> l = nil.
    Proof.
      destruct l as [|t l]; intro H.
      reflexivity.
      destruct g1 as [lab1 sons1] ; destruct g2 as [lab2 sons2].
      inversion H.
    Qed.
  
    (* Definitions that two paths through two graphs are equivalent *)
    Definition EquivPathsBis (l1 : list nat)(g1: Graph T)(l2 : list nat)(g2 : Graph T): Prop.
    Proof.
      revert g1 g2 l2 ; induction l1 as [|n1 l1 IH] ; intros [lab1 sons1] [lab2 sons2] [|n2 l2].
      (* empty paths: we must check that the labels are equivalent
         and that the labels of the sons are permutations *)
      exact (RelT lab1 lab2).
      (* one path is empty but the other is not ==> not equivalent *) 
      exact False.
      (* one path is empty but the other is not ==> not equivalent *) 
      exact False.
      (* both paths are not empty *)
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2].
      (* We check that both index are indeed index of the concerned ilist *)
      elim (le_lt_dec lgti1 n1) ; intros a ;
      elim (le_lt_dec lgti2 n2) ; intros b.
      (* both indexes are not correct ==> equivalent ? *)
      exact True.
      (* one is index but the other not ==> not equivalent *)
      exact False.
      (* one is index but the other not ==> equivalent *)
      exact False.
      (* both are good indexes : we must check that the labels of respective nodes are equivalent
         and that the rest of the paths are equivalent *)
      set (g1' := ln1 (code_Fin1 a)) ; set (g2' := ln2 (code_Fin1 b)).
      exact (RelT (label g1') (label g2') /\ (IH g1' g2' l2)).
    Defined.

    Lemma EquivPathsBis_refl : forall l g, EquivPathsBis l g l g.
    Proof.
      induction l as [|n l IH] ; intros [lab1 sons1].
      simpl.
      reflexivity.
      destruct sons1 as [lgti1 ln1].
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n) ; intros a.
      reflexivity.
      split.
      reflexivity.
      apply IH.
    Qed.
   
    Lemma EquivPathsBis_sym : forall l1 l2 g1 g2, EquivPathsBis l1 g1 l2 g2 -> 
      EquivPathsBis l2 g2 l1 g1.
    Proof.
      induction l1 as [|n1 l1 IH] ; intros [|n2 l2] [lab1 sons1] [lab2 sons2] H.
      simpl in *|-*.
      symmetry; assumption.
      destruct H.
      destruct H.
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2].
      revert H.
      simpl in *|-*.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n1) ; intros a ; elim (le_lt_dec lgti2 n2) ; intros b H ; 
      try assumption.
      destruct H as [H1 H2].
      split ; [symmetry |apply IH] ; assumption.
    Qed.
   
    Lemma EquivPathsBis_trans : forall l1 l2 l3 g1 g2 g3, 
      EquivPathsBis l1 g1 l2 g2 -> EquivPathsBis l2 g2 l3 g3 -> EquivPathsBis l1 g1 l3 g3.
    Proof.
      induction l1 as [|n1 l1 IH] ;
      intros [|n2 l2] [|n3 l3] [lab1 sons1] [lab2 sons2] [lab3 sons3] H1 H2 ; 
      try apply H1 ; try apply H2.
      simpl in *|-*.
      transitivity lab2 ; assumption.
      inversion H1.
      inversion H1.
      
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2] ; 
      destruct sons3 as [lgti3 ln3].
      revert H1 H2.
      simpl.
      unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n1) ; intros a ; elim (le_lt_dec lgti2 n2) ; intros b ; 
      elim (le_lt_dec lgti3 n3) ; intros c H1 H2 ; try assumption. 
      reflexivity.
      inversion H1.
      destruct H1 as [H11 H12] ; destruct H2 as [H21 H22].
      split.
      transitivity (label (ln2 (code_Fin1 b))) ; assumption.
      apply (IH _ _ _ _ _ H12 H22).
    Qed.

    Lemma EquivPaths_EquivPathsBis : forall l1 l2 g1 g2, 
      EquivPaths l1 g1 l2 g2 -> EquivPathsBis l1 g1 l2 g2.
    Proof.
      induction l1 as [|n1 l1 IH] ;
      intros [|n2 l2] [lab1 [lgti1 sons1]] [lab2 [lgti2 sons2]] ; try (intros H1 ; assumption).
      intros [H1 _] ; assumption.
      simpl ; unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n1) ; elim (le_lt_dec lgti2 n2) ; intros b a H1 ; try assumption.
      destruct H1 as [H1 H2].
      split.
      assumption.
      apply (IH _ _ _ H2).
    Qed.

    Inductive EquivPaths_ter(l1 : list nat)(g1: Graph T)(l2 : list nat)(g2 : Graph T): Prop := 
      is_EPt : RelOp RelT (label_path l1 g1) (label_path l2 g2) -> EquivPaths_ter l1 g1 l2 g2.
      
    Lemma EquivPaths_EquivPaths_ter : forall l1 l2 g1 g2, 
      EquivPaths l1 g1 l2 g2 -> EquivPaths_ter l1 g1 l2 g2.
    Proof.
      induction l1 as [|n1 l1 IH] ;
      intros [|n2 l2] [lab1 [lgti1 sons1]] [lab2 [lgti2 sons2]] ; intros H1 ; apply is_EPt.
      destruct H1 as [H1 _] ; assumption.
      inversion H1.
      inversion H1.
      revert H1.
      simpl ; unfold sumbool_rec, sumbool_rect.
      elim (le_lt_dec lgti1 n1) ;
      elim (le_lt_dec lgti2 n2) ; intros b a H1.
      reflexivity.
      inversion H1.
      inversion H1.
      destruct H1 as [H1 H2].
      apply IH, H2.
    Qed.
    
    Definition GeqPermPath (g1 g2: Graph T): Prop := 
      (forall l1: list nat, exists l2 : list nat, EquivPaths l1 g1 l2 g2) /\
      (forall l2: list nat, exists l1 : list nat, EquivPaths l1 g1 l2 g2).
     
    Lemma GeqPermPath_refl : forall g, GeqPermPath g g.
    Proof.
      intros g ; split ; intro l ; exists l ; apply EquivPaths_refl.
    Qed.
     
    Lemma GeqPermPath_sym : forall g1 g2, GeqPermPath g1 g2 -> GeqPermPath g2 g1.
    Proof.
      intros g1 g2 [H1 H2] ; split.
      intros l2.
      destruct (H2 l2) as [l1 H2'].
      exists l1.
      apply (EquivPaths_sym _ _ _ _ H2').
      intros l1. 
      destruct (H1 l1) as [l2 H1'].
      exists l2.
      apply (EquivPaths_sym _ _ _ _ H1').
    Qed.
     
    Lemma GeqPermPath_trans : 
      forall g1 g2 g3, GeqPermPath g1 g2 -> GeqPermPath g2 g3 -> GeqPermPath g1 g3.
    Proof.
      intros g1 g2 g3 H1 H2. 
      split.
      destruct  H1 as [H1 _] ; destruct H2 as [H2 _].
      intro l1.
      destruct (H1 l1) as [l2 H1'].
      destruct (H2 l2) as [l3 H2'].
      exists l3.
      apply (EquivPaths_trans _ _ _ _ _ _ H1' H2').
      destruct  H1 as [_ H1] ; destruct H2 as [_ H2].
      intro l3.
      destruct (H2 l3) as [l2 H2'].
      destruct (H1 l2) as [l1 H1'].
      exists l1.
      apply (EquivPaths_trans _ _ _ _ _ _ H1' H2').
    Qed.

    Lemma Geq_GeqPermPath_aux : forall g1 g2, Geq RelT g1 g2 -> 
      (forall l1: list nat, exists l2 : list nat, EquivPaths l1 g1 l2 g2).
    Proof.
      intros g1 g2 H l ; exists l ;
      revert g1 g2 H ; induction l as [|t l IH] ; 
      intros _ _ [[lab1 sons1] [lab2 sons2] H1 H2].

      simpl in *|-* .
      split.
      assumption.
      assert (H3 :=imap_ilist_rel Req (@labelM _ RelT) H2).
      apply (ilist_rel_finer_IlistPerm3 H3).
      destruct sons1 as [lgti1 ln1] ; destruct sons2 as [lgti2 ln2].
      simpl.
      unfold sumbool_rec, sumbool_rect.
      inversion H2 as [h2 H3] ; simpl in h2, H3.
      elim (le_lt_dec lgti1 t) ; elim (le_lt_dec lgti2 t) ; intros b a.
      reflexivity.
      assert (c := le_lt_trans _ _ _ a b).
      rewrite h2 in c.
      apply (lt_irrefl _ c).
      assert (c := le_lt_trans _ _ _ b a).
      rewrite h2 in c.
      apply (lt_irrefl _ c).
      assert (h3 : code_Fin1 b = rewriteFins h2 (code_Fin1 a)).
      apply decode_Fin_unique.
      unfold rewriteFins.
      rewrite <- decode_Fin_match.
      do 2 rewrite decode_code1_Id.
      reflexivity.
      rewrite h3.
      split.
      apply (labelM (H3 (code_Fin1 a))).
      apply (IH _ _ (H3 (code_Fin1 a))).
    Qed.

    Lemma Geq_GeqPermPath : forall g1 g2, Geq RelT g1 g2 -> GeqPermPath g1 g2.
    Proof.
      split.
      apply (Geq_GeqPermPath_aux H).
      intro l2.
      assert (H1 := Geq_GeqPermPath_aux (Geq_sym _ H)).
      destruct (H1 l2) as [l1 H2].
      exists l1.
      apply (EquivPaths_sym _ _ _ _ H2).
    Qed.

End GeqPermPath.