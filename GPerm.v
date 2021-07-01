(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of various relations using permutations on 
    Graphs and equivalence proofs with associated tools and lemmas *)

Require Import Fin.
Require Import Ilist.
Require Import Extroduce.
Require Import IlistPerm.
Require Import Setoid.
Require Import Utf8.
Require Import Graphs.
Require Import Basics.

Set Implicit Arguments.

Section GeqPerm. 
    Variable T: Set.
    Variable RelT: relation T.

    (* Trees to represent Graphs only to a certain depth*)
    Inductive TreeG : Set := 
      mk_TreeG : T -> ilist TreeG -> TreeG.
    
    Definition labelT (t: TreeG) : T := let (l, _) := t  in l.
    Definition sonsT (t: TreeG) : ilist TreeG := let (_, s) := t in s.

    Lemma labelT_sonsT_ok (t: TreeG) : mk_TreeG (labelT t) (sonsT t) = t.
    Proof.
      destruct t as [lab s].
      reflexivity.
    Qed.
    
    (* A first relation transformer on TreeG to test the definition *)
    Inductive Teq: TreeG -> TreeG -> Prop := 
      Teq_intro: forall t1 t2,
        RelT (labelT t1) (labelT t2) -> ilist_rel Teq (sonsT t1) (sonsT t2) -> Teq t1 t2.
 
    (* A better induction principle on TreeG *)
    Lemma TreeG_ind_better : forall (P: TreeG -> Prop),
      (forall (t : T) (l: ilist TreeG), (forall i, P (fcti l i))  -> 
      P (mk_TreeG t l)) -> (forall t, P t).
    Proof.
      intros P H.
      fix Hr 1.
      intros [lab l].
      apply H.
      intro i.
      apply Hr.
    Qed.

    (* In the following lines : proof that Teq preserves equivalence *)
    Lemma Teq_refl (RRefl : Reflexive RelT): forall t, Teq t t.
    Proof.
      induction t as [lab l IH] using TreeG_ind_better.
      apply Teq_intro.
      reflexivity.
      apply (is_ilist_rel _ _ _ (refl_equal _)).
      intro i.
      apply IH.
   Qed.
   
   Lemma Teq_sym (Rsym: Symmetric RelT) : forall t1 t2, Teq t1 t2 -> Teq t2 t1.
   Proof.
     induction t1 as [lab1 l1 IH] using TreeG_ind_better.
     intros [lab2 l2] H.
     inversion H as [t1 t2 H1 [h H2] H3 H4] ; clear t1 t2 H3 H4.
     apply Teq_intro.
     symmetry.
     assumption.
     simpl in *|-*.
     destruct l1 as [n l1] ; destruct l2 as [n2 l2].
     simpl in *|-*.
     revert l2 H H1 H2.
     rewrite <- h.
     intros l2 H H1 H2.
     clear h n2.
     apply (is_ilist_rel _ _ _ (refl_equal _ : lgti (existT _ n l2) = lgti (existT _ n l1))).
     simpl in *|-*.
     intro i ; apply (IH _ _ (H2 i)).
   Qed.

   Lemma Teq_trans (Rtrans: Transitive RelT)  : forall t1 t2 t3, Teq t1 t2 -> Teq t2 t3 -> Teq t1 t3.
   Proof.
     induction t1 as [lab1 l1 IH] using TreeG_ind_better.
     intros [lab2 l2] [lab3 l3] H1 H2.
     inversion H1 as [t11 t12 H11 [h1 H12] H13 H14] ; 
     inversion H2 as [t21 t22 H21 [h2 H22] H23 H24] ; 
     clear t11 t12 H13 H14 t21 t22 H23 H24 H1 H2.
     apply Teq_intro.
     apply (transitivity H11 H21).
     destruct l1 as [n l1] ; destruct l2 as [n2 l2] ; destruct l3 as [n3 l3].
     simpl in *|-*.
     revert h2 l2 l3 H11 H12 H21 H22.
     rewrite <- h1.
     intro h2 ; rewrite <- h2.
     intros l2 l3 H11 H12 H21 H22.
     apply (is_ilist_rel _ _ _ (refl_equal _ : lgti (existT _ n l1) = lgti (existT _ n l3))).
     intro i ; apply (IH _ _ _ (H12 _) (H22 _)).
   Qed.

    Add Parametric Relation (Req: Equivalence RelT) : (TreeG) (Teq)
      reflexivity proved by (Teq_refl _)
      symmetry proved by (Teq_sym _)
      transitivity proved by (Teq_trans _)
      as TeqRel.

    (* depth is n-1 *)
    (* Fundamental definition : transformation of a graph into a tree of depth n+1 *)
    Definition Graph2TreeG (n: nat)(g: Graph T) : TreeG.
    Proof.
      revert g ; induction n as [|n IH] ; intros [t l].
      exact (mk_TreeG t (@inil _)).
      exact (mk_TreeG t (imap IH l)).
    Defined.

(* the trivial corollaries *)
    Lemma Graph2TreeG_ok0 (g: Graph T): Graph2TreeG 0 g = mk_TreeG (label g) (@inil _).
      Proof.
        destruct g as [t l].
        reflexivity.
      Qed.

    Lemma Graph2TreeG_okS (n: nat)(g: Graph T): Graph2TreeG (S n) g = 
      mk_TreeG (label g) (imap (Graph2TreeG n) (sons g)).
      Proof.
        destruct g as [t l].
        reflexivity.
      Qed.
   
    Lemma Graph2TreeG_ok1 : forall g n, labelT (Graph2TreeG n g) = label g.
    Proof.
      intros [lab l] [|n] ; reflexivity.
    Qed.

    Lemma Graph2TreeG_ok2 : forall g n, n > 0 -> 
      ilist_rel eq (imap labelT (sonsT (Graph2TreeG n g))) (imap (@label _) (sons g)).
    Proof.
      destruct n as [|n]; destruct g as [lab l] ; intros h.
      apply False_rec, (lt_irrefl _ h).
      apply (is_ilist_rel _ _ _ (refl_equal _ : 
        lgti (imap labelT (imap (fun x : Graph T => Graph2TreeG n x) l)) = lgti (imap (@label _) l))).
      simpl.
      intro i.
      set (g := fcti l i).
      destruct g as [lab' l'].
      destruct n as [|n] ; reflexivity.
    Qed.
      
    (* Fundamental definition : permutation relation on TreeG *)
    Inductive TeqPerm: TreeG -> TreeG -> Prop := 
      TeqPerm_intro: forall g1 g2, RelT (labelT g1) (labelT g2) -> 
        IlistPerm3 TeqPerm (sonsT g1) (sonsT g2) -> TeqPerm g1 g2.

  Lemma TeqPerm_ind_better: forall P : TreeG → TreeG → Prop,
    (∀g1 g2 : TreeG, RelT (labelT g1) (labelT g2) → IlistPerm3 TeqPerm (sonsT g1) (sonsT g2) → 
    IlistPerm3 P (sonsT g1) (sonsT g2) -> P g1 g2) → (∀t t0 : TreeG, TeqPerm t t0 → P t t0).
    Proof.
      intros P Hyp.
      refine (fix IH (t t0: TreeG)(H: TeqPerm t t0){struct H}: P t t0 :=
      match H in TeqPerm t' t0' return P t' t0' with
        TeqPerm_intro _ _ H1 H2 => _ end).
      apply Hyp.
      assumption.
      assumption.
      induction H2.
      apply IlistPerm3_nil; assumption.
      apply (IlistPerm3_cons _ _ f1 f2).
      apply IH.
      assumption.
      assumption.
    Qed.

    (* In the following lines we show that TeqPerm preserves equivalence *)
    Lemma TeqPerm_refl (Rrefl: Reflexive RelT) (t: TreeG) : TeqPerm t t.
    Proof.
      induction t as [lab [n l] IH] using TreeG_ind_better.
      apply TeqPerm_intro.
      reflexivity.
      revert l IH ; induction n as [|n IHn] ; intros l IH.
      apply IlistPerm3_nil; reflexivity.
      apply (IlistPerm3_cons _ _ (first _ : Fin (lgti (mkilist l))) (first _ : Fin (lgti (mkilist l)))).
      apply IH.
      simpl in *|-*.
      apply IHn.
      intro i'.
      apply (IH (succ i')).
    Qed.

    Lemma TeqPerm_sym (Rsym: Symmetric RelT): forall t1 t2, TeqPerm t1 t2 -> TeqPerm t2 t1.
    Proof.
      intros t1 t2 Hyp.
      induction Hyp using TeqPerm_ind_better ; clear H0.
      apply TeqPerm_intro.
      symmetry.
      assumption.
      apply IlistPerm3_flip', H1.
    Qed.

   Lemma TeqPerm_trans (Rtrans: Transitive RelT): 
     forall t1 t2 t3, TeqPerm t1 t2 -> TeqPerm t2 t3 -> TeqPerm t1 t3.
   Proof.
      induction t1 using TreeG_ind_better.
      intros l2 l3 H1 H2.
      inversion_clear H1 as [t' t'' H11 H12].
      inversion_clear H2 as [t' t'' H21 H22].
      apply TeqPerm_intro.
      apply (transitivity H11 H21).
      apply IlistPerm3_IlistPerm4_eq in H12 ;  
      apply IlistPerm3_IlistPerm4_eq in H22.
      apply IlistPerm4_IlistPerm3_eq.
      apply (IlistPerm4_trans_refined H H12 H22).
   Qed.

    Add Parametric Relation (Req: Equivalence RelT) : (TreeG) (TeqPerm)
      reflexivity proved by (TeqPerm_refl _)
      symmetry proved by (TeqPerm_sym _)
      transitivity proved by (TeqPerm_trans _)
      as TeqPermRel.

    (* To test our definitions we first show that Teq <-> Geq *)
    Lemma Teq_Geq (g1 g2 : Graph T) : (forall n, Teq (Graph2TreeG n g1) (Graph2TreeG n g2)) -> 
      Geq RelT g1 g2.
    Proof.
      revert g1 g2.
      cofix Hc.
      intros [lab1 sons1] [lab2 sons2] H.
      apply Geq_intro.
      assert (H1 := H 0).
      simpl in *|-*.
      inversion H1 as [t1 t2 H2 H3 H4 H5] ; clear t1 t2 H3 H4 H5.
      assumption.
      
      assert (H1 := H 1).
      inversion H1 as [t1 t2 H2 [H3 H4] H5 H6] ; clear t1 t2 H2 H4 H5 H6.
      
      simpl lgti in *|-*.
      apply (is_ilist_rel _ _ _ H3).
      clear H1.
      intro i.
      apply Hc.
      
      intro n.
      assert (H1 := H (S n)).
      simpl in H1.
      inversion H1 as [t1 t2 H4 [H5 H6] H7 H8] ; clear t1 t2 H4 H7 H8.
      simpl in H5, H6.
      assert (H7 : rewriteFins H5 i = rewriteFins H3 i).
      treatFinPure.
      rewrite <- H7 ; apply (H6 i).
    Qed.

    Lemma Geq_Teq(g1 g2 : Graph T) : Geq RelT g1 g2 -> 
      (forall n, Teq (Graph2TreeG n g1) (Graph2TreeG n g2)).
    Proof.
      intros H n.
      revert g1 g2 H.
      induction n as [|n IH] ; intros [lab1 sons1] [lab2 sons2] H ; 
      inversion H as [g1 g2 H1 [H2 H3] H4 H5] ; clear g1 g2 H4 H5;
      apply Teq_intro.
      assumption.
      simpl.
      apply (is_ilist_rel _ _ _ (refl_equal _)).
      intro i ; inversion i.
      assumption.
      simpl.
      simpl in H2.
      assert (H4 : lgti (imap (fun x : Graph T => Graph2TreeG n x) sons1) = 
        lgti (imap (fun x : Graph T => Graph2TreeG n x) sons2)).
      do 2 rewrite imap_lgti.
      assumption.
      apply (is_ilist_rel _ _ _ H4).
      simpl.
      intro i.
      apply IH.
      simpl in H3.
      assert (H5 : rewriteFins H2 i = rewriteFins H4 i).
      treatFinPure.
      assert (H6 := H3 i).
      rewrite H5 in H6.
      assumption.
    Qed.

    Lemma TeqPerm_exists : forall t1 t2, TeqPerm t1 t2 -> 
      forall i1, exists i2, TeqPerm (fcti (sonsT t1) i1) (fcti (sonsT t2) i2).
    Proof.  
      intros _ _ [t1 t2 H1 H2] i1.
      apply IlistPerm3_IlistPerm4_eq in H2.
      inversion H2 as [l1 l2 H3 H4 H5 H6] ; clear l1 l2 H5 H6.
      destruct (H4 i1) as [i2 [H5 _]].
      exists i2.
      assumption.
    Qed.
   
    Lemma Graph2TreeG_Sn_lgti : forall g n, lgti (sonsT (Graph2TreeG (S n) g)) = lgti (sons g).
    Proof.
      intros [lab sons] n.
      reflexivity.
    Qed.

    (* Permutations on Graphs : the initial problem : the embedded inductive type *)
    CoInductive GeqPerm0 : relation (Graph T) :=
      GeqPerm0_intro: forall g1 g2, RelT (label g1) (label g2) -> 
        IlistPerm3 GeqPerm0 (sons g1) (sons g2) -> GeqPerm0 g1 g2.

    (* here is the impredicative encoding of GeqPerm0 *)
    Definition GeqPerm : relation (Graph T) :=
       fun (g1 g2: Graph T) => exists R: relation (Graph T), 
        (forall (g1 g2: Graph T), R g1 g2 -> RelT (label g1) (label g2) /\ 
        IlistPerm3 R (sons g1) (sons g2)) /\ R g1 g2.

    (* the Mendler-style variant - see Nakata and Uustalu, SOS'10 *)
    CoInductive GeqPerm1 : relation (Graph T) :=
      GeqPerm1_intro: forall g1 g2 (X: relation (Graph T)), subrelation X GeqPerm1 -> 
        RelT (label g1) (label g2) -> IlistPerm3 X (sons g1) (sons g2) -> GeqPerm1 g1 g2.

    Lemma GeqPerm_coind (R: relation (Graph T))
       (s: forall (g1 g2: Graph T), R g1 g2 -> RelT (label g1) (label g2) 
       /\ IlistPerm3 R (sons g1) (sons g2)) (g1 g2: Graph T)(t: R g1 g2): GeqPerm g1 g2.
    Proof.
      red.
      exists R.
      split ; 
      assumption.
    Qed.

    Lemma GeqPerm_out (g1 g2: Graph T)(Hyp: GeqPerm g1 g2): 
      RelT (label g1) (label g2) /\ IlistPerm3 GeqPerm (sons g1) (sons g2).
    Proof.
      destruct Hyp as [R [Hyp1 Hyp2]].
      assert (H := Hyp1 _ _ Hyp2).
      destruct H as [H1 H2].
      split.
      assumption.
      apply (@IlistPerm3_mon _ _ _ R) ; try assumption.
      exact (GeqPerm_coind Hyp1).
    Qed.
  
    Lemma GeqPerm_intro: forall g1 g2, RelT (label g1) (label g2) -> 
        IlistPerm3 GeqPerm (sons g1) (sons g2) -> GeqPerm g1 g2.
    Proof.
      intros g1 g2 H1 H2.
      apply (GeqPerm_coind (R:= fun (g1 g2: Graph T) => RelT (label g1) (label g2) 
        /\ IlistPerm3 GeqPerm (sons g1) (sons g2))).
      clear g1 g2 H1 H2 ; intros g1 g2 [H1 H2].
      split ; try assumption.
      apply (@IlistPerm3_mon _ _ _ GeqPerm) ; try assumption.
      red.
      apply GeqPerm_out.
      split; assumption.
    Qed.
      
    Lemma GeqPerm0_GeqPerm: subrelation GeqPerm0 GeqPerm.
    Proof.
      intros g1 g2 Hyp.
      apply (GeqPerm_coind (R:= GeqPerm0)) ; try assumption.
      clear g1 g2 Hyp ; intros _ _ [g1 g2 H1 H2].
      split; assumption.
    Qed.

(* the following is only morally correct but not accepted by Coq when doing Qed:
    Lemma GeqPerm_GeqPerm0: subrelation GeqPerm GeqPerm0.
    Proof.
      cofix.
      intros g1 g2 Hyp.
      destruct (GeqPerm_out Hyp) as [H1 H2].
      apply GeqPerm0_intro.
      assumption.
      exact (IlistPerm3_mon GeqPerm_GeqPerm0 H2).
    Guarded.
 *)     

    Lemma GeqPerm1_GeqPerm: subrelation GeqPerm1 GeqPerm.
    Proof.
      intros g1 g2 Hyp.
      apply (GeqPerm_coind (R:= GeqPerm1)) ; try assumption.
      clear g1 g2 Hyp ; intros _ _ [g1 g2 R H2 H3 H4].
      split; [assumption | apply (IlistPerm3_mon H2 H4)].
    Qed.

    Lemma GeqPerm_GeqPerm1: subrelation GeqPerm GeqPerm1.
    Proof.
      cofix Hc.
      intros g1 g2 Hyp.
      destruct (GeqPerm_out Hyp) as [H1 H2].
      apply (GeqPerm1_intro _ _ Hc); assumption.
    Qed.

(* now a precise analysis of TeqPermn which is the nth conjunct of TeqPerm_gene *)
    Definition TeqPermn (n:nat)(g1 g2: Graph T): Prop := TeqPerm (Graph2TreeG n g1) (Graph2TreeG n g2).

    Lemma TeqPermn_refl (Rrefl : Reflexive RelT)(n:nat) : Reflexive (TeqPermn n).
    Proof.  
      intro g ; apply (TeqPerm_refl Rrefl).
    Qed.

    Lemma TeqPermn_sym (Rsym : Symmetric RelT)(n:nat) : Symmetric (TeqPermn n).
    Proof.  
      intros g1 g2 H ; apply (TeqPerm_sym Rsym), H.
    Qed.

    Lemma TeqPermn_trans (Rtrans : Transitive RelT)(n: nat) : Transitive (TeqPermn n).
    Proof.  
      intros g1 g2 g3 H1 H2 ; apply (TeqPerm_trans Rtrans H1 H2).
    Qed.

   Add Parametric Relation (Req: Equivalence RelT) (n:nat) : (Graph T) (TeqPermn n)
      reflexivity proved by (TeqPermn_refl _ n)
      symmetry proved by (TeqPermn_sym _ (n:= n))
      transitivity proved by (TeqPermn_trans _ (n:=n))
    as TeqPermnRel.

   Lemma TeqPermn_0 (g1 g2: Graph T):
      RelT (label g1) (label g2) <-> TeqPermn 0 g1 g2.
   Proof.
     split; intro Hyp.
     red.
     do 2 rewrite Graph2TreeG_ok0.
     apply TeqPerm_intro.
     assumption.
     apply IlistPerm3nil.
(* other direction *)
     inversion_clear Hyp as [g3 g4 H1 _].
     do 2 rewrite Graph2TreeG_ok0 in H1.
     assumption.     
   Qed.

   Lemma TeqPermn_Sn (n:nat)(g1 g2: Graph T): 
     RelT (label g1) (label g2) -> IlistPerm3 (TeqPermn n) (sons g1) (sons g2)
     -> TeqPermn (S n) g1 g2.
   Proof.
     intros HypL HypS.
     red.
     do 2 rewrite Graph2TreeG_okS.
     apply TeqPerm_intro.
     assumption.
     apply IlistPerm3_imap_bis.
     assumption.
   Qed.

   Lemma TeqPermn_Sn_back (n:nat)(g1 g2: Graph T): TeqPermn (S n) g1 g2 ->
     RelT (label g1) (label g2) /\ IlistPerm3 (TeqPermn n) (sons g1) (sons g2).
   Proof.
     intro Hyp ; red in Hyp.
     do 2 rewrite Graph2TreeG_okS in Hyp.
     inversion_clear Hyp as [g3 g4 H1 H2].
     simpl in *|-*.
     split.
     assumption.
     apply (IlistPerm3_imap_back(f1:=Graph2TreeG n)(f2:=Graph2TreeG n)).
     assumption.
   Qed.

(* Note that the last three lemmas characterize TeqPermn for all n. In other
   words, this could have been an alternative definition by recursion on n. *)

   Lemma TeqPermn_Sn_n (g1 g2 : Graph T)(n: nat): 
      TeqPermn (S n) g1 g2  -> TeqPermn n g1 g2.
    Proof.
      revert g1 g2 ; induction n as [|n IHn] ; intros g1 g2 H1 ; 
      destruct (TeqPermn_Sn_back H1) as [H2 H3].
      apply TeqPermn_0.
      assumption.
      apply TeqPermn_Sn.
      assumption.
      apply (IlistPerm3_mon IHn H3).
    Qed.




(* Lemma TeqPerm_Graph2TreeG_n_Sn can be generalized to arbitrary differences: *)
   Lemma TeqPermn_antitone (g1 g2: Graph T)(m n: nat)(Hyp: m <= n):
     TeqPermn n g1 g2 -> TeqPermn m g1 g2.
   Proof. 
     induction Hyp as [| n H1 IH]; intro H2.
     assumption.
     apply IH.
     apply TeqPermn_Sn_n, H2.
   Qed.

   Lemma TeqPermn_dec (Req: Equivalence RelT)(Rdec : forall t1 t2, {RelT t1 t2}+{not (RelT t1 t2)}): 
     forall g1 g2 n, {TeqPermn n g1 g2}+{not (TeqPermn n g1 g2)}.
   Proof.
     intros g1 g2 n ; revert g1 g2 ; induction n as [|n IH] ; intros g1 g2 ;
     elim (Rdec (label g1) (label g2)); intros H1.
     left.
     apply TeqPermn_0.
     assumption.
     right.
     intros H2.
     contradiction H1.
     apply TeqPermn_0, H2.

     elim (IlistPerm3_dec _ IH (sons g1) (sons g2)) ; intros H2.
     left.
     apply TeqPermn_Sn; assumption.
     right.
     intros H3.
     destruct (TeqPermn_Sn_back H3) as [_ H4].
     contradiction H2.

     right.
     intros H2.
     destruct (TeqPermn_Sn_back H2) as [H3 _].
     contradiction H3.
   Qed.

    (* The definition that should be equivalent to GeqPerm *)
    Definition TeqPerm_gene (g1 g2: Graph T): Prop := forall n, TeqPermn n g1 g2.

(* now, this is just the intersection of equivalence relations,
   but we prove it by hand *)
    Lemma TeqPerm_gene_refl (Rrefl : Reflexive RelT): Reflexive TeqPerm_gene.
    Proof.  
      intros g n.
      apply (TeqPermn_refl Rrefl).
    Qed.

    Lemma TeqPerm_gene_sym (Rsym : Symmetric RelT): Symmetric TeqPerm_gene.
    Proof.  
      intros g1 g2 H n.
      apply (TeqPerm_sym Rsym (H n)).
    Qed.

    Lemma TeqPerm_gene_trans (Rtrans : Transitive RelT): Transitive TeqPerm_gene.
    Proof.  
      intros g1 g2 g3 H1 H2 n.
      apply (TeqPerm_trans Rtrans (H1 n) (H2 n)).
    Qed.

    Add Parametric Relation (Req: Equivalence RelT): (Graph T) TeqPerm_gene
      reflexivity proved by (TeqPerm_gene_refl _)
      symmetry proved by (TeqPerm_gene_sym _)
      transitivity proved by (TeqPerm_gene_trans _)
    as TeqPerm_geneRel.

    (* The first part of the equivalence : the easy one : ok ! *)
    (* a modular proof *)
    Lemma GeqPerm0_TeqPerm: subrelation GeqPerm0 TeqPerm_gene.
    Proof.
      intros g1 g2 H n.
      revert g1 g2 H.
      induction n as [|n IH] ; intros _ _ [g1 g2 H1 H2].
      apply TeqPermn_0, H1.
      apply TeqPermn_Sn.
      apply H1.
      apply (IlistPerm3_mon IH), H2.
    Qed.

(* we even have the slightly stronger statement with GeqPerm in place of GeqPerm0 *)
    Lemma GeqPerm_TeqPerm: subrelation GeqPerm TeqPerm_gene.
    Proof.
      intros g1 g2 H n ; revert g1 g2 H.
      induction n as [|n IH] ; intros [lab1 sons1] [lab2 sons2] H;
      apply GeqPerm_out in H; destruct H as [H1 H2]; apply TeqPerm_intro ; try assumption.
      simpl ; apply IlistPerm3nil.
      do 2 rewrite Graph2TreeG_okS.
      apply (IlistPerm3_mon IH) in H2.
      apply IlistPerm3_imap_bis.
      assumption.
    Qed.

    Lemma GeqPerm1_TeqPerm: subrelation GeqPerm1 TeqPerm_gene.
    Proof.
      intros g1 g2 H n ; revert g1 g2 H.
      induction n as [|n IH] ; intros [lab1 sons1] [lab2 sons2] H ;
      inversion H as [g1' g2' X S H1 H2 H4 H5] ; clear g1' g2' H4 H5 ; apply TeqPerm_intro ; 
      try assumption.
      simpl ; apply IlistPerm3nil.
      do 2 rewrite Graph2TreeG_okS.
      apply (IlistPerm3_mon S), (IlistPerm3_mon IH) in H2.
      apply IlistPerm3_imap_bis.
      assumption.
    Qed.

(* we describe a particular instance of the infinite pigeonhole principle *)
Definition IPPIlistPerm3Cert: Prop := forall(m: nat)(P: nat -> IlistPerm3Cert_list m -> Prop),
  (forall n: nat, exists f: IlistPerm3Cert_list m, P n f)
  -> exists f0: IlistPerm3Cert_list m, forall n:nat, exists n':nat, n' >= n /\ P n' f0.

(* this is a classical principle and obviously uses that IlistPerm3Cert_list m is finite;
   the detailed justification is found in the file IPPJustification.v *)
 
(* The crucial step to prove TeqPerm_GeqPerm *)

Lemma TeqPerm_gene_IlistPerm3: IPPIlistPerm3Cert ->  forall(g1 g2 : Graph T),
      TeqPerm_gene g1 g2 -> IlistPerm3 TeqPerm_gene (sons g1) (sons g2).
    Proof.
      intros IPP g1 g2 H.
      assert (Hyp: lgti (sons g1) = lgti (sons g2)).
      destruct (TeqPermn_Sn_back (H 1)) as [_ H1].
      apply (IlistPerm3_lgti H1).
      assert (H0: forall n:nat, exists f: IlistPerm3Cert_list(lgti (sons g1)), 
        IlistPerm3Cert (TeqPermn n) (sons g1) (sons g2) Hyp f).
      intro n.
      apply IlistPerm3_IlistPerm3Cert.
      destruct (TeqPermn_Sn_back (H (S n))) as [_ Hn].
      assumption.
      destruct (IPP _ _ H0) as [f0 f0good].
      apply (IlistPerm3Cert_IlistPerm3 (Hyp:= Hyp)(f:= f0)).
      apply IlistPerm3Cert_inter.
      intro i.
      destruct (f0good i) as [i' [i'bigger i'good]].
      apply (@IlistPerm3Cert_mon _ (TeqPermn i')) ; try assumption.
      intros g1' g2' H1.
      apply (TeqPermn_antitone i'bigger H1).
    Qed.

    Lemma TeqPerm_GeqPerm: IPPIlistPerm3Cert -> subrelation TeqPerm_gene GeqPerm.
    Proof.
      intros IPP g1 g2 Hyp.
      apply (GeqPerm_coind (R:=TeqPerm_gene)); try assumption.
      clear g1 g2 Hyp ; intros g1 g2 H.
      split.
      apply TeqPermn_0, (H 0).
      apply (TeqPerm_gene_IlistPerm3 IPP H).
    Qed.

    Lemma TeqPerm_GeqPerm1: IPPIlistPerm3Cert -> subrelation TeqPerm_gene GeqPerm1.
    Proof.
      intro IPP.
      cofix Hc ; intros g1 g2 H.
      apply (GeqPerm1_intro _ _ Hc).
      set (H0 := H 0) ; inversion H0 as [g1' g2' H1 H2 H3 H4] ; clear g1' g2' H2 H3 H4.
      do 2 rewrite Graph2TreeG_ok0 in H1 ; assumption.
      apply (TeqPerm_gene_IlistPerm3 IPP H).
    Qed.

    Lemma GeqPerm_refl_indirect (IPP: IPPIlistPerm3Cert)(Rrefl : Reflexive RelT): forall g, GeqPerm g g.
    Proof.
      intro g ; apply (TeqPerm_GeqPerm IPP), (TeqPerm_gene_refl Rrefl).
    Qed.

(* a direct proof that does not pass through TeqPerm_gene *)
    Lemma GeqPerm_refl  (Rrefl : Reflexive RelT): forall g, GeqPerm g g.
    Proof.
      intros g.
      apply (GeqPerm_coind (R:= @eq (Graph T))); try assumption ; split; rewrite H.
      reflexivity.
      apply IlistPerm3_refl, eq_equivalence.
    Qed.

    Lemma GeqPerm1_refl(Rrefl : Reflexive RelT): forall g, GeqPerm1 g g.
    Proof.
      assert (Gen: forall g1 g2 : Graph T, g1 = g2 -> GeqPerm1 g1 g2).
      cofix Hc ; intros g1 g2 Hyp ; apply (GeqPerm1_intro _ _ Hc) ; rewrite Hyp ; try reflexivity.
      apply IlistPerm3_refl, eq_equivalence.
      intro g ; apply Gen ; reflexivity.
    Qed.

    Lemma GeqPerm_sym_indirect (IPP: IPPIlistPerm3Cert)(Rsym : Symmetric RelT): 
      forall g1 g2, GeqPerm g1 g2 -> GeqPerm g2 g1.
    Proof.
      intros g1 g2 H; apply (TeqPerm_GeqPerm IPP), (TeqPerm_gene_sym Rsym (GeqPerm_TeqPerm H)).
    Qed.

    (* a direct proof that does not pass through TeqPerm_gene *)
    Lemma GeqPerm_sym (Rsym : Symmetric RelT) : forall g1 g2, GeqPerm g1 g2 -> GeqPerm g2 g1.
    Proof.
      intros g1 g2 H ;apply (GeqPerm_coind (R:= fun g1 g2 => GeqPerm g2 g1)) ; try assumption.
      clear g1 g2 H ; intros g1 g2 H ; destruct (GeqPerm_out H) as [H1 H2].
      split.
      symmetry ; assumption.
      apply (IlistPerm3_flip H2).
    Qed.

    Lemma GeqPerm1_sym (Rsym : Symmetric RelT) : forall g1 g2, GeqPerm1 g1 g2 -> GeqPerm1 g2 g1.
    Proof.
      cofix Hc ; intros g1 g2 H.
      apply (GeqPerm1_intro _ _ (X:= fun g1 g2 => GeqPerm1 g2 g1)) ; destruct H as [g1 g2 X S H1 H2].
      clear g1 g2 X S H1 H2 ; intros g1 g2 H.
      apply (Hc _ _ H).
      apply (Rsym _ _ H1).
      apply (IlistPerm3_flip (IlistPerm3_mon S H2)).
    Qed.

    Lemma GeqPerm_trans_indirect (IPP: IPPIlistPerm3Cert)(Rtrans: Transitive RelT): 
      forall g1 g2 g3, GeqPerm g1 g2 -> GeqPerm g2 g3 -> GeqPerm g1 g3.
    Proof.
      intros g1 g2 g3 H1 H2.
      apply (TeqPerm_GeqPerm IPP), (TeqPerm_gene_trans _ (GeqPerm_TeqPerm H1) (GeqPerm_TeqPerm H2)).
    Qed.

    Lemma GeqPerm_trans (Rtrans: Transitive RelT): 
      forall g1 g2 g3, GeqPerm g1 g2 -> GeqPerm g2 g3 -> GeqPerm g1 g3.
    Proof.
      intros g1 g2 g3 H1 H2.
      apply (GeqPerm_coind (R:= fun g1 g3 => exists g2, GeqPerm g1 g2 /\ GeqPerm g2 g3)).
      clear g1 g2 g3 H1 H2 ; intros g1 g3 [g2 [Hyp1 Hyp2]].
      destruct (GeqPerm_out Hyp1) as [Hyp11 Hyp12] ; destruct (GeqPerm_out Hyp2) as [Hyp21 Hyp22].
      split.
      transitivity (label g2); assumption.
      apply (IlistPerm3_trans_special Hyp12 Hyp22).
      exists g2 ; split; assumption.
    Qed.

    Lemma GeqPerm1_trans (Rtrans: Transitive RelT) : 
      forall g1 g2 g3, GeqPerm1 g1 g2 -> GeqPerm1 g2 g3 -> GeqPerm1 g1 g3.
    Proof.
      cofix Hc ; intros g1 g2 g3 H1 H2.
      apply (GeqPerm1_intro _ _  (X:= fun g1 g3 => exists g2, GeqPerm1 g1 g2 /\ GeqPerm1 g2 g3)) ; 
      destruct H1 as [g1' g2' X1 S1 H1' H1] ;destruct H2 as [g2'' g3' X2 S2 H2' H2].
      clear g1' X1 S1 H1' g2'' g3' X2 S2 H2' H1 H2 ; intros g1 g3 [g2 [H1 H2]] ; exact (Hc _ _ _ H1 H2).
      transitivity (label g2''); assumption.
      apply (IlistPerm3_trans_special (i2:= sons g2'')) ;
      [apply (IlistPerm3_mon S1 H1) | apply (IlistPerm3_mon S2 H2)].
    Qed.

    (* Recording that GeqPerm preserves equivalence *)
    Add Parametric Relation (Req: Equivalence RelT): (Graph T) (GeqPerm)
      reflexivity proved by (GeqPerm_refl _)
      symmetry proved by (GeqPerm_sym _)
      transitivity proved by (GeqPerm_trans _)
      as GeqPermRel.

End GeqPerm.

  Section GinGP.
    Definition Graph_in_Graph_Perm (T: Set) (RelT : relation T):= Graph_in_Graph_Gene (GeqPerm RelT).    

    Lemma GinGP_sons (T: Set)(RelT: relation T): 
      forall g1 g2: Graph T, Graph_in_Graph_Perm RelT g1 g2 -> 
      forall i, Graph_in_Graph_Perm RelT (fcti (sons g1) i) g2.
    Proof.
      intros g1 g2 H1 i.
      induction H1 as [g2 H1 | g2 i' H1 IH].
      destruct (GeqPerm_out H1) as [H2 H3].
      destruct (IlistPerm3_exists_rec H3 i) as [i' [H4 _]].
      apply (is_Graph_in_Graph_Gene_indir _ i').
      apply (is_Graph_in_Graph_Gene_dir _ _ _ H4).
      
      apply (is_Graph_in_Graph_Gene_indir _ i' IH).
    Qed.

    Lemma Graph_in_Graph_Perm_trans (T: Set)(RelT: relation T)(Rtrans: Transitive RelT): 
      forall g1 g2 g3: Graph T, 
      Graph_in_Graph_Perm RelT g1 g2 -> Graph_in_Graph_Perm RelT g2 g3 -> Graph_in_Graph_Perm RelT g1 g3.
    Proof.
      intros g1 g2 g3 H1 H2.
      revert H2.
      induction H1 as [g2 H1 | g2 i H1 IH1] ; intros H2.
      induction H2 as [g3 H2 | g3 i' H2 IH2].

      apply (is_Graph_in_Graph_Gene_dir ).
      apply (GeqPerm_trans _ H1 H2).
      apply (is_Graph_in_Graph_Gene_indir _ i' IH2).

      apply IH1, GinGP_sons, H2.
    Qed.

    Add Parametric Morphism (T: Set)(RelT: relation T)(Rtrans: Transitive RelT)(g: Graph T) : 
      (Graph_in_Graph_Perm RelT g) with signature (GeqPerm RelT) ==> (impl)
    as Graph_in_Graph_PermPM.
    Proof.
      intros g1 g2 Heq H.
      revert g2 Heq.
      induction H as [g1 H1 | g1 i H1 IH]; intros g2 H2.
      apply is_Graph_in_Graph_Gene_dir.
      apply (GeqPerm_trans _ H1 H2).
      apply GeqPerm_out in H2.
      destruct H2 as [H2 H3].
      apply IlistPerm3_IlistPerm4_eq in H3.
      inversion H3 as [l1 l2 H4 H5 H6 H7] ; clear l1 l2 H6 H7.
      destruct (H5 i) as [i2 [H6 H7]].
      apply (is_Graph_in_Graph_Gene_indir _ i2).
      apply IH.
      assumption.
    Qed.

    Add Parametric Morphism (T: Set)(RelT: relation T)(Req: Equivalence RelT)(g: Graph T) : 
      (fun x => Graph_in_Graph_Perm RelT x g) with signature (GeqPerm RelT) ==> (impl)
    as Graph_in_Graph_PermM2.
    Proof.
      intros g1 g2 Heq H.
      revert g2 Heq.
      induction H as [g H1 | g i H1 IH]; intros g2 H2.
      apply (is_Graph_in_Graph_Gene_dir _ _ _ (GeqPerm_trans _ (GeqPerm_sym _ H2) H1)).
      apply (is_Graph_in_Graph_Gene_indir g i (IH _ H2)).
    Qed.

End GinGP.

Section GPPerm.
  
  Inductive GPPerm (T: Set)(RelT : relation T)(g1 g2: Graph T): Prop := 
    GPPerm_intro : Graph_in_Graph_Perm RelT g1 g2 -> Graph_in_Graph_Perm RelT g2 g1 -> GPPerm RelT g1 g2.

  Lemma GPPerm_refl (T: Set)(RelT : relation T)(Rrefl: Reflexive RelT)(g: Graph T): GPPerm RelT g g.
  Proof.
    apply GPPerm_intro ; apply is_Graph_in_Graph_Gene_dir, GeqPerm_refl; assumption.
  Qed.

  Lemma GPPerm_sym  (T: Set)(RelT : relation T): 
    forall(g1 g2: Graph T), GPPerm RelT g1 g2 -> GPPerm RelT g2 g1.
  Proof.
    intros g1 g2 [h1 h2].
    apply GPPerm_intro ; assumption.
  Qed.

  Lemma GPPerm_trans (T: Set)(RelT : relation T)(Rtrans: Transitive RelT): forall (g1 g2 g3: Graph T), 
    GPPerm RelT g1 g2 -> GPPerm RelT g2 g3 -> GPPerm RelT g1 g3.
  Proof.
    intros g1 g2 g3 [h1 h1'] [h2 h2'].
    apply GPPerm_intro.
    apply (Graph_in_Graph_Perm_trans _ h1 h2).
    apply (Graph_in_Graph_Perm_trans _ h2' h1').
  Qed.

  Add Parametric Relation(T: Set)(RelT : relation T)(Req: Equivalence RelT): (Graph T) (GPPerm RelT)
    reflexivity proved by (GPPerm_refl _)
    symmetry proved by (@GPPerm_sym _ RelT)
    transitivity proved by (GPPerm_trans _)
  as GPPermRel.

End GPPerm.

Section Example_GPPerm.

CoFixpoint G01 : Graph nat := let g1 := mk_Graph 1 (singleton G01) in mk_Graph 0 (singleton g1).
CoFixpoint G10 : Graph nat := let g0 := mk_Graph 0 (singleton G10) in mk_Graph 1 (singleton g0).

Lemma GPPerm_G01_G10 : GPPerm eq G01 G10.
Proof.
  apply GPPerm_intro.
  apply (is_Graph_in_Graph_Gene_indir _ (first _: Fin (lgti (sons G10)))).
  apply is_Graph_in_Graph_Gene_dir.
  apply GeqPerm0_GeqPerm.
  cofix Hc.
  apply GeqPerm0_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (first _: Fin (lgti (singleton (mk_Graph 1 (singleton G01))))) 
    (first _ : Fin (lgti (singleton G10)))).
  apply GeqPerm0_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (first _: Fin (lgti (singleton G01))) 
    (first _ : Fin (lgti (singleton (mk_Graph 0 (singleton G10)))))).
  assumption.
  simpl ; apply IlistPerm3nil.
  simpl ; apply IlistPerm3nil.

  apply (is_Graph_in_Graph_Gene_indir _ (first _: Fin (lgti (sons G01)))).
  apply is_Graph_in_Graph_Gene_dir.
  apply GeqPerm0_GeqPerm.
  cofix Hc.
  apply GeqPerm0_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (first _: Fin (lgti (singleton (mk_Graph 0 (singleton G10))))) 
    (first _ : Fin (lgti (singleton G01)))).
  apply GeqPerm0_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (first _: Fin (lgti (singleton G10))) 
    (first _ : Fin (lgti (singleton (mk_Graph 1 (singleton G01)))))).
  assumption.
  simpl ; apply IlistPerm3nil.
  simpl ; apply IlistPerm3nil.
Qed.

CoFixpoint G01' : Graph nat := mk_Graph 0 (singleton G10')
with G10' : Graph nat := mk_Graph 1 (singleton G01').

Lemma GPPerm_G01'_G10' : GPPerm eq G01' G10'.
Proof.
  apply GPPerm_intro.
  apply (is_Graph_in_Graph_Gene_indir _ (first _: Fin (lgti (sons G10')))).
  apply (Graph_in_Graph_Gene_refl (GeqPerm_refl _)).

  apply (is_Graph_in_Graph_Gene_indir _ (first _: Fin (lgti (sons G01')))).
  apply (Graph_in_Graph_Gene_refl (GeqPerm_refl _)).
Qed.

Lemma Geq_G01_G01' : Geq eq G01 G01'.
Proof.
  cofix Hc.
  apply Geq_intro.
  reflexivity.
  
  apply (is_ilist_rel _ _ _ (refl_equal _ : lgti (sons G01) = lgti (sons G01'))).
  intro i.
  apply Geq_intro.
  reflexivity.
  apply (is_ilist_rel _ _ _ (refl_equal _ : lgti (singleton G01) = lgti (singleton G01'))).
  intro i'.
  apply Hc.
Qed.

Lemma Geq_G10_G10' : Geq eq G10 G10'.
Proof.
  cofix Hc.
  apply Geq_intro.
  reflexivity.
  
  apply (is_ilist_rel _ _ _ (refl_equal _ : lgti (sons G10) = lgti (sons G10'))).
  intro i.
  apply Geq_intro.
  reflexivity.
  apply (is_ilist_rel _ _ _ (refl_equal _ : lgti (singleton G10) = lgti (singleton G10'))).
  intro i'.
  apply Hc.
Qed.

Definition g1 : Graph nat := mk_Graph 3 (icons (mk_Graph 2 (@inil _)) (singleton G01)).

Definition g2 : Graph nat := mk_Graph 3 (icons G01 (singleton (mk_Graph 2 (@inil _)))).

Lemma GPPerm_g1_g2 : GPPerm eq g1 g2.
Proof.
  apply GPPerm_intro.
  apply is_Graph_in_Graph_Gene_dir.
  apply GeqPerm_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (first _: Fin (lgti (sons g1))) (succ (first _) : Fin (lgti (sons g2)))).
  apply (GeqPerm_refl _).
  apply (IlistPerm3_cons _ _ (first _: Fin (lgti (extroduce (sons g1) (first (lgti (singleton G01)))))) 
    (first _ : Fin (lgti (extroduce (sons g2) (succ (first 0)))))).
  apply GeqPerm_intro.
  reflexivity.
  apply (IlistPerm3_refl (GeqPermRel _)).
  simpl ; apply IlistPerm3nil.

  apply is_Graph_in_Graph_Gene_dir.
  apply GeqPerm_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (succ (first _) : Fin (lgti (sons g2)))(first _: Fin (lgti (sons g1))) ).
  apply (GeqPerm_refl _).
  apply (IlistPerm3_cons _ _  (first _ : Fin (lgti (extroduce (sons g2) (succ (first 0)))))
    (first _: Fin (lgti (extroduce (sons g1) (first (lgti (singleton G01))))))).
  apply GeqPerm_intro.
  reflexivity.
  apply (IlistPerm3_refl (GeqPermRel _)).
  simpl ; apply IlistPerm3nil.
Qed.

Definition g012 : Graph nat := 
  mk_Graph 0 (icons (mk_Graph 1 (@inil _)) (singleton (mk_Graph 2 (@inil _)))).

Definition g021 : Graph nat := 
  mk_Graph 0 (icons (mk_Graph 2 (@inil _)) (singleton (mk_Graph 1 (@inil _)))).

Lemma GPPerm_g012_g021 : GPPerm eq g012 g021.
Proof.
  assert (H : GeqPerm eq g012 g021).
  apply GeqPerm_intro.
  reflexivity.
  apply (IlistPerm3_cons _ _ (first _ : Fin (lgti (sons g012))) 
    (succ (first _) : Fin (lgti (sons g021))) (GeqPerm_refl _ _)).
  apply (IlistPerm3_cons _ _ (first _ : Fin (lgti (extroduce (sons g012)
     (first (lgti (singleton _)))))) (first _ : Fin (lgti (extroduce (sons g021) (succ (first 0)))))
     (GeqPerm_refl _ _)).
  apply IlistPerm3_nil ; reflexivity.

  apply GPPerm_intro ; 
  apply is_Graph_in_Graph_Gene_dir.
  assumption.
  apply (GeqPerm_sym _ H).
Qed.

Definition g3 : Graph nat := mk_Graph 2 (singleton G10).
Definition g4 : Graph nat := mk_Graph 2 (singleton G01).

Definition node_in (T: Set)(R: relation T)(t: T)(g : Graph T) :=
  exists g', Graph_in_Graph_Perm R g' g /\ R t (label g').

Lemma node_not_in_not_eq (T: Set)(R: relation T)(Rrefl: Reflexive R)(g g' : Graph T) : 
  not (node_in R (label g') g) -> not (GPPerm R g' g).
Proof.
  intros H1 [H2 _].
  apply H1.
  unfold node_in.
  exists g'.
  split.
  assumption.
  reflexivity.
Qed.

Lemma not_GPPerm_g3_g4 : not (GPPerm eq g3 g4).
Proof.
  intros [[H1|i H1] _].
  destruct (GeqPerm_out H1) as [_ [_ e2 | i1 i2 H3 _]].
  inversion e2.
  destruct (GeqPerm_out H3) as [H5 _].
  inversion H5.

  revert H1.
  fix Hr 1.
  intros [H| i'' [H |i''' H]].
  destruct (GeqPerm_out H) as [H' _].
  inversion H'.
  destruct (GeqPerm_out H) as [H' _].
  inversion H'.
  apply (Hr H).
Qed.
End Example_GPPerm.
