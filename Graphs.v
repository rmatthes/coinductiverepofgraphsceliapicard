(** Graphs.v Version 1.5 February 2012 *)
(** runs under V8.3, tested with 8.3pl2 *)

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
Require Import Morphisms.
Require Import Basics.
Require Import Tools.
Require Import ListEq.

Set Implicit Arguments.

Section Graphs_def_tools. 

  Variable T: Set.
  (* Definition of coinductive graphs *)
  CoInductive Graph: Set :=
  mk_Graph: T -> (ilist Graph) -> Graph.

  Section Graphs_def_tools.  
    (* Basic functions on graphs *)
    Definition label (g:Graph): T := let (t,_) := g in t.
    Definition sons (g:Graph): ilist Graph := let (_,lg) := g in lg.
  
    (* Some proofs to show the consistency of these definitions *)
    Lemma label_sons_OK: forall g: Graph, g = mk_Graph (label g) (sons g).
    Proof.
      intro.
      destruct g.
      reflexivity.
    Qed.

  End Graphs_def_tools.

  Section Geq_def_tools.
    Variable RelT : relation T.

    (* Definition of a relation transformer on Graph *)
    CoInductive Geq: Graph->Graph->Prop :=
      Geq_intro: forall g1 g2,
        RelT (label g1) (label g2) -> ilist_rel Geq (sons g1) (sons g2) -> Geq g1 g2.

    (* Proof that Geq preserves equivalence *)
    Lemma Geq_refl (Rrefl: Reflexive RelT): forall g: Graph, Geq g g.
    Proof.
      cofix.
      intros [lab l].
      apply Geq_intro.
      reflexivity.
      apply (is_ilist_rel Geq l l (refl_equal _)).
      intro i.
      apply Geq_refl.
    Qed.

    Lemma Geq_trans (Rtrans: Transitive RelT): 
      forall g1 g2 g3, Geq g1 g2 -> Geq g2 g3 -> Geq g1 g3.
    Proof.
      cofix.
      intros _ _ g3 [[t1 l1] g2 e1 [e1' h1]] h2 ; 
        destruct h2 as [[t2 l2] [t3 l3] e2 [e2' h2]].
      apply Geq_intro.
      apply (Rtrans _ t2) ; assumption.
      simpl in *|-*.
      apply (is_ilist_rel Geq _ _ (trans_eq e1' e2')).
      
      intro i.
      assert (h3 : rewriteFins (eq_trans e1' e2') i =  
        rewriteFins e2' (rewriteFins e1' i)) by treatFinPure.
      rewrite h3; clear h3.
      apply (Geq_trans _ _ _ (h1 i) (h2 (rewriteFins e1' i))).
    Qed.

    Lemma Geq_sym (Rsym: Symmetric RelT): 
      forall g1 g2: Graph, Geq g1 g2 -> Geq g2 g1.
    Proof.
      cofix.
      intros _ _ [[t1 l1] [t2 l2] e1 [e2 h1]].
      apply Geq_intro ; simpl in *|-*.
      apply Rsym, e1.
      apply (is_ilist_rel _ _ _ (sym_eq e2)).
      intro i.
      assert (h2 := h1 (rewriteFins (eq_sym e2) i)).
      assert (h3 : rewriteFins e2 (rewriteFins (eq_sym e2) i) = i) by treatFinPure.
      rewrite h3 in h2.
      apply (Geq_sym _ _ h2).
    Qed.
    
    (* Recording that Geq preserves equivalence *)
    Add Parametric Relation (Req: Equivalence RelT): (Graph) (Geq)
      reflexivity proved by (Geq_refl _)
      symmetry proved by (Geq_sym _)
      transitivity proved by (Geq_trans _)
      as GeqRel.

  End Geq_def_tools. 

  Let LeqGeqRel (RelT: relation T)(Req: Equivalence RelT):= ilist_relRel (GeqRel Req).

  (* Definition of the etaExpand necessary for coinduction *)
  Section etaExpand_def_tools. 
    Definition etaExpandG (g: Graph) := 
      match g with 
        mk_Graph t lg => mk_Graph t lg
      end.

    Lemma etaExpandG_Identity : forall g: Graph, etaExpandG g = g.
    Proof.
      intro.
      destruct g.
      reflexivity.
    Qed.

  End etaExpand_def_tools. 

  Section applyF2G_def_tools. 
    (* Function that applies a function f to all the labels of a graph *)
    CoFixpoint applyF2G(f: T -> T)(g:Graph):Graph := 
      let (t,lg) := g in mk_Graph (f t) (imap (applyF2G f) lg).

  End applyF2G_def_tools.

  Section wf_def_tools.

  (* Definition of the notion of well-formedness for A and B *)
  CoInductive wfG: Graph->Prop :=
    is_wfG: forall g, (iall wfG (sons g)) -> wfG g.

  (* Theorem showing the consistency of this definition *)
  Theorem wfG_applyF2G: forall (g :Graph) (f: T -> T), 
    wfG g -> wfG (applyF2G f g).
  Proof.
    cofix.
    destruct g; intros f h.
    inversion_clear h as (a, H).
    simpl in H.
    apply is_wfG; simpl.
    inversion_clear i as (n', iln).
    unfold iall; simpl; intro fi.
    apply (wfG_applyF2G _ _ (H fi)).
  Qed.
  End wf_def_tools.

  Section Graph_in_Graph.
    (* Definition of a relation saying if a graph  is "included" 
       in another graph modulo Geq *)
    (* It can be included at first level, or deeper *)
    Inductive Graph_in_Graph (RelT: relation T)(gin g: Graph): Prop :=
      is_Graph_in_Graph_dir: forall f: Fin (lgti (sons g)), 
        Geq RelT gin (fcti (sons g) f) -> Graph_in_Graph RelT gin g
     | is_Graph_in_Graph_indir: forall f: Fin (lgti (sons g)), 
        Graph_in_Graph RelT gin (fcti (sons g) f) -> Graph_in_Graph RelT gin g.

    Add Parametric Morphism (RelT: relation T)(R_trans: Transitive RelT)(g: Graph) : 
      (Graph_in_Graph RelT g) with signature (Geq RelT) ==> (impl)
    as Graph_in_GraphM.
    Proof.
      intros g1 g2 Heq H.
      revert g2 Heq.
      induction H as [g1 f H | g1 f H IH]; intros y Heq ;
      destruct Heq as [g1 g2 e1 [e2 Heq]].
      apply (is_Graph_in_Graph_dir g2 (rewriteFins e2 f) (Geq_trans _ H (Heq f))).
      apply (is_Graph_in_Graph_indir g2 (rewriteFins e2 f) (IH _ (Heq f))).
    Qed.

    Add Parametric Morphism (RelT: relation T)(Req: Equivalence RelT)(g: Graph) : 
      (fun x => Graph_in_Graph RelT x g) with signature (Geq RelT) ==> (impl)
    as Graph_in_GraphM2.
    Proof.
      intros g1 g2 Heq H.
      revert g2 Heq.
      induction H as [g f H | g f H IH]; intros g2 Heq.
      apply (is_Graph_in_Graph_dir g f (Geq_trans _ (Geq_sym _ Heq) H)).
      apply (is_Graph_in_Graph_indir g f (IH _ Heq)).
    Qed.

    (* Lemma to validate the definitions *)
    Lemma sons_in_Graph (RelT: relation T)(R_refl: Reflexive RelT): forall g: Graph, 
      (forall f: Fin (lgti (sons g)), Graph_in_Graph RelT (fcti (sons g) f) g).
    Proof.
      intros g f.
      apply (is_Graph_in_Graph_dir g f (Geq_refl _ _)).
    Qed.

    Lemma GinG_sons_in_Graph (RelT: relation T): forall g1 g2, 
      Graph_in_Graph RelT g1 g2 -> forall f, Graph_in_Graph RelT (fcti (sons g1) f) g2.
    Proof.
      intros g1 g2 H f.
      induction H as [g2 f' H | g2 f' H IH]; apply (is_Graph_in_Graph_indir g2 f').
      inversion_clear H as [x i _ [H2 H3]].
      apply (is_Graph_in_Graph_dir _ (rewriteFins H2 f) (H3 _)).
      apply IH.
    Qed.
      
    (* Proof of preservation of transitivity for Graph_in_Graph *)
    Lemma Graph_in_Graph_trans (RelT: relation T)(Req: Equivalence RelT): 
      forall g1 g2 g3: Graph, Graph_in_Graph RelT g1 g2 -> Graph_in_Graph RelT g2 g3 -> 
      Graph_in_Graph RelT g1 g3.
    Proof.
      intros g1 g2 g3 H1 H2.
      induction H1 as [g2 f H1 | g2 f H1 IH1].
      apply (Graph_in_GraphM2 _ (Geq_sym _ H1)).
      apply (GinG_sons_in_Graph H2).
      apply (IH1 (GinG_sons_in_Graph H2 f)).
    Qed.

  Section Graph_in_Graph_gene.
    (* Definition of a relation saying if a graph is "included" 
       in another graph *)
    (* It can be included at first level, or deeper *)
    Inductive Graph_in_Graph_Gene (GRel: relation Graph)(gin g: Graph): Prop :=
      is_Graph_in_Graph_Gene_dir: GRel gin g -> Graph_in_Graph_Gene GRel gin g
     | is_Graph_in_Graph_Gene_indir: forall i: Fin (lgti (sons g)), 
        Graph_in_Graph_Gene GRel gin (fcti (sons g) i) -> Graph_in_Graph_Gene GRel gin g.

    (* Lemma to validate the definitions *)

    Lemma sons_in_Graph_Gene_refl (GRel: relation Graph)(GRrefl: Reflexive GRel): 
      forall g: Graph, (forall i: Fin (lgti (sons g)), 
      Graph_in_Graph_Gene GRel (fcti (sons g) i) g).
    Proof.
      intros g i.
      apply (is_Graph_in_Graph_Gene_indir _ i).
      apply is_Graph_in_Graph_Gene_dir.
      reflexivity.
    Qed.

    Lemma Graph_in_Graph_Gene_refl (GRel: relation Graph)(GRrefl: Reflexive GRel)(g: Graph): 
      Graph_in_Graph_Gene GRel g g.
    Proof.
      apply is_Graph_in_Graph_Gene_dir.
      reflexivity.
    Qed.

  End Graph_in_Graph_gene.

  Section GinG'.
    Definition GinG'(R: relation T) := Graph_in_Graph_Gene (Geq R).
    
    Lemma GinG_GinG' (R: relation T)(g1 g2 : Graph ) : 
      Graph_in_Graph R g1 g2 -> GinG' R g1 g2.
    Proof.
      intros H ; induction H as [g2 i H1 |g2 i H1 IH].
      apply (is_Graph_in_Graph_Gene_indir _ i).
      apply (is_Graph_in_Graph_Gene_dir _ _ _ H1).
      apply (is_Graph_in_Graph_Gene_indir _ i).
      apply IH.
    Qed.
  
    Add Parametric Morphism(RelT: relation T)(R_trans: Transitive RelT)(g: Graph) : 
      (GinG' RelT g) with signature (Geq RelT) ==> (impl)
    as GinG'M.
    Proof.
      intros g1 g2 Heq H.
      revert g2 Heq.
      induction H as [g1 H | g1 f H IH]; intros y Heq.
      apply is_Graph_in_Graph_Gene_dir.
      apply (Geq_trans _ H Heq).
      destruct Heq as [g1 g2 e1 [e2 Heq]].
      apply (is_Graph_in_Graph_Gene_indir g2 (rewriteFins e2 f) (IH _ (Heq f))).
    Qed.

    Add Parametric Morphism (RelT: relation T)(Req: Equivalence RelT)(g: Graph) : 
      (fun x => GinG' RelT x g) with signature (Geq RelT) ==> (impl)
    as GinG'M2.
    Proof.
      intros g1 g2 Heq H.
      revert g2 Heq.
      induction H as [g H | g f H IH]; intros g2 Heq.
      apply (is_Graph_in_Graph_Gene_dir _ _ _ (Geq_trans _ (Geq_sym _ Heq) H)).
      apply (is_Graph_in_Graph_Gene_indir g f (IH _ Heq)).
    Qed.

    Lemma GinG'_sons_in_Graph (RelT: relation T): forall g1 g2, 
      GinG' RelT g1 g2 -> forall f, GinG' RelT (fcti (sons g1) f) g2.
    Proof.
      intros g1 g2 H i.
      induction H as [g2 H | g2 i' H IH].
      destruct H as [g1 g2 _ [H1 H2]].
      apply (is_Graph_in_Graph_Gene_indir _ (rewriteFins H1 i)), is_Graph_in_Graph_Gene_dir, H2.
      apply (is_Graph_in_Graph_Gene_indir _ i'), IH.
    Qed.
      
    Lemma GinG'_trans (R: relation T)(Req: Equivalence R)(g1 g2 g3: Graph ) : 
      GinG' R g1 g2 -> GinG' R g2 g3 -> GinG' R g1 g3.
    Proof.
      intros H1 H2.
      induction H1 as [g2 H1 |g2 i H1 IH].
      apply (GinG'M2 _ (Geq_sym _ H1)), H2.
      apply IH, GinG'_sons_in_Graph, H2.
    Qed.
    
  End GinG'.

  End Graph_in_Graph.

  Section Finite_def_tools.
    (* Correct coinductive definition of G_all *)
    CoInductive G_all (Pg:Graph->Prop): Graph->Prop :=
      is_Gall: forall g, Pg g -> iall (G_all Pg) (sons g) -> 
        G_all Pg g.

    Definition P_Finite(RelT: relation T)(lg: list Graph):= 
      fun x => exists y, In y lg /\ Geq RelT x y.

    (* Definition of G_finite indicating whether a graph is finite (possibly circular) *)
    Inductive G_finite (RelT: relation T)(g:Graph): Prop :=
      is_Gfinite: forall (lg:list Graph), 
      G_all (P_Finite RelT lg) g -> G_finite RelT g.

    Add Parametric Morphism (RelT: relation T): (sons)
      with signature (Geq RelT) ==> (ilist_rel (Geq RelT))
    as sonsM.
    Proof.
      intros.
      destruct H.
      assumption.
    Qed.

    Add Parametric Morphism (RelT: relation T): (label)
      with signature (Geq RelT) ==> (RelT)
    as labelM.
    Proof.
      intros.
      destruct H.
      assumption.
    Qed.

    Definition Geq_prop_morph (RelT: relation T)(Pg: Graph -> Prop) := 
      Proper (Geq RelT ==> impl) Pg.

    Add Parametric Morphism (RelT: relation T)(Req: Equivalence RelT)(lg: list Graph): 
      (P_Finite RelT lg) with signature (Geq RelT) ==> (impl)
    as P_FiniteM.
    Proof.
      intros g1 g2 H1 [g [H2 H3]].
      exists g.
      split.
      assumption.
      apply (Geq_trans _ (Geq_sym _ H1) H3).
    Qed.

    Lemma Geq_ilist_rel(RelT: relation T): forall g1 g2: Graph, Geq RelT g1 g2 -> 
      ilist_rel (Geq RelT) (sons g1) (sons g2).
    Proof.
      intros.
      destruct H.
      assumption.
    Qed.
      
    Lemma G_all_Geq_eq (RelT: relation T): forall (Pg: Graph -> Prop)
        (HypPg: Geq_prop_morph RelT Pg)(g1 g2: Graph), 
        Geq RelT g1 g2 -> ((G_all Pg g1) -> G_all Pg g2).
    Proof.
      intros Pg HypPg.
      cofix Hcb.
      intros g1 g2 H1 H2.
      destruct H2 as [g1 Hpb1 H2].
      unfold Geq_prop_morph in HypPg.
      apply is_Gall.
      rewrite <- H1.
      assumption.
      destruct H1 as [g1 g2 _ [H3 H4]].
      intro i.
      assert (H5 : i = (rewriteFins H3 (rewriteFins (sym_eq H3) i))) by treatFinPure.
      rewrite H5.
      apply (Hcb _ _ (H4 _) (H2 _)).
    Qed.

    (* Proof of the monotonicity of P_Finite *)
    Lemma P_Finite_monotone (RelT: relation T): forall (lg lg': list Graph)(g: Graph), 
      incl lg lg' -> P_Finite RelT lg g -> P_Finite RelT lg' g.
    Proof.
      intros lg lg' g H1 [g' [H2 H3]].
      exists g' ; split.
      apply (H1 g' H2).
      assumption.
    Qed.

    (* Proof of the monotonicity of G_all with P_Finite *)
    Lemma G_all_monotone: forall (P P':Graph -> Prop)(g: Graph),
      (forall g, P g -> P' g) -> G_all P g -> G_all P' g.
    Proof.
      intros P P' g H1 ; revert g ; cofix Hc ; intros _ [g H2 H3].
      apply is_Gall.
      apply H1, H2.
      intro i.
      apply (Hc _ (H3 i)).
    Qed.

    Lemma G_all_P_Finite_monotone (RelT: relation T): forall (lg lg':list Graph)(g: Graph),
      incl lg lg' -> G_all (P_Finite RelT lg) g -> 
      G_all (P_Finite RelT lg') g.
    Proof.
      intros lg lg' g H1.
      apply G_all_monotone.
      intros g'.
      apply P_Finite_monotone, H1.
    Qed.

    Lemma G_Finite_Geq_eq (RelT: relation T)(Req: Equivalence RelT): 
      forall (g1 g2: Graph), Geq RelT g1 g2 -> ((G_finite RelT g1) ->G_finite RelT g2).
    Proof.
      intros g1 g2 H1 [l H2].
      apply (is_Gfinite (G_all_Geq_eq (P_FiniteM Req (lg := l)) H1 H2)).
    Qed.

    Lemma collectLists_G' (RelT: relation T)(Req: Equivalence RelT)(l: ilist Graph):
      iall (G_finite RelT) l -> exists lg, iall (G_all (P_Finite RelT lg)) l.
    Proof.
      intros H.
      destruct l as [n l] ; fold (mkilist l) in *|-*.
      induction n as [|n IH].
      exists nil.
      intro i.
      inversion i.
      assert (H1 : iall (G_finite RelT) (mkilist (fun x => l (succ x)))).
      intro i.
      apply (H (succ i)).
      destruct (IH _ H1) as [lg H2].
      destruct (H (first n)) as [lg' H3].
      exists (lg' ++ lg).
      unfold iall.
      intro i.
      elim (zerop (decode_Fin i)) ; intros H4.
      rewrite (decode_Fin_0_first _ H4).
      apply (G_all_P_Finite_monotone (incl_appl lg (incl_refl _))), H3.
      apply (G_all_P_Finite_monotone (incl_appr lg' (incl_refl _))).
      rewrite (decode_Fin_unique _ _ (decode_Fin_get_cons _ H4 : _ = decode_Fin (succ _))).
      apply (H2 (get_cons i H4)).
    Qed.

    (* Proof that if and only if g is finite, 
       the graphs included in g are finite too *)
    Lemma GinG_finite_ci (RelT: relation T)(Req: Equivalence RelT): 
      forall g: Graph, G_finite RelT g <-> iall (G_finite RelT) (sons g).
    Proof.
      split ;
      intros H.
      intro f.
      destruct H as [lg H].
      apply (is_Gfinite (lg := lg)).
      destruct H as [g _ H2].
      apply (H2 f).
      
      destruct (collectLists_G' _ H) as [lg H1].
      apply (is_Gfinite (lg := g :: lg)).
      apply is_Gall.
      exists g.
      split.
      apply in_eq.
      apply (Geq_refl _).
      intro i. 
      apply (G_all_P_Finite_monotone (incl_tl _ (incl_refl lg))), H1.
    Qed.

    Lemma G_all_G_in_G_P(RelT: relation T)(Req: Equivalence RelT): 
       forall (P: Graph -> Prop)(HypP: Geq_prop_morph RelT P)(g: Graph), 
       G_all P g -> (forall gin,  Graph_in_Graph RelT gin g -> P gin).
    Proof.
      intros P HypP _ [g _ Hall] gin Hin.
      unfold Geq_prop_morph in HypP.
      induction Hin as [g f Hin | g f Hin IH].
      rewrite <- (Geq_sym _ Hin).
      destruct (Hall f) as [g' HPg _].
      assumption.
      destruct (Hall f) as [g'  _ H].
      apply (IH H).
    Qed.

    Lemma G_finite_All_G_in_G_finite (RelT: relation T)(Req: Equivalence RelT): 
      forall g: Graph, G_all (G_finite RelT) g -> (forall gin: Graph, 
      Graph_in_Graph RelT gin g -> G_finite RelT gin).
    Proof.
      apply (G_all_G_in_G_P _).
      intros g1 g2 H1 H2.
      apply (G_Finite_Geq_eq _ H1 H2).
    Qed.

    Lemma G_finite_All_G_in_G_finite' (RelT: relation T)(Req: Equivalence RelT): 
      forall g: Graph, G_finite RelT g -> (forall gin: Graph, 
      Graph_in_Graph RelT gin g -> G_finite RelT gin).
    Proof.
      intros g H1 gin H2.
      induction H2 as [g f H3 | g f _ IH] ; 
      destruct (GinG_finite_ci _ g) as [H2 _].
      apply (G_Finite_Geq_eq _ (Geq_sym _ H3)).
      apply (H2 H1 f).
      apply (IH (H2 H1 f)).
    Qed.

  End Finite_def_tools.
End Graphs_def_tools. 

Section Graphs_of_nat.
  Section Theorem_for_infinity_gene.

    Definition morph_f (T: Set)(R: relation T)(f: T -> nat):=
      Proper (R ==> eq(A := nat)) f.

    Definition mf (T: Set)(R: relation T)(f: T -> nat) := 
      forall g1 g2, R g1 g2 -> f g1 = f g2.

    Lemma finite_bounded : 
     forall (T: Set)(RelT: relation T)(g: Graph T)(f: Graph T -> nat)
     (hm: morph_f (Geq RelT) f), G_finite RelT g -> exists m, 
     G_all (fun x => f x <= m) g.
    Proof.
      intros T RelT g f hm [lg H].
      exists (max_list_nat (map f lg)).
      revert g H.
      cofix Hc.
      intros _ [g [g' [H1 H2]] H].
      apply is_Gall.
      rewrite (hm _ _ H2).
      apply (max_list_max (map f lg) _ (in_map _ _ _ H1)).
      intro i.
      apply (Hc _ (H i)).
    Qed.

    Lemma morph_f_label_nat : morph_f (Geq (@eq nat)) (@label nat).
    Proof.
      intros _ _ [g1 g2 e _].
      assumption.
    Qed.
    
    Lemma finite_label_bounded : forall g: Graph nat, 
      G_finite (@eq nat) g -> exists m, G_all (fun x => (label x <= m)) g.
    Proof.
      intros g H.
      apply (finite_bounded morph_f_label_nat H).
    Qed.

    Lemma morph_f_nb_sons (T: Set)(RelT: relation T) : 
      morph_f (Geq RelT) (fun x => lgti (sons x)).
    Proof.
      intros _ _ [g1 g2 _ [e _]].
      assumption.
    Qed.
    
    Lemma finite_ilist_bounded (T: Set)(RelT: relation T): 
      forall g: Graph T, G_finite RelT g -> 
      exists m, G_all ((fun x => lgti (sons x) <= m)) g.
    Proof.
      intros g H.
      apply (finite_bounded (@morph_f_nb_sons T RelT) H).
    Qed.

  End Theorem_for_infinity_gene.

  Section Theorem_for_infinity.

    Definition Pg_label_bound(m: nat) := (fun x : Graph nat => label x <= m).

    Add Parametric Morphism (m: nat): (Pg_label_bound m)
      with signature (Geq (@eq nat) ==> impl)
      as Pg_label_boundM.
    Proof.
      intros a1 a2 Heq H.
      destruct Heq as [a1 a2 e _].
      unfold Pg_label_bound.
      rewrite <- e.
      assumption.
    Qed.
    
    Lemma infinite_unbounded : 
     forall (T: Set)(RelT: relation T)(g: Graph T)(f: Graph T -> nat)
     (hm: morph_f (Geq RelT) f), not (exists m, 
     G_all (fun x => f x <= m) g) -> not (G_finite RelT g).
    Proof.
      intros T RelT g f H1 H2 H3.
      apply H2.
      apply (finite_bounded H1 H3).
    Qed.

    (* contrapositive of the previous lemma *)
    Lemma unbounded_infiniteGraph : 
      forall g: Graph nat, not (exists m, G_all (Pg_label_bound m) g) -> 
      not (G_finite (@eq nat) g).
    Proof.
      intros g H1.
      apply (infinite_unbounded morph_f_label_nat H1).
    Qed.

    Definition Pg_ilist_bound (T: Set) (m: nat): Graph T -> Prop:= 
      fun x: Graph T => lgti (sons x) <= m.

    (* contrapositive of the previous lemma *)
    Lemma ilist_unbounded_infiniteGraph : forall (T: Set)(RelT: relation T), 
      forall g: Graph T, not (exists m,  G_all (Pg_ilist_bound m) g) -> 
      not (G_finite RelT g).
    Proof.
      intros T RelT g.
      apply infinite_unbounded.
      apply morph_f_nb_sons.
    Qed.
      
  End Theorem_for_infinity.

Section Examples.

  Section Finite_example.

     (* Example of a finite graph *)
     Definition finite_example: Graph nat.
     Proof.
       cofix Hc.
       exact (mk_Graph 0 (singleton (mk_Graph 1 (singleton Hc)))).
     Defined.
     
    (* Proof that it is finite *)
    Lemma finite_example_finite: G_finite (@eq nat) finite_example.
    Proof.
      apply (is_Gfinite (lg := 
        finite_example :: (mk_Graph 1 (singleton finite_example)) ::nil)).
      cofix Hc.
      apply is_Gall.
      exists finite_example.
      split.
      apply in_eq.
      apply (Geq_refl _).
      intro f.
      apply is_Gall.
      exists (fcti (sons finite_example) (first 0)).
      split.
      right ; left; reflexivity.
      apply (Geq_refl _).
      unfold iall.
      simpl.
      intro f'.
      apply Hc.
    Qed.

    Definition finite_example_unfolded: Graph nat.
    Proof.
      cofix Hc.
      exact (mk_Graph 0 (singleton (mk_Graph 1 
        (singleton (mk_Graph 0 (singleton (mk_Graph 1 (singleton Hc)))))))).
    Defined.

   Lemma finite_example_Geq_finite_example_unfolded: 
     Geq (@eq _) finite_example finite_example_unfolded.
    Proof.
      cofix Hc.
      assert (H :forall (T: Set) (a1 a2: T), lgti (singleton a1) = lgti (singleton a2)).
      intros T a1 a2 ; reflexivity.
      do 4 (apply Geq_intro ; try reflexivity ; simpl ; 
        apply (is_ilist_rel _ _ _ (H _ _ _)) ; 
        simpl ; intro f ; clear f).
      apply Hc.
    Qed.

  End Finite_example.

  Section Infinite_example.

     (* Example of an infinite graph (whose labels are unbounded) *)
    Definition infinite_graph_gene: forall (n: nat), Graph nat.
    Proof.
      cofix Hc.
      intros n.
      exact (mk_Graph n (singleton (Hc (S n)))).
    Defined.

    Lemma infinite_graph_gene_n_inc_Sn: forall n: nat, 
      Geq (@eq nat) (fcti (sons (infinite_graph_gene n)) (first 0)) 
        (infinite_graph_gene (S n)).
    Proof.
      intros n.
      apply (Geq_refl _).
    Qed.
 
    Lemma infinite_graph_gene_Sn_in_n: forall n : nat, 
      Graph_in_Graph (@eq nat) (infinite_graph_gene (S n)) (infinite_graph_gene n).
    Proof.
      intros n.
      apply (is_Graph_in_Graph_dir _ (first _ : Fin (lgti (sons (infinite_graph_gene n))))).
      apply (Geq_refl _).
    Qed.

    Lemma infinite_example_gene_n_inc_all: forall n m: nat, 
      n < m -> Graph_in_Graph (@eq _) (infinite_graph_gene m) (infinite_graph_gene n).
    Proof.
      intros n m H.
      induction m as [| m IHm].
      inversion H.
      elim (le_lt_eq_dec n m (lt_n_Sm_le _ _ H)); intros h.
      apply (Graph_in_Graph_trans (@eq_equivalence _) (infinite_graph_gene_Sn_in_n m) 
        (IHm h)).
      rewrite h.
      apply infinite_graph_gene_Sn_in_n.
    Qed.

    Lemma infinite_example_gene_unbounded : forall n: nat, 
      not (exists m, G_all (fun x => label x <= m) (infinite_graph_gene n)).
    Proof.
      intros n [m H].
      inversion H as [g h H0 e].
      clear g e H0.
      simpl in *|-*.
      assert (Hin := infinite_example_gene_n_inc_all (le_gt_S _ _ h)).
      assert (S m <= m).
      apply (G_all_G_in_G_P (@eq_equivalence _) (@Pg_label_boundM m) H Hin).
      apply (le_Sn_n _ H0).
    Qed.
  
    (* Proof that it is infinite *)
    Lemma infinite_example_infinite: forall n: nat, 
      not (G_finite (@eq _) (infinite_graph_gene n)).
    Proof.
      intros n.
      apply unbounded_infiniteGraph.
      unfold Pg_label_bound.
      apply (infinite_example_gene_unbounded n).
    Qed.

  End Infinite_example.

  Section Infinite_example_bounded.
    
    Fixpoint addn0 (n: nat) (g: Graph nat) : Graph nat := 
      match n with
        O =>  g 
      | S m => mk_Graph 0 (singleton (addn0 m g))
      end.
    
    Definition add11 (g: Graph nat): Graph nat := mk_Graph 1 (singleton g).

    Definition addn011 (n: nat) (g: Graph nat): Graph nat := 
      (addn0 n (add11 g)).
    
    Definition inf_ex_bounded_gene_aux : forall (n: nat)(m: nat), Graph nat.
    Proof.
      cofix Hc.
      intros n m.
      destruct m as [| m].
      exact (add11 (Hc (S n) (S n))).
      exact (mk_Graph 0 (singleton (Hc n m))).
    Defined.


     (* Example of an infinite graph (whose labels and length of sons are bounded) *)
    Definition inf_ex_bounded_gene (n: nat) : Graph nat := 
      inf_ex_bounded_gene_aux n n.

  Lemma not_minus_O_le: forall (m n: nat), m -n =0 -> m <= n.
  Proof.
    intros n m H.
    apply not_lt.
    intros H1.
    rewrite (minus_n_m_0 (lt_le_weak _ _ H1) H) in H1.
    apply (lt_irrefl _ H1).
  Qed.

  Lemma list_not_infinite' : forall (lg: list (Graph nat))(seq: nat -> Graph nat),
    (forall (n m:nat), Geq (@eq _) (seq n)(seq(n+m)) -> m=0) ->
    (forall (n:nat), n <= length lg -> ~~P_Finite (@eq _) lg (seq n)) -> False.
  Proof.
    induction lg as [|g lg IH]; intros seq H1 H2.
    apply (H2 0 (le_refl 0)).
    intros [g [H3 _]].
    inversion H3.

(* the following first part of the proof is based on a simple intuitive argument:
   not all elements up to index length lg can be in P_Finite lg, 
   hence one of them must be bisimilar with g
*)

    apply (IH _ H1).
    intros n H3 H4.

    apply (H2 _ (lt_le_weak _ _ (le_lt_n_Sm _ _ H3))) ; intro H0.

    assert (H5: Geq (@eq _) (seq n) g).
    destruct H0 as [g' [[H5|H5] H6]];
    [rewrite H5 | destruct H4 ; exists g' ; split]; assumption.

  
(* also the following second  part of the proof is based on a simple intuitive argument:   
   If we throw this element (seq x) out, the remaining sequence has all elements up to index 
   length lg in P_Finite lg since g is already taken. Now, this is a contradiction.
*)
 
(* first some preparations *)
   set (seq' := fun x: nat => if (le_lt_dec n x) then seq (S x) else seq x).
   assert (seq'Prop: (forall x: nat, x < n -> seq' x = seq x) /\ 
     (forall x: nat, n <= x -> seq' x = seq (S x))).
   split ; intros x h ; unfold seq'; elim (le_lt_dec n x) ; intro a ; try reflexivity ; 
   [assert (h1 := (le_lt_trans n x n a h)) | assert (h1 := (le_lt_trans n x n h a))] ; 
   elim (lt_irrefl _ h1).
   destruct seq'Prop as [seq'Prop1 seq'Prop2].

   assert (H6 : (∀n m : nat, Geq (@eq _) (seq' n) (seq' (n + m)) → m = 0)).

(* seq' is a sub-sequence of seq, so 
  forall n m : nat, Geq (seq' n) (seq' (n + m)) -> m = 0
   is a consequence of the same property for seq *)

   intros n' m H6.
   destruct (le_lt_dec n (n'+m)) as [h1|h1].
   rewrite (seq'Prop2 _ h1) in H6.
   destruct (le_lt_dec n n') as [h2 |h2].
   rewrite (seq'Prop2 _ h2) in H6.
   rewrite <- plus_Sn_m in H6.
   apply (H1 (S n') _ H6).
   rewrite (seq'Prop1 _ h2) in H6.
   rewrite plus_n_Sm in H6.
   elim (O_S _ (sym_eq (H1 _ _ H6))).
   do 2 rewrite seq'Prop1 in H6 ; try exact h1 ; 
   try exact (le_lt_trans _ _ _ (le_plus_l n' m) h1).
   apply (H1 _ _ H6).

(* we can now carry out the second step of the proof *)
   apply (IH _ H6).
   intros n' H7 H8.
   destruct (le_lt_dec n n') as [h1|h1'];
   [rewrite (seq'Prop2 _ h1) in H8 ; destruct (H2 (S n') (le_n_S _ _ H7))
   | rewrite (seq'Prop1 _ h1') in H8 ; set (h1 := lt_le_weak _ _ h1'); 
     destruct (H2 n' (le_S _ _ H7))];
   intros  [g0 [[Hyp1|Hyp1] Hyp2]] ; apply H8;
   try (exists g0 ; split; assumption) ; rewrite <- Hyp1 in Hyp2 ;
   assert (H10:=(GeqRel_Transitive (@eq_equivalence _) H5 
     (GeqRel_Symmetric (@eq_equivalence _) Hyp2)));
   rewrite (le_plus_minus _ _ h1) in H10.
   rewrite plus_n_Sm in H10.
   elim (O_S _ (sym_eq (H1 _ _ H10))).
   elim (lt_irrefl _ (le_lt_trans n n' n 
     (not_minus_O_le _ _ (H1 _ _ (GeqRel_Symmetric (@eq_equivalence _) H10))) h1')).
Qed.

  Lemma list_not_infinite: forall (lg: list (Graph nat))(seq: nat -> Graph nat),
    (forall (n m:nat), Geq (@eq _) (seq n)(seq(n+m)) -> m=0) ->
    (forall (n:nat), n <= length lg -> P_Finite (@eq _)lg (seq n)) -> False.
  Proof.
    intros lg seq H1 H2.
    apply (@list_not_infinite' lg seq H1).
    intros n h H3.
    apply H3.
    apply (H2 n h).
  Qed.

  Lemma inf_ex_bounded_gene_aux_0 : forall (n: nat),
    inf_ex_bounded_gene_aux n 0 = 
    mk_Graph 1 (singleton (inf_ex_bounded_gene_aux (S n) (S n))).
  Proof.
    intros n.
    rewrite <- (etaExpandG_Identity (inf_ex_bounded_gene_aux n 0)).
    reflexivity.
  Qed.

  Lemma inf_ex_bounded_gene_aux_S : forall (n m: nat),
    inf_ex_bounded_gene_aux n (S m) = 
    mk_Graph 0 (singleton (inf_ex_bounded_gene_aux n m)).
  Proof.
    intros n m.
    rewrite <- (etaExpandG_Identity (inf_ex_bounded_gene_aux n (S m))).
    reflexivity.
  Qed.

  Lemma inf_ex_bounded_gene_aux_addn011: forall (n m: nat),
    inf_ex_bounded_gene_aux n m = addn011 m (inf_ex_bounded_gene_aux (S n)(S n)).
  Proof.
    intro n.
    induction m as [|m IHm].
    apply inf_ex_bounded_gene_aux_0.
    rewrite inf_ex_bounded_gene_aux_S.
    rewrite IHm.
    unfold addn011 at 2.
    reflexivity.
  Qed.
    
  Lemma inf_ex_bounded_gene_addn011: forall n, 
    inf_ex_bounded_gene n = addn011 n (inf_ex_bounded_gene (S n)).
  Proof.
    intro n.
    unfold inf_ex_bounded_gene.
    apply inf_ex_bounded_gene_aux_addn011.
  Qed.

  Lemma addn011_Geq : forall (g1 g2: Graph nat)(n: nat),
    Geq (@eq _) g1 g2 -> Geq (@eq _) (addn011 n g1) (addn011 n g2).
  Proof.
    intros g1 g2 n H.
    induction n as [|n IHn].
    apply Geq_intro.
    reflexivity.
    assert (h : lgti (singleton g1) = lgti (singleton g2)).
    reflexivity.
    apply (is_ilist_rel _ _ _ h).
    intro f.
    assumption.
    simpl.
    apply Geq_intro.
    reflexivity.
    assert (h : lgti (singleton (addn011 n g1)) = lgti (singleton (addn011 n g2))).
    reflexivity.
    apply (is_ilist_rel _ _ _ h).
    intro f.
    assumption.
  Qed.

  Lemma addn0comp : forall (n1 n2: nat)(g: Graph nat),
    addn0 n1 (addn0 n2 g) = addn0 (n1+n2) g.
  Proof.
    induction n1 as [|n1 IHn].
    reflexivity.
    intros n2 g.
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma addn0_Geq_inv: forall (n: nat)(g1 g2: Graph nat),
    Geq (@eq _) (addn0 n g1)(addn0 n g2) -> Geq (@eq _) g1 g2.
  Proof.
    intros n g1 g2 H.
    induction n as [|n IHn] ;
    inversion H as [g3 g4 e1 [e H1] h1 h2] ;
    clear g3 g4 e1 h1 h2.
    assumption.
    simpl in H1.
    apply (IHn (H1 (first _))).
  Qed.

  Lemma addn0_Geq: forall (n: nat)(g1 g2: Graph nat),
   Geq (@eq _) g1 g2 ->  Geq (@eq _) (addn0 n g1)(addn0 n g2).
  Proof.
    induction n as [|n IH]; intros g1 g2 H.
    apply H.
    apply Geq_intro.
    reflexivity.
    simpl.
    apply (is_ilist_rel _ _ _ (refl_equal _ : 
     lgti (singleton (addn0 n g1)) = lgti(singleton (addn0 n g2)))).
    simpl.
    intro i ; apply IH, H.
  Qed.

  Lemma inf_ex_bounded_gene_inj (n m: nat): 
    Geq (@eq _) (inf_ex_bounded_gene n)(inf_ex_bounded_gene (n+m)) -> m=0.
  Proof.
    destruct m.
    reflexivity.
    intro.
    rewrite inf_ex_bounded_gene_addn011 in H.
    rewrite (inf_ex_bounded_gene_addn011 (n + S m)) in H.
    unfold addn011 in H.
    rewrite <- addn0comp in H.
    apply addn0_Geq_inv in H.
    inversion H as [g3 g4 e1 h0 h1 h2] ; inversion e1.
  Qed.

  Lemma G_all_addn0_inv: forall (lg: list (Graph nat))(g: Graph nat)(n: nat),
    G_all (P_Finite (@eq _) lg) (addn0 n g) -> 
    G_all (P_Finite (@eq _) lg) g.
  Proof.
    intros lg g n H.
    induction n as [|n IHn].
    assumption.
    inversion H as [g' Hp Hall e].
    apply (IHn (Hall (first 0))).
  Qed.

  Lemma G_all_add11_inv: forall (lg: list (Graph nat))(g: Graph nat),
    G_all (P_Finite (@eq _) lg) (add11 g) ->  G_all (P_Finite (@eq _) lg) g.
  Proof.
    intros lg g H.
    inversion H as [g' Hp Hall e].
    apply (Hall (first 0)).
  Qed.

  Lemma G_all_addn011_inv: forall (lg: list (Graph nat))(g: Graph nat)(n: nat),
    G_all (P_Finite (@eq _) lg) (addn011 n g) ->  G_all (P_Finite (@eq _) lg) g.
  Proof.
    intros lg g n H.
    apply (G_all_add11_inv (G_all_addn0_inv _ _ H)).
  Qed.

  Lemma inf_ex_bounded_geneelements_aux: forall (n: nat)(lg: list (Graph nat)),
    G_all (P_Finite (@eq _) lg) (inf_ex_bounded_gene n) -> 
    forall m: nat, G_all (P_Finite (@eq _) lg) (inf_ex_bounded_gene (n+m)).
  Proof.
    intros n lg Hyp m. revert n Hyp.
    induction m as [|m IHm]; intros n Hyp.
    rewrite <- plus_n_O.
    assumption.
    rewrite <- plus_n_Sm.
    assert (H:= IHm _ Hyp).
    rewrite inf_ex_bounded_gene_addn011 in H.
    apply (G_all_addn011_inv _ _ H).
  Qed.

  Lemma inf_ex_bounded_geneelements: forall (n: nat)(lg: list (Graph nat)),
    G_all (P_Finite (@eq _) lg) (inf_ex_bounded_gene n) -> 
    forall m: nat, P_Finite (@eq _) lg (inf_ex_bounded_gene (n+m)).
  Proof.
    intros n lg H m.
    assert (H0:= inf_ex_bounded_geneelements_aux _ H m).
    inversion H0.
    assumption.
  Qed.


    (* proof that it is infinite *)
    Theorem inf_ex_bounded_gene_infinite: forall (n: nat), 
      not (G_finite (@eq _) (inf_ex_bounded_gene n)).
    Proof.
      intros n H.
      inversion H as [lg Hall].
      apply (list_not_infinite (lg:=lg) (fun m:nat => inf_ex_bounded_gene (n+m))).
      intros n' m H1.
      rewrite plus_assoc in H1.
      apply inf_ex_bounded_gene_inj in H1.
      assumption.
      intros n' Hle.
      apply (inf_ex_bounded_geneelements _ Hall).
    Qed.
    
    Definition ilist_n0 (n: nat) := mkilist (fun i : Fin n => 0).
    
    (* Compression of inf_ex_bounded_gene *)
    CoFixpoint inf_ex_bounded_gene' (n : nat) : Graph (ilist nat) := 
      mk_Graph (ilist_n0 n) (singleton (inf_ex_bounded_gene' (S n))).
      
    Definition nb_O (g: Graph (ilist nat)) : nat := 
      match g with 
        mk_Graph l _ => lgti l 
      end.
    Lemma  inf_ex_bounded_gene'_Sn_n(n: nat): 
      Graph_in_Graph eq (inf_ex_bounded_gene' (S n)) (inf_ex_bounded_gene' n).
    Proof.
      apply (is_Graph_in_Graph_dir _ (first _ : Fin (lgti (sons (inf_ex_bounded_gene' n))))).
      apply (Geq_refl _).
    Qed.

    Lemma inf_ex_bounded_gene'_m_n (n m : nat): n < m -> 
      Graph_in_Graph eq (inf_ex_bounded_gene' m) (inf_ex_bounded_gene' n).
    Proof.
      intros H.
      induction m as [| m IHm].
      inversion H.
      elim (le_lt_eq_dec n m (lt_n_Sm_le _ _ H)); intros h.
      apply (Graph_in_Graph_trans (@eq_equivalence _) (inf_ex_bounded_gene'_Sn_n _)
        (IHm h)).
      rewrite h.
      apply inf_ex_bounded_gene'_Sn_n.
    Qed.
    
    Theorem inf_ex_bounded_gene'_infinite: forall (n: nat), 
      not (G_finite (@eq _) (inf_ex_bounded_gene' n)).
    Proof.
      intros n.
      assert (H1 := @infinite_unbounded _ eq (inf_ex_bounded_gene' n) nb_O).
      assert (H2 : morph_f (Geq eq) nb_O).
      intros _ _ [[lab1 l1] [lab2 l2] H2 _].
      simpl in *|-*.
      rewrite H2.
      reflexivity.
      apply (H1 H2) ; clear H1.
      intros [m H3].
      inversion H3.
      assert (H4 : S m <= m).
      assert (H5 : forall m x y, Geq eq x y -> impl (nb_O x <= m) (nb_O y <= m)).
      intros m' _ _ [[labx lx] [laby ly] H4 H5] H6.
      simpl in *|-*.
      rewrite <- H4 ; assumption.
      rewrite (refl_equal _ : S m = nb_O (inf_ex_bounded_gene' (S m))).
      apply (G_all_G_in_G_P _ (H5 m) H3).
      apply inf_ex_bounded_gene'_m_n, le_gt_S, H.
      apply (le_Sn_n _ H4).
    Qed.
      
  End Infinite_example_bounded.

End Examples.

Definition is_cycle (T: Set)(RelT: relation T) (g: Graph T): Prop := 
  Graph_in_Graph RelT g g.

Lemma finite_example_is_cycle : is_cycle (@eq _) finite_example.
Proof.
  apply (is_Graph_in_Graph_indir finite_example (first 0)).
  apply (is_Graph_in_Graph_dir (mk_Graph 1 (singleton finite_example)) (first 0)).
  apply (Geq_refl _).
Qed.

Inductive hasCycle (T: Set)(RelT: relation T)(g: Graph T): Prop := 
  hasCycle_dir: is_cycle RelT g -> hasCycle RelT g
| hasCycle_indir: forall f, hasCycle RelT (fcti (sons g) f) -> hasCycle RelT g.

Lemma finite_example_has_cycle: hasCycle (@eq _) finite_example.
Proof.
  apply hasCycle_dir.
  apply finite_example_is_cycle.
Qed.
  
Definition JustOneLeaf (n: nat) := mk_Graph n (inil (Graph nat)).

Lemma JustOneLeaf_not_cycle: forall n: nat, not (hasCycle (@eq _) (JustOneLeaf n)).
Proof.
  intros n [[f H |f H]|f H];
  inversion f.
Qed.

Lemma JustOneLeaf_finite (n: nat) : G_finite eq (JustOneLeaf n).
Proof.
  apply (is_Gfinite (lg := JustOneLeaf n :: nil)).
  apply is_Gall.
  exists (JustOneLeaf n).
  split.
  left ; reflexivity.
  apply (Geq_refl _).
  unfold iall.
  simpl.
  intro i.
  inversion i.
Qed.

CoFixpoint three_nodes_graph: Graph nat :=
  mk_Graph 1 (icons (mk_Graph 3 (icons three_nodes_graph (inil (Graph nat))))
                    (icons (mk_Graph 2 (inil (Graph nat))) (inil (Graph nat)))).

Lemma three_nodes_graph_hasCycle: hasCycle (@eq _) three_nodes_graph.
Proof.
  apply hasCycle_dir.
  apply (is_Graph_in_Graph_indir three_nodes_graph (first 1)).
  apply (is_Graph_in_Graph_dir (fcti (sons three_nodes_graph) (first 1)) (first 0)).
  apply (Geq_refl _).
Qed.

Definition three_nodes_graph_bis: Graph nat.
Proof.
  set (g2 := mk_Graph 2 (inil (Graph nat))).
  set (g3 := mk_Graph 3 (icons g2 (inil (Graph nat)))).
  exact (mk_Graph 1 (icons g2 (icons g3 (inil (Graph nat))))).
Defined.

Lemma three_nodes_graph_bis_not_hasCycle: not (hasCycle (@eq _) three_nodes_graph_bis).
Proof.
  intros [[f H |f H]| f H];
  elim (zerop (decode_Fin f)) ; intros a ;
  try assert (h:= (le_antisym _ _ (gt_S_le _ _ (decode_Fin_inf_n f)) (gt_le_S _ _ a))) ;
  try assert (h := a) ; 
  try assert (H2 := decode_Fin_unique _ _ (h: _ = decode_Fin (first _)) : f = first 1) ; 
  try assert (H2 := decode_Fin_unique _ _ (h: _ = decode_Fin (succ (first 0))) : 
    f = succ (first 0)) ; 
  simpl in f, H ; rewrite H2 in H; clear f h H2 a;
  try (inversion H as [g1 g2 e H1 H3 H4] ; inversion e) ; 
  try (destruct H as [f' H | f' H] ;
  rewrite (Fin_first_1 f') in H ; clear f' ; 
  try (inversion H as [g1 g2 e H1 H3 H4] ; inversion e)) ; 
  try (destruct H as [[f H| f H] |f H] ; simpl in H ; rewrite (Fin_first_1 f) in H ; 
    clear f) ; 
  try (inversion H as [g1 g2 e H1 H3 H4] ; inversion e) ; 
  try (destruct H as [[f H| f H] | f H] ; inversion f) ; 
  destruct H as [f H | f H] ; inversion f.
Qed.

CoFixpoint two_nodes_cycle: Graph nat := 
  mk_Graph 2 (icons (mk_Graph 3 (icons two_nodes_cycle (inil (Graph nat)))) 
                    (inil (Graph nat))).

Lemma two_nodes_cycle_hasCycle: hasCycle (@eq _) two_nodes_cycle.
Proof.
  apply hasCycle_dir.
  apply (is_Graph_in_Graph_indir _ (first 0 : Fin (lgti (sons two_nodes_cycle)))).
  apply (is_Graph_in_Graph_dir _ (first 0 : Fin (lgti (sons (fcti (sons two_nodes_cycle) (first 0)))))).
  apply (Geq_refl _).
Qed.

Definition three_nodes_graph_ter: Graph nat := 
  mk_Graph 1 (icons two_nodes_cycle 
                   (icons (mk_Graph 3 (icons two_nodes_cycle (inil (Graph nat))))
                          (inil (Graph nat)))).

Lemma three_nodes_graph_ter_hasCycle: hasCycle (@eq _) three_nodes_graph_ter.
Proof.
  apply (hasCycle_indir _ (first 1 : Fin (lgti (sons three_nodes_graph_ter)))).
  apply hasCycle_dir.
  apply (is_Graph_in_Graph_indir (fcti (sons three_nodes_graph_ter) (first 1)) (first 0)).
  apply (is_Graph_in_Graph_dir 
    (fcti (sons (fcti (sons three_nodes_graph_ter) (first 1))) (first 0)) (first 0)) .
  apply (Geq_refl _).
Qed.

Lemma three_nodes_graph_ter_hasCycle2: hasCycle (@eq _) three_nodes_graph_ter.
Proof.
  apply (hasCycle_indir _ (succ (first 0) : Fin (lgti (sons three_nodes_graph_ter)))).
  apply hasCycle_dir.
  apply (is_Graph_in_Graph_indir (fcti (sons three_nodes_graph_ter) (succ (first 0))) 
    (first 0)).
  apply (is_Graph_in_Graph_dir 
    (fcti (sons (fcti (sons three_nodes_graph_ter) (succ (first 0)))) (first 0)) 
    (first 0)) .
  apply (Geq_refl _).
Qed.

Definition three_nodes_graph4: Graph nat.
Proof.
  cofix g1.
  set (g3 := mk_Graph 3 (icons g1 (inil (Graph nat)))).
  set (g2 := mk_Graph 2 (icons g3 (inil (Graph nat)))).
  exact (mk_Graph 2 (icons g2 (inil (Graph nat)))).
Defined.

Lemma three_nodes_graph4_hasCycle: hasCycle (@eq _) three_nodes_graph4.
Proof.
  apply hasCycle_dir.
  apply (is_Graph_in_Graph_indir three_nodes_graph4 (first 0)).
  apply (is_Graph_in_Graph_indir (fcti (sons three_nodes_graph4) (first 0)) (first 0)).
  apply (is_Graph_in_Graph_dir 
    (fcti (sons (fcti (sons three_nodes_graph4) (first 0))) (first 0)) 
    (first 0) (Geq_refl _ _)).
Qed.

End Graphs_of_nat.

Section hasCycle'.

  Inductive hasCycle'(T: Set)(RelT: relation T)(g: Graph T) : Prop := 
    hasCycle'_intro : forall (g': Graph T), is_cycle RelT g' -> GinG' RelT g' g -> hasCycle' RelT g.
    
    Lemma hasCycle'_sons (T: Set)(RelT: relation T)(Req: Equivalence RelT)(g: Graph T)
      (i: Fin (lgti (sons g))): hasCycle' RelT (fcti (sons g) i) -> hasCycle' RelT g.
    Proof.
      intros [g' H1 H2].
      apply (hasCycle'_intro H1).
      apply (GinG'_trans _ H2).
      apply GinG'_sons_in_Graph, is_Graph_in_Graph_Gene_dir.
      apply (Geq_refl _).
    Qed.
    
    Lemma hasCycle_hasCycle'(T: Set)(RelT: relation T)(Req: Equivalence RelT)(g: Graph T): 
      hasCycle RelT g -> hasCycle' RelT g.
    Proof.
      intros H.
      induction H as [g H |g i H IH].
      apply (hasCycle'_intro H).
      apply is_Graph_in_Graph_Gene_dir.
      apply (Geq_refl _). 
      apply (hasCycle'_sons _ _ _ IH).
    Qed.
    
    Add Parametric Morphism (T: Set)(RelT: relation T)(Req: Equivalence RelT) : 
      (is_cycle RelT) with signature (Geq RelT) ==> (impl)
    as is_cycleM.
    Proof.
      intros g1 g2 H1 H2.
      apply (Graph_in_GraphM _ H1), (Graph_in_GraphM2 _ H1), H2.
    Qed.
    
    Lemma hasCycle'_hasCycle(T: Set)(RelT: relation T)(Req: Equivalence RelT)(g: Graph T): 
      hasCycle' RelT g -> hasCycle RelT g.
    Proof.
      intros [g' H1 H2].
      induction H2 as [g H2 |g i H2 IH].
      apply hasCycle_dir.
      rewrite <- H2.
      apply H1.
      apply (hasCycle_indir _ i IH).
    Qed.

End hasCycle'.







