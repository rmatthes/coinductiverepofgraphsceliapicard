(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides a proposition of equivalence relation on 
     lists that allows to compare the elements of the list
     with a dedicated (possibly a bisimulation) relation *)

Set Implicit Arguments.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.

(* Notation Morphism R f := (Proper (R%signature) f). *)

Definition map:= List.map.

(* definition of the relation *)
Inductive ListEq (A: Set)(eqA: relation A): relation (list A) :=
   ListEq_nil: ListEq eqA nil nil
 | ListEq_cons: forall (a1 a2: A)(l1 l2: list A), 
     eqA a1 a2 -> ListEq eqA l1 l2 -> ListEq eqA (a1 :: l1)(a2 :: l2).

Add Parametric Morphism (A: Set): (ListEq(A:= A))
  with signature (subrelation(A:= A)) ==> (subrelation(A:= list A))
  as ListEq_monM.
Proof.
  intros eqA1 eqA2 HypSub t1 t2 Hyp.
  induction Hyp as [|a1 a2 l1 l2 e Hyp IH].
  - apply ListEq_nil.
  - apply ListEq_cons.  
    + apply HypSub.
      assumption.
    + assumption.
Qed.

(* proof that ListEq is an equivalence relation *)
Instance ListEq_refl : forall (A: Set)(eqA: relation A)`{Reflexive A eqA},
  Reflexive (ListEq eqA).
Proof.
  intros A eqA reflA x.
  induction x as [| a la IHl].
  - apply ListEq_nil.
  - apply ListEq_cons.
    + reflexivity.
    + assumption.
Qed.

Instance ListEq_sym : forall (A: Set)(eqA: relation A)`{Symmetric A eqA},
  Symmetric (ListEq eqA).
Proof.
  intros A eqA symA x y H.
  induction H as [|a1 a2 l1 l2 e H IH].
  - apply ListEq_nil.
  - apply ListEq_cons; 
      [symmetry|];
      assumption.
Qed.

Instance ListEq_trans: forall (A: Set)(eqA: relation A)`{Transitive A eqA},
  Transitive (ListEq eqA).
Proof.
  intros A eqA transA x y z H1 H2.
  revert z H2.
  induction H1 as [|a1 a2 x y e1 H1 IH1]; intros z H2.
  - assumption.
  - destruct z as [|a3 z] ;
      inversion_clear H2 as [| a4 a5 l1 l2 e2 H3].
    apply ListEq_cons.
    + apply (transA _ _ _ e1 e2).
    + apply (IH1 _ H3).
Qed.

Add Parametric Relation (A: Set)(eqA: relation A)`{Reflexive A eqA}: 
  (list A) (ListEq eqA) 
  reflexivity proved by (ListEq_refl(eqA:=eqA))
  as ListeqRefl.


Add Parametric Relation (A: Set)(eqA: relation A)`{Equivalence A eqA}: 
  (list A) (ListEq eqA) 
  reflexivity proved by (ListEq_refl(eqA:=eqA))
  symmetry proved by (ListEq_sym(eqA:=eqA))
  transitivity proved by (ListEq_trans(eqA:=eqA))
  as ListEqRel.

Instance ListEqeqeq : forall(A: Set), subrelation (ListEq (@eq A)) (@eq (list A)).
Proof.
  intros A x x0 H.
  induction H as [| a1 a2 l1 l2 e1 H IH].
  - reflexivity.
  - rewrite IH.
    rewrite e1.
    reflexivity.
Qed.

Instance eqListEqeq : forall (A: Set), subrelation (@eq (list A)) (ListEq (@eq A)).
Proof.
  intros A x x0 h.
  rewrite h.
  reflexivity.
Qed.

Section additional_functions.
(* redefinition of some classical functions of list using ListEq *)
Instance cmpeq : forall (A: Set)(cmp: relation A)(cmpRel : Equivalence cmp),
  subrelation (@eq A) cmp.
Proof.
  intros A cmp cmpRel x x0 h.
  rewrite h.
  reflexivity.
Qed.

Fixpoint InEq (A: Set)(cmpA: relation A)(a: A)(l: list A){struct l}: Prop:=
  match l with
  | nil => False
  | b :: m => cmpA b a \/ InEq cmpA a m
  end.

Lemma nth_indep_comp: 
  forall (A: Set)(cmp: relation A)(cmpRel: Equivalence cmp)
  (n: nat)(l: list A)(d d': A), n < length l -> cmp (nth n l d) (nth n l d').
Proof.
  intros A cmp cmpRel n l d d' h.
  apply (cmpeq cmpRel).
  apply (nth_indep _ _ _ h).
Qed.

Lemma map_map_ListEq: 
  forall (A B C: Set)(cmpC: relation C)(cmpCRel: Equivalence cmpC)
  (f: A -> B) (g: B -> C)(l: list A), 
  ListEq cmpC (map g (map f l)) (map (fun x: A => g (f x)) l).
Proof.
  intros A B C cmpC cmpCRel f g l.
  apply (cmpeq (ListEqRel(eqA:=cmpC))).
  apply map_map.
Qed.

Lemma map_nth_comp: 
  forall (A B: Set)(cmp: relation B)(cmpRel: Equivalence cmp)(f: A -> B)
  (l: list A)(d: A)(n: nat), cmp (nth n (map f l) (f d)) (f (nth n l d)).
Proof.
  intros A B cmp cmpRel  f l d n.
  apply (cmpeq cmpRel).
  apply map_nth.
Qed.

Lemma map_map_nth_comp: 
  forall (A B C: Set)(cmpB: relation B)(cmpBRel: Equivalence cmpB)
  (cmpC: relation C)(cmpCRel: Equivalence cmpC)
  (f: A -> B)(g: B -> C)(gM: Proper (cmpB ==> cmpC) g)
  (l: list A)(d: A)(n: nat), 
  cmpC (nth n (map g (map f l)) (g (f d))) (g (f (nth n l d))).
Proof.
  intros A B C cmpB cmpBRel cmpC cmpCRel f g gM l d n.
  rewrite (map_nth_comp cmpCRel g).
  apply gM.
  rewrite (map_nth_comp cmpBRel f).
  reflexivity.
Qed.

Lemma ListEq_map_f_g: 
  forall (A B: Set)(cmpB: relation B)(f g: A -> B) (l: list A), 
  (forall a: A, cmpB (f a) (g a))-> ListEq cmpB (map f l) (map g l).
Proof.
  intros A B cmpB f g l h.
  induction l as [| hd l].
  - apply ListEq_nil.
  - apply (ListEq_cons _ _ (h hd) IHl).
Qed.

Lemma ListEq_length: forall (A: Set)(cmpA: relation A)(l1 l2: list A), 
  ListEq cmpA l1 l2 -> length l1 = length l2.
Proof.
  intros A cmpA ; induction l1 as [| hd1 l1]; destruct l2 as [|hd2 l2]; 
  intros h; 
  try reflexivity;
  try (inversion_clear h as [| x y z t e H]).
  simpl.
  rewrite (IHl1 l2 H).
  reflexivity.
Qed.
  
Lemma ListEq_nth: forall (A: Set)(cmpA: relation A)(cmpAR: Equivalence cmpA)
  (l1 l2: list A) (n: nat)(h: n< length l1)(d: A), ListEq cmpA l1 l2 -> 
  cmpA (nth n l1 d) (nth n l2 d).
Proof.
  intros A cmpA cmpAR ; 
  induction l1 as [|hd1 l1 IHl] ; destruct l2 as [| hd2 l2]; 
  intros n h d le; try (inversion_clear le as [| x y z t e H]).
  - reflexivity.
  - destruct n as [|n].
  + assumption.
  + apply (IHl _ _ (lt_S_n _ _ h) _ H).
Qed.

Lemma ListEq_eq: forall (A B: Set)
  (cmpB: relation B)(cmpBR: Equivalence cmpB)
  (l: list A) (f1 f2: A -> B), ListEq cmpB (map f1 l) (map f2 l) ->
  forall a: A, In a l -> cmpB (f1 a) (f2 a).
Proof.
  intros A B cmpB cmpBR ; 
  induction l as [| hd l IHl]; intros f1 f2 H a Hin.
  - inversion Hin.
  - inversion_clear H as [| x y z t e h].
    destruct Hin as [eq | Hin].
    + rewrite <- eq.
      assumption.
    + apply IHl;
        assumption.
Qed.

End additional_functions.
