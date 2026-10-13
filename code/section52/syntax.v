(*

-> Section 5.2 in paper
-> Union Types + Null + Intersection Types
-> Intersection introduction
-> Nominal types
-> A * B -> A & B <: Bottom
-> Generalized subtyping for empty types

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
Require Export Lists.List.
Export ListNotations.

(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ
 | t_unit : typ
 | t_prim : nat -> typ.

Inductive exp : Set :=  (*r expression *)
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : typ -> typ -> exp -> exp (*r λ(x:A):B. e *)
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp
 | e_new    : nat -> exp.

(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 (*
 Inductive bind : Set :=
 | bind_typ : typ -> bind.

 *)
Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env typ.

Inductive okt : env -> Prop :=
| okt_empty :
     okt empty
| okt_typ : forall E x T,
     okt E-> x # E -> okt (E & x ~: T).

(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs A B e) => e_abs A B (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_null) => e_null
  | e_new A  => e_new A
end.


Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (L:vars) (A B:typ) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A B e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lec_e_null :
     lc_exp e_null
 | lc_e_new : forall A,
     lc_exp (e_new A).


(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_abs A B e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_null) => \{}
  | e_new A  => \{}
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs A B e) => e_abs A B (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_null) => e_null
  | (e_new A) => e_new A
end.


(*************************
*** Equality for types ***
**************************)

Lemma eq_dec_nat : forall (n1 n2 : nat), {n1 = n2} + {n1 <> n2}.
Proof.
  decide equality.
Defined.

Lemma eq_dec : forall x y:typ, {x = y} + {x <> y}.
Proof.
 decide equality.
 apply eq_dec_nat.
Defined.

Notation "l1 `union` l2" := (set_union eq_dec l1 l2) (at level 80).
Notation "l1 `inter` l2" := (set_inter eq_dec l1 l2) (at level 80).

(*******************************)
(*** Environment for P types ***)
(*******************************)


Definition envp := list (nat * typ).

(* Definition PG : envp. *)

Definition domain_envp (l : envp) : list nat := map fst l.

Definition range_envp (l : envp) : list typ := map snd l.

(*
get_all_subtypes returns all the primitive subtypes of a given type
*)

Require Import FunInd.

(*
issupertype returns true if A <: B
and false otherwise

It works for the transitive closure
It works for supertypes having multiple unrelated subtypes
*)

Function issupertype (l: envp) (A:typ) (B:typ) {struct l} : bool :=
    match l with
    | [] => false
    | (i, t) :: xs => match eq_dec A (t_prim i) with
                     | left _ => match eq_dec B t with
                                 | left _ => true
                                 | right _ => issupertype xs t B
                                 end
                     | right _ => issupertype xs A B
                    end
    end.

Function get_all_subtypes (l : envp) (A: typ) {struct l} : list nat :=
  match l with
  | [] => []
  | (i, t) :: xs => let flag := (issupertype l (t_prim i) A) in
                    match flag with
                      | true  => i :: (get_all_subtypes xs A)
                      | false => get_all_subtypes xs A
                      end
  end.

(* Eval compute in (issupertype [(3, (t_prim 2)); (2, (t_prim 1))]) (t_prim 1) (t_prim 2). *)


Definition get_all_subtypes_wrapper (A: typ) (l : envp) : list nat :=
  let l1 := (get_all_subtypes l A) in
    match l1 with
    | [] => match A with
            | (t_prim i) => [i]
            | _          => []
            end
    | _  => l1
    end.   


Fixpoint nats_to_types (l : list nat) {struct l} : (list typ) :=
  match l with
  | [] => []
  | a :: xs => [t_prim a] ++ (nats_to_types xs)
  end.


(*well-formdness type for *)
Inductive wft (PG:envp) : typ -> Prop :=
  | wft_top :
      wft PG t_top
  | wft_bot :
      wft PG t_bot
  | wft_int :
      wft PG t_int
  | wft_arrow : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_arrow A B)
  | wft_or : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_union A B)
  | wft_and : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_and A B)
  | wft_unit :
      wft PG t_unit
  | wft_prim : forall (i : nat),
      set_In i (domain_envp PG) ->
      wft PG (t_prim i).

Inductive okenvp : envp -> Prop :=
  | okenvp_empty :
      okenvp []
  | okenvp_sub : forall (PG:envp) (A:typ) (i:nat),
     okenvp PG ->
     wft PG A ->
     ~( set_In i (domain_envp PG)) ->
     okenvp ((i, A) :: PG).

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_arrow : forall t1 t2, Ord t2 -> Ord (t_arrow t1 t2)
| o_unit  : Ord t_unit
| o_prim  : forall i, Ord (t_prim i).

#[export]
Hint Constructors Ord : core.

(****************************************)
(**********  FindSubtypes    ************)
(****************************************)

(* TODO: How to return all prmitive types as subtype of top? *)

Fixpoint FindSubtypes (PG : envp) (A: typ) :=
    match A with
    | t_top         => [t_int; t_unit] ++ nats_to_types (domain_envp PG)
    | t_bot         => []
    | t_int         => [t_int]
    | t_arrow A1 B1 => []
    | t_union A1 B1 => (FindSubtypes PG A1) `union` (FindSubtypes PG B1)
    | t_and A1 B1   => (FindSubtypes PG A1) `inter` (FindSubtypes PG B1)
    | t_unit        => [t_unit]
    | t_prim i      => [t_prim i] ++ nats_to_types (get_all_subtypes PG (t_prim i))
    end.

Fixpoint ArrowRanges (PG : envp) (A: typ) :=
    match A with
    | t_top         => FindSubtypes PG t_top
    | t_bot         => []
    | t_int         => []
    | t_unit        => []
    | t_prim _      => []
    | t_arrow _ B   => FindSubtypes PG B
    | t_union A1 B1 => (ArrowRanges PG A1) `union` (ArrowRanges PG B1)
    | t_and A1 B1   => (ArrowRanges PG A1) `inter` (ArrowRanges PG B1)
    end.

Fixpoint FunRange (A: typ) : typ :=
    match A with
    | t_top         => t_top
    | t_arrow _ B   => B
    | t_union A1 B1 =>
        match FunRange A1, FunRange B1 with
        | t_bot, R => R
        | R, t_bot => R
        | R1, R2 => t_union R1 R2
        end
    | t_and A1 B1   =>
        match FunRange A1, FunRange B1 with
        | t_bot, _ => t_bot
        | _, t_bot => t_bot
        | R1, R2 => t_and R1 R2
        end
    | _             => t_bot
    end.

(* True when A still has a function part. Used by s_disj so that
   emptying FindSubtypes on arrows does not make every A→B bottomlike. *)
Fixpoint contains_arrow (A : typ) : bool :=
    match A with
    | t_top         => true
    | t_arrow _ _   => true
    | t_union A1 B1 => orb (contains_arrow A1) (contains_arrow B1)
    | t_and A1 B1   => andb (contains_arrow A1) (contains_arrow B1)
    | _             => false
    end.

(* defns sub *)
Reserved Notation "PG |- A <: B" (at level 80, A at next level).
Inductive sub (PG: envp) : typ -> typ -> Prop :=    (* defn sub *)
 | s_top : forall A,
     okenvp PG ->
     wft PG A -> 
     PG |- A <: t_top
 | s_int :
     okenvp PG -> 
     sub PG t_int t_int
 | s_unit :
     okenvp PG -> 
     sub PG t_unit t_unit
 | s_arrow : forall (A1 A2 B1 B2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 ->
     wft PG B1 -> wft PG B2 ->
     sub PG B1 A1 ->
     sub PG A2 B2 ->
     sub PG (t_arrow A1 A2) (t_arrow B1 B2)
 | s_ora : forall (A1 A2 A:typ),
     okenvp PG ->
     wft PG A -> wft PG A1 -> wft PG A2 -> 
     sub PG A1 A ->
     sub PG A2 A ->
     sub PG (t_union A1 A2) A
 | s_orb : forall (A A1 A2:typ),
     okenvp PG ->
     wft PG A -> wft PG A1 -> wft PG A2 ->
     sub PG A A1 ->
     sub PG A (t_union A1 A2)
 | s_orc : forall (A A1 A2:typ),
     okenvp PG ->
     wft PG A -> wft PG A1 -> wft PG A2 ->
     sub PG A A2 ->
     sub PG A (t_union A1 A2)
 | s_anda : forall A A1 A2,
     okenvp PG ->
     wft PG A -> wft PG A1 -> wft PG A2 ->
     sub PG A A1 ->
     sub PG A A2 ->
     sub PG A (t_and A1 A2)
 | s_andb : forall A1 A2 A,
     okenvp PG ->
     wft PG A -> wft PG A1 -> wft PG A2 ->
     sub PG A1 A ->
     sub PG (t_and A1 A2) A
 | s_andc : forall A1 A2 A,
     okenvp PG ->
     wft PG A -> wft PG A1 -> wft PG A2 ->
     sub PG A2 A ->
     sub PG (t_and A1 A2) A
(* s_disj is new subtyping rule for bottom like types.
   FindSubtypes of arrows is empty, so we also require that A has
   no function part; otherwise every A→B would be a subtype of everything. *)
 | s_disj : forall A B,
     okenvp PG ->
     wft PG A -> wft PG B ->
     FindSubtypes PG A = [] ->
     contains_arrow A = false ->
     sub PG A B
 | s_p_refl : forall i,
     okenvp PG ->
     wft PG (t_prim i) ->
     sub PG (t_prim i) (t_prim i)
 | s_p_sub : forall n1 n2,
     okenvp PG ->
     wft PG (t_prim n1) -> wft PG (t_prim n2) ->
     set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n2))) ->
     sub PG (t_prim n1) (t_prim n2)
where "PG |- A <: B" := (sub PG A B) : env_scope.

#[export]
Hint Constructors sub lc_exp ok okt okenvp wft : core.

(* well-formdness properties *)

Lemma subtyping_regular : forall PG A B,
  PG |- A <: B -> okenvp PG /\ wft PG A /\ wft PG B.
Proof.
  induction 1; auto.
Qed.

Lemma findsubtypes_bot : forall PG, FindSubtypes PG t_bot = [].
Proof. reflexivity. Qed.

Lemma contains_arrow_bot : contains_arrow t_bot = false.
Proof. reflexivity. Qed.

#[export]
Hint Resolve findsubtypes_bot contains_arrow_bot : core.

(***********************************)
(****  FindSubtypes Properties  ****)
(***********************************)

Lemma list_empty_decide : forall l : list typ, (l = []) \/ (l <> []).
Proof.
  intros. induction l. auto.
  destruct IHl. right. 
  unfold not. intros. inversion H0.
  unfold not in *.
  right. intros.
  inversion H0.
Defined.

Lemma elem_append_in_list : forall (a : typ) (l : list typ), set_In a (a :: l).
Proof.
  intros. simpl. auto.
Defined.

Lemma elem_append_in_union1 : forall (a1 a2 : typ) (l1 l2 : list typ), 
set_In a1 (a1 :: l1 `union` a2 :: l2).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro1. auto.
Defined.

Lemma elem_append_in_union2 : forall (a1 : typ) (l1 : list typ), 
set_In a1 ([] `union` a1 :: l1).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro2. auto.
Defined.

Lemma union_findsubtypes_empty_elim (PG: envp) : forall l1 A B l2 l3,
l1 = FindSubtypes PG (t_union A B) /\ 
l2 = FindSubtypes PG A /\ l3 = FindSubtypes PG B ->
l1 = [] -> l2 = [] /\ l3 = [].
Proof.
    intros.
    destructs H.
    simpl in H.
    destruct l2.
    destruct l3.
    auto.
    rewrite <- H2 in H.
    rewrite H0 in H.
    rewrite <- H1 in H.
    lets: elem_append_in_union2 t l3.
    rewrite <- H in H3.
    inverts H3.
    rewrite H0 in H.
    rewrite <- H1 in H.
    destruct (FindSubtypes PG B).
    simpl in H. inverts H.
    lets: elem_append_in_union1 t t0 l2 l.
    rewrite <- H in H3.
    inverts H3.
Defined.

Lemma sub_refl (PG: envp) : forall A, wft PG A -> okenvp PG -> sub PG A A.
  inductions A; eauto; intros; inverts H; auto.
Qed.

#[export]
Hint Resolve sub_refl : core.

Lemma sub_or (PG: envp) : forall A B C, sub PG (t_union A B) C ->
  sub PG A C /\ sub PG B C.
Proof.
Admitted.

Lemma sub_and (PG: envp) : forall A B C, sub PG A (t_and B C) -> 
 sub PG A B /\ sub PG A C.
Proof.
Admitted.

Lemma prim_type_in_nats_to_types : forall (A : typ) (l : list nat), 
  set_In A (nats_to_types l) ->
  exists (i : nat), A = t_prim i.
Proof.
  induction l; intros. simpl in H. inverts H.
  simpl in H. destruct H. exists a. auto. auto.
Defined.

Lemma prim_in_domain : forall PG (j:nat),
  set_In j (domain_envp PG) ->
  exists (i:nat), t_prim j = t_prim i.
Proof.
  intros PG j IN. exists*.
Qed.

Lemma prim_type_in : forall (A : typ) PG n, 
  set_In A (FindSubtypes PG (t_prim n)) ->
  exists (i : nat), A = t_prim i.
Proof.
  intros A PG n H. simpl in H.
  destruct H. exists*.
  destruct (get_all_subtypes PG (t_prim n)); intros. simpl in H.
  inverts H.
  apply prim_type_in_nats_to_types in H. destruct H.
  exists*.
Qed.

(*

----- IMPORTANT -----

*)

Lemma arrow_in_top_bot (PG: envp) : forall A B C, 
set_In (t_arrow A B) (FindSubtypes PG C) ->
False.
Proof.
Admitted.

Lemma prim_subtypes_not_empty : forall PG i,
  okenvp PG -> wft PG (t_prim i) -> 
  FindSubtypes PG (t_prim i) <> [].
Proof.
  introv OK WFT.
  unfold not. intros.
  simpl in H.
  induction (get_all_subtypes PG (t_prim i)) as [| i1 l IHl].
  inverts H.
  simpl in H. inverts H.
Qed.

Lemma i_in_nat_to_types : forall i PG,
  set_In i (domain_envp PG) ->
  set_In (t_prim i) (nats_to_types (domain_envp PG)).
Proof.
  introv IN.
  induction (domain_envp PG). inverts IN.
  simpl in IN. destruct IN.
  simpl. left. subst~.
  simpl. right. apply* IHl.
Qed.

Lemma ord_in_findsubtypes (PG: envp) : forall A B,
  okenvp PG -> wft PG A -> wft PG B ->
  Ord A -> sub PG A B -> set_In A (FindSubtypes PG B) \/ 
  (exists t1 t2, A = t_arrow t1 t2).
Proof.
Admitted.

Lemma ord_sub_findsubtypes_not_empty (PG: envp) : forall A B, 
Ord A -> sub PG A B ->
(forall t1 t2, A <> t_arrow t1 t2) ->
(FindSubtypes PG B) <> [].
Proof.
Admitted.

Lemma list_append_findsubtypes_in (PG: envp) : forall t l A, (t :: l) = FindSubtypes PG A ->
set_In t (FindSubtypes PG A).
Proof.
  intros.
  rewrite <- H.
  apply elem_append_in_list.
Defined.

Lemma elem_in_findsubtypes_ord (PG: envp) : forall A B,
okenvp PG -> wft PG A -> wft PG B ->
(set_In B (FindSubtypes PG A)) -> Ord B.
Proof.
  introv OK WFT1 WFT2 IN.
  inductions A.
  - simpl in IN;
    destruct IN as [H1 | [H1 | H1]];
    try solve [rewrite <- H1; auto; inversion H1].
    apply prim_type_in_nats_to_types in H1.
    destruct H1 as [i H1]. rewrite~ H1.
  - simpl in IN;
    destruct IN; try rewrite <- H; auto;
    inversion H.
  - simpl in IN; inversion IN.
  - simpl in IN;
    destruct IN; try rewrite <- IN; auto;
    inversion H; auto.
  - inverts WFT1. simpl in IN.
    apply set_union_elim in IN. destruct IN. 
    apply IHA1; auto. 
    apply IHA2; auto.
  - inverts WFT1. simpl in IN.
    apply set_inter_elim1 in IN.
    apply IHA1; auto.
  - simpl in IN. inverts* IN.
  - apply prim_type_in in IN. 
    destruct IN as [i X]. subst~. (*need a lemma here*)
    (* should p type be an orinary type? *)
Qed.

Lemma prim_in_nat_to_types : forall i PG,
  set_In (t_prim i) (nats_to_types (domain_envp PG)) ->
  set_In i (domain_envp PG).
Proof.
  introv IN.
  induction (domain_envp PG). inverts IN.
  simpl in IN. destruct IN. inverts H.
  simpl. left. subst~.
  simpl. right. apply* IHl.
Qed.

(*

---- IMPORTANT PROPERTIES

*)

Lemma allsubtypes_in_to_domain_nat : forall PG A,
  forall i, set_In i (get_all_subtypes PG A) ->
  set_In i (domain_envp PG).
Proof.
  induction PG; introv IN1.
  - inverts IN1.
  - destruct a as [C D].
    simpl in *. destruct (eq_dec_nat C C).
    destruct (eq_dec A D).
    + simpl in IN1.
      destruct IN1.
      * auto.
      * specialize (IHPG A i).
        forwards: IHPG H.
        auto.
    + simpl in IN1.
      destruct (issupertype PG D A).
      simpl in IN1. destruct IN1.
      auto.
      apply IHPG in H; auto.
      apply IHPG in IN1; auto.
    + contradiction.
Qed.

Lemma nat_to_types_iff : forall l1 l2,
  (nats_to_types (l1 ++ l2)) = (nats_to_types l1) ++ (nats_to_types l2).
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. specialize (IHl1 l2).
    rewrite IHl1. auto.
Qed.

Lemma allsubtypes_in_to_domain : forall PG A,
  forall B, set_In B (nats_to_types (get_all_subtypes PG A)) ->
  set_In B (nats_to_types (domain_envp PG)).
Proof.
  induction PG; introv IN1.
  - inverts IN1.
  - simpl in *. destruct a as [C D].
    destruct (eq_dec_nat C C).
    destruct (eq_dec A D); simpl in IN1.
    + destruct IN1.
      * rewrite <- H. simpl. auto.
      * apply IHPG in H. auto.
    + destruct (issupertype PG D A).
      * simpl in IN1. destruct IN1.
        simpl. auto.
        apply IHPG in H. auto.
      * apply IHPG in IN1. auto.
    + contradiction. 
Qed.


Lemma wft_p_in_findsubtypes : forall PG A B,
  okenvp PG -> wft PG A ->
  set_In B (FindSubtypes PG A) -> wft PG B.
Proof.
  introv OK WFT IN.
  induction A; intros; simpl in IN.
  - destruct IN as [IN | [IN | IN]]; subst~.
    forwards* (i&EQ): prim_type_in_nats_to_types IN. subst.
    apply prim_in_nat_to_types in IN; auto.
  - destruct IN as [IN | IN]; subst~; inverts IN.
  - inverts IN.
  - clear IHA1 IHA2.
    inversion IN.
  - inverts WFT. apply set_union_elim in IN. destruct~ IN.
  - inverts WFT. apply set_inter_elim1 in IN; auto.
  - destruct IN as [IN | IN]; subst~. inverts IN.
  - destruct IN as [IN | IN]; subst~.
    forwards* (i&EQ): prim_type_in_nats_to_types IN.
    subst.
    apply allsubtypes_in_to_domain in IN; auto.
    apply prim_in_nat_to_types in IN. auto.
Qed.

Lemma inter_not_empty_elim (PG: envp) : forall A l,
okenvp PG ->
wft PG A ->
l = FindSubtypes PG A ->
l <> [] ->
set_In t_int l \/ 
set_In (t_arrow t_top t_bot) l \/
set_In t_unit l \/
exists i, set_In (t_prim i) l.
Proof.
  introv OK WFT EQ NEQ.
  destruct l.
  contradiction.
  lets H: elem_append_in_list t l.
  rewrite EQ in H.
  lets* H1: elem_in_findsubtypes_ord A t OK WFT.
  forwards* WFTt: wft_p_in_findsubtypes H.
  (*need a lemma here*)
  lets H2: H1 WFTt H. 
  lets H2': H2.
  clear H1.
  induction H2; auto.
 - left. apply elem_append_in_list.
 - apply arrow_in_top_bot in H. contradiction.
 - right. right. left. apply elem_append_in_list.
 - right. right. right.
   exists i. apply elem_append_in_list.
Qed.

Lemma not_in (PG: envp) : forall A B,
okenvp PG -> wft PG (t_and A B) -> 
not (set_In t_int (FindSubtypes PG (t_and A B))) /\
not (set_In (t_arrow t_top t_bot) (FindSubtypes PG (t_and A B))) /\
not (set_In t_unit (FindSubtypes PG (t_and A B))) /\
(forall i, not (set_In (t_prim i) (FindSubtypes PG (t_and A B)))) ->
(FindSubtypes PG (t_and A B)) = [].
Proof.
  introv OK WFT NIN.
  lets OR: list_empty_decide (FindSubtypes PG (t_and A B)).
  destruct OR. 
  - rewrite H. auto.
  - destructs NIN. 
    eapply inter_not_empty_elim with (A:=(t_and A B)) in H; eauto.
    destruct H as [H5 | [H5 | [H5 | H5]] ].
    contradiction.
    contradiction.
    contradiction.
    destruct H5 as [i1 H5].
    specialize (H3 i1).
    contradiction.
Qed.

Lemma demorgan : forall P Q R S : Prop, 
~ (P \/ Q \/ R \/ S) -> ~ P /\ ~ Q /\ ~ R /\ ~ S.
Proof.
  intros.
  unfold not in *.
  splits; intros; apply H; auto.
Defined.

Lemma elem_in_findsubtypes_sub (PG: envp) : forall A B,
okenvp PG -> wft PG A -> wft PG B ->
(set_In B (FindSubtypes PG A)) -> sub PG B A.
Proof.
  introv OK WFT1 WFT2 IN.
  inductions A.
  - simpl in IN.
    destruct~ IN as [H | [H | H] ]; 
    try solve [rewrite <- H; auto].
  - simpl in IN.
    destruct IN. rewrite <- H. auto.
    inversion H.
  - simpl in IN. inversion IN.
  - simpl in IN. inversion IN.
  - simpl in IN. inverts WFT1.
    apply set_union_elim in IN. destruct~ IN. 
  - simpl in IN. inverts WFT1.
    apply* s_anda.
    apply set_inter_elim1 in IN.
    apply IHA1; auto.
    apply set_inter_elim2 in IN. 
    apply IHA2; auto.
  - inverts* IN. inverts H.
  - simpl in IN. destruct IN. subst~.
    forwards* (i&EQ): prim_type_in_nats_to_types H.
    subst~.
Qed.


Lemma findsubtypes_empty_not_ord (PG: envp) : forall A B,
okenvp PG -> wft PG A -> wft PG B ->
FindSubtypes PG A = [] -> sub PG B A ->
(forall t1 t2, B <> t_arrow t1 t2) -> not (Ord B).
Proof.
Admitted.

Lemma findsubtypes_not_empty (PG: envp) : forall A,
FindSubtypes PG A <> [] -> exists B, set_In B (FindSubtypes PG A).
Proof.
  intros.
  destruct (FindSubtypes PG A).
  contradiction.
  lets: elem_append_in_list t l.
  exists t. auto.
Defined.

(*

----- IMPORTANT -----

Important Properties

*)

Lemma in_domain_app : forall PG,
  okenvp PG -> forall i1 i2 A, set_In i1 (domain_envp (PG ++ [(i2, A)])) ->
  i1 = i2 \/ set_In i1 (domain_envp PG).
Proof.
  introv OK.
  unfold domain_envp; intros.
  rewrite map_app in H.
  apply in_app_or in H.
  destruct H. right*.
  simpl in H. destruct H.
  left*. inverts H.
Defined.

Lemma wft_prim_inversion : forall i PG,
  wft PG (t_prim i) -> In i (map fst PG).
Proof.
  introv OK.
  inverts OK. unfold domain_envp in H0. auto.
  Defined.

Lemma okenvp_wft : forall PG,
  okenvp PG -> forall i, set_In i (domain_envp PG) -> wft PG (t_prim i).
Proof.
  intros.
  apply wft_prim.
  auto.
Defined.

Lemma getsubtypes_inversion_temp1 : forall PG,
  forall n1 i A B,
  set_In n1 (get_all_subtypes ((i, A) :: PG) B) ->
  (n1 = i) \/ set_In n1 (get_all_subtypes PG B).
Proof.
  induction PG; intros.
  - simpl in H. destruct (eq_dec B A).
    destruct (eq_dec_nat i i); simpl in H.
    destruct H. auto. inverts H.
    contradiction.
    destruct (eq_dec_nat i i); simpl in H.
    inverts H. inverts H.
  - destruct a as [C D].
    simpl.
    simpl in H. destruct (eq_dec B D).
    destruct (eq_dec B A).
    destruct  (eq_dec_nat i i).
    simpl in H.
    destruct H; auto.
    contradiction.
    destruct  (eq_dec_nat i i).
    destruct  (eq_dec_nat C C).
    simpl in H. simpl.
    destruct (eq_dec A (t_prim C)).
    simpl in H. destruct H; auto.
    subst.
    destruct (issupertype PG A D).
    simpl in H. destruct H; auto.
    simpl in H. destruct H; auto.
    contradiction.
    contradiction.
    destruct ((eq_dec_nat i i)).
    destruct (eq_dec B A).
    simpl in H.
    destruct H. auto.
    destruct (eq_dec_nat C C).
    simpl in H.
    destruct (issupertype PG D B).
    simpl in H.
    simpl.
    destruct H; auto.
    simpl. auto.
    contradiction.
    simpl in H.
    destruct ((eq_dec_nat C C)); simpl in H.
    destruct (eq_dec A (t_prim C)); simpl in H.
    destruct (issupertype PG D B).
    simpl in H. destruct H; auto.
    simpl. auto.
    simpl. destruct (issupertype PG A B); simpl in H.
    destruct H. auto.
    destruct (issupertype PG D B).
    simpl in H. simpl. destruct H; auto. auto.
    destruct (issupertype PG D B); simpl; simpl in H.
    destruct H; auto. auto.
    contradiction.
    contradiction.
Qed. 


Lemma demorgan2 : forall P Q, ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not in *; intros.
  splits; intros.
  apply H; auto.
  apply H; auto.
Qed.


Lemma getsubtypes_inversion_temp12 : forall PG,
  forall n1 i A B,
  set_In n1 (get_all_subtypes ((i, A) :: PG) B) ->
  ((n1 = i) /\ (issupertype ((i, A) :: PG) (t_prim i) B = true) ) 
  \/ set_In n1 (get_all_subtypes PG B).
Proof.
   destruct PG; intros.
  - simpl in H. destruct (eq_dec B A).
    destruct (eq_dec_nat i i); simpl in H.
    destruct H. left. split. auto.
    subst. simpl.
    destruct (eq_dec A A).
    destruct (eq_dec_nat n1 n1); simpl.
    auto. contradiction.
    contradiction.
    inverts H. contradiction.
    destruct (eq_dec_nat i i); simpl in H.
    inverts H. inverts H.
  - destruct p as [j C].
    simpl.

    simpl in H. destruct (eq_dec B C).

    destruct (eq_dec B A).
    destruct  (eq_dec_nat i i).
    simpl in H.
    destruct H; auto.
    contradiction.
    destruct  (eq_dec_nat j j).
    destruct  (eq_dec_nat i j).
    simpl in H. simpl.
    destruct (eq_dec A (t_prim j)).
    destruct (eq_dec_nat i i); simpl in *.
    destruct H; auto.
    contradiction.
    destruct (eq_dec_nat i i); simpl in *.
    subst.
    destruct (issupertype PG A C).
    simpl in H. destruct H; auto.
    simpl in H. destruct H; auto.
    contradiction.
    destruct ((eq_dec_nat i i)); simpl in H.
    destruct (eq_dec A (t_prim j)); simpl in *.
    destruct H; auto.
    subst.
    destruct (issupertype PG A C); simpl in *.
    destruct H; auto.
    destruct H; auto.
    contradiction.
    contradiction.

    destruct (eq_dec B A).
    destruct (eq_dec_nat i i); simpl in *.
    destruct ((eq_dec_nat j j)); simpl in *.
    destruct H; auto.
    contradiction.
    contradiction.

    destruct (eq_dec_nat i i); simpl in *.
    destruct (eq_dec_nat j j); simpl in *.
    destruct (eq_dec A (t_prim j)); simpl in *.
    destruct (issupertype PG C B); simpl in *.
    destruct H; auto.
    auto.
    destruct (issupertype PG A B); simpl in *.
    destruct H; auto.
    destruct (issupertype PG C B); simpl in *.
    destruct H; auto.
    auto.
    contradiction.
    contradiction.
Qed.

Lemma subpertypes_inversion : forall PG,
  forall i n,
  issupertype PG (t_prim i) (t_prim n) = true ->
  set_In i (get_all_subtypes PG (t_prim n)).
Proof.
  induction PG; introv EQ.
  - inverts EQ.
  - destruct a as [j A].
    destruct A; simpl in *.
   + (*case top*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_top (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_top (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case int*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_int (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_int (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case bot*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_bot (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_bot (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case arrow*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_arrow A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_arrow A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case union*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_union A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_union A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case intersection*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_and A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_and A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case unit*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_unit (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_unit (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (* case P *)
     destruct (eq_dec_nat n n0); simpl in *.
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     auto.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     forwards*: IHPG EQ.
     contradiction.
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_prim n0) (t_prim n)); simpl.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_prim n0) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
Defined.

Lemma not_in_domain_issupertype_false : forall PG,
  okenvp PG ->
  forall i, ~ set_In i (domain_envp PG) -> 
  forall A, issupertype PG A (t_prim i)  = false.
Proof.
  introv OK.
  induction OK; intros.
  - simpl. auto.
  - simpl in H1.
    apply demorgan2 in H1. destruct H1.
    destruct A; simpl; destruct (eq_dec A0 (t_prim i)); simpl;
    (*all cases except P*)
    try solve [
      forwards*: IHOK H2 t_top;
      forwards*: IHOK H2].
    (*case P*)
    destruct (eq_dec_nat i0 n); simpl.
    subst. inverts H. contradiction.
    forwards*: IHOK H2 (t_prim n).
Defined.

Lemma not_in_domain_subtypes_empty : forall PG,
  okenvp PG -> forall i,
  ~ set_In i (domain_envp PG) ->
  (get_all_subtypes PG (t_prim i)) = [].
Proof.
  introv OK.
  induction OK; intros.
  - simpl. auto.
  - simpl in H1.
    apply demorgan2 in H1. destruct H1.
    destruct A;
    simpl; destruct (eq_dec_nat i i); simpl; try solve [contradiction].
    + forwards* FALSE: not_in_domain_issupertype_false OK t_top;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK t_int;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK t_bot;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_arrow A1 A2);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_union A1 A2);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_and A1 A2);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK t_unit;
      rewrite* FALSE.
    + (*case P*)
      destruct (eq_dec_nat i0 n); simpl.
      subst. inverts H. contradiction.
      forwards FALSE: not_in_domain_issupertype_false OK H2 (t_prim n).
      rewrite FALSE. auto.
Defined.

Lemma issupertype_weakening : forall PG n1 n2,
  issupertype PG (t_prim n1) (t_prim n2) = true ->
  forall i A,
  ~ set_In i (domain_envp PG) ->
  issupertype ((i, A) :: PG) (t_prim n1) (t_prim n2) = true.
Proof.
  introv EQ NOTIN.
  destruct A;
  try (simpl; destruct (eq_dec_nat n1 i); subst; simpl; auto);
  try solve [apply subpertypes_inversion in EQ;
  apply allsubtypes_in_to_domain_nat in EQ;
  contradiction].
Qed.


Lemma set_in_weakening : forall PG n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  forall i A,
  set_In n1 (get_all_subtypes ((i, A) :: PG) (t_prim n2)).
Proof.
  destruct PG; intros.
  - simpl in H. inverts H.
  - destruct p as [j C].
    destruct A.
   + (*case A = top*)
     destruct C.

     * (*case top top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      simpl.
      simpl in H. auto. auto.
      contradiction.
      contradiction.

    * (*case top int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG t_int (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_int (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    *  (*case top bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case top intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = int*)
     destruct C.

     * (*case int top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case int int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case int bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case int intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.
      
   + (*case A = bot*)
     destruct C.

     * (*case bot top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case bot int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case bot bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case bot arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case bot intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = arrow*)
     destruct C.

     * (*case arrow top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case arrow int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case arrow bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case arrow arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case arrow union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case arrow intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = union*)
     destruct C.

     * (*case union top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case union int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case union bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case union arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case union union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    * (*case union intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = intersection*)
     destruct C.

     * (*case intersection top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case intersection bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case intersection P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = unit*)
     destruct C.

    * (*case unit top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case unit int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_unit (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case unit bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case unit intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case unit P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = P*)
     destruct C.

    * (*case P top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P bot*)   
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P intersection*) 
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P P*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat n2 n0); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      (*repeatition started in reverse*)

      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      (*repeatition from (eq_dec_nat i j) *)

      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      (**** repeatition from (eq_dec_nat n2 n0) *****)

      destruct (eq_dec_nat n2 n0); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      (*repeatition started in reverse*)

      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      (*repeatition from (eq_dec_nat i j) *)

      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.
Defined.


Lemma issupertype_top_p : forall PG n,
  issupertype PG (t_top) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_int_p : forall PG n,
  issupertype PG (t_int) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_bot_p : forall PG n,
  issupertype PG (t_bot) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_unit_p : forall PG n,
  issupertype PG (t_unit) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_arrow_p : forall PG A B n,
  issupertype PG (t_arrow A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_union_p : forall PG A B n,
  issupertype PG (t_union A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_inter_p : forall PG A B n,
  issupertype PG (t_and A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. apply IHPG.
Defined.

Lemma issupertype_inverse : forall PG i A n,
  issupertype ((i, A) :: PG) (t_prim i) (t_prim n) = true ->
  A = (t_prim n) \/ issupertype PG A (t_prim n) = true.
Proof.
  destruct PG; intros.
  - destruct A; simpl in *;
    try solve [destruct (eq_dec_nat i i); simpl in *;
    inverts H].
    destruct (eq_dec_nat n n0); simpl in *.
    destruct (eq_dec_nat i i); simpl in *.
    auto. contradiction.
    destruct (eq_dec_nat i i); simpl in *.
    inverts H.  contradiction.
  - destruct p as [j C].
    destruct A;
    (*all cases except P*)
    destruct C; simpl in *; 
    try solve [
    destruct (eq_dec_nat i j); simpl in *;
    destruct (eq_dec_nat i i); simpl in *;
    auto; contradiction;
    destruct (eq_dec_nat i i); simpl in *;
    auto; contradiction].

    + (*case A = top, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = int, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = bot, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = arrow, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = union, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = intersection, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = unit, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = P, C = P*)
      destruct (eq_dec_nat n n1); simpl in *.
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
Defined.

Lemma get_all_subtypes_issupertype : forall PG,
  okenvp PG ->
  forall n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  issupertype PG (t_prim n1) (t_prim n2) = true.
Proof.
  introv OK.
  induction OK; intros.
  - simpl in H. inverts H.
  - destruct A.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_top_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_int_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_bot_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_arrow_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_union_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_inter_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_unit_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + apply getsubtypes_inversion_temp12 in H1; auto.
      destruct H1. destruct  H1.
      subst. auto.
      apply IHOK in H1.
      forwards: issupertype_weakening H1 (t_prim n) H0.
      auto.
Qed.

Lemma n_in_semi_trans : forall PG,
  okenvp PG ->
  forall n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  forall i,
  set_In i (get_all_subtypes ((i, t_prim n1) :: PG) (t_prim n2)).
Proof.
  intros.
  simpl.
  destruct (eq_dec_nat n2 n1); simpl.
  destruct (eq_dec_nat i i); simpl.
  auto.
  contradiction.
  destruct (eq_dec_nat i i); simpl.
  apply get_all_subtypes_issupertype in H0; auto.
  rewrite H0. simpl. auto.
  contradiction.
Defined.

Lemma p_in_sub_nat62 : forall PG,
  okenvp PG ->
  forall n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  forall n3, set_In n2 (get_all_subtypes PG (t_prim n3)) ->
  set_In n1 (get_all_subtypes PG (t_prim n3)).
Proof.
  introv OK.
  inductions OK; intros.
  - inverts H0.
  - apply getsubtypes_inversion_temp12 in H1. destruct H1.
    destruct H1.
    apply getsubtypes_inversion_temp12 in H2. destruct H2.
    destruct H2.
    subst.
    apply subpertypes_inversion; auto.

    subst.
    forwards*: issupertype_inverse H3.
    destruct H1. subst.
    apply n_in_semi_trans; auto.
    destruct A.
    rewrite issupertype_top_p in H1. inverts H1.
    rewrite issupertype_int_p in H1. inverts H1.
    rewrite issupertype_bot_p in H1. inverts H1.
    rewrite issupertype_arrow_p in H1. inverts H1.
    rewrite issupertype_union_p in H1. inverts H1.
    rewrite issupertype_inter_p in H1. inverts H1.
    rewrite issupertype_unit_p in H1. inverts H1.
    forwards*: subpertypes_inversion H1.
    forwards*: IHOK H4 H2.
    apply n_in_semi_trans; auto.
    apply getsubtypes_inversion_temp12 in H2. destruct H2.
    destruct H2. subst.
    apply not_in_domain_subtypes_empty in H0; auto.
    rewrite H0 in H1. inverts H1.
    forwards*: IHOK H1 H2.
    apply set_in_weakening. auto.
Defined.

Lemma nats_to_types_iff : forall i l,
  set_In i l <-> set_In (t_prim i) (nats_to_types l).
Proof.
  split.
  - gen i. induction l; intros.
    inverts H.
    simpl. simpl in H.
    destruct H.
    auto. auto.
  - gen i. induction l; intros.
    inverts H.
    simpl in H. simpl.
    destruct H.
    inverts H. auto.
    forwards*: IHl H.
Qed.

Lemma p_in_sub : forall PG n1 n2,
  okenvp PG ->
  set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n2))) ->
  forall n3, set_In (t_prim n2) (nats_to_types (get_all_subtypes PG (t_prim n3))) ->
  set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n3))).
Proof.
  intros.
  apply nats_to_types_iff.
  apply nats_to_types_iff in H0.
  apply nats_to_types_iff in H1.
  eapply p_in_sub_nat62 with (n2:=n2); auto.
Qed.


Lemma set_in_sub (PG: envp) : forall A x, set_In x (FindSubtypes PG A) ->
forall B, sub PG A B -> set_In x (FindSubtypes PG B).
Proof.
Admitted.

Lemma findsubtypes_sub_empty (PG: envp) : forall A1 A2 B,
FindSubtypes PG (t_and A1 A2) = [] -> 
sub PG B (t_and A1 A2) -> FindSubtypes PG B = [].
Proof.
    intros.
    lets: list_empty_decide (FindSubtypes PG B).
    destruct H1. auto.
    lets: findsubtypes_not_empty B H1.
    destruct H2.
    lets: set_in_sub B x H2 (t_and A1 A2) H0.
    rewrite H in H3. inverts H3.
Defined.

(********************************)
(*******  sub Properties  *******)
(********************************)

Lemma sub_transitivity (PG: envp) : forall B A C, PG |- A <: B -> 
 sub PG B C -> sub PG A C.
Proof.
Admitted.
(*
induction B; intros;
generalize H0 H; clear H0; clear H; generalize A; clear A.
- (*case top*)
  intros; inductions H0; try solve [inverts H4;  eauto]. auto.
  inverts* H3. 
- (*case int*)
  intros; inductions H; eauto; try solve [inverts* H0].
- (*case bot*)
  intros; inductions H; eauto; try solve [inverts* H0].
- (*case A -> B*)
  induction C; intros;
  forwards*(OK&WFT1&WFT2): subtyping_regular H0;
  forwards*(?&WFT3&WFT4): subtyping_regular H;
  try solve [inverts H0; inverts H5; auto].
  clear IHC1 IHC2.
  inductions H; eauto. clear IHsub1 IHsub2.
  inverts* H0.
- (*case union*)
  intros. apply sub_or in H0. destruct H0.
  forwards* (OK&WFTA&WFT): subtyping_regular H. inverts WFT.
  forwards* (?&?&WFTC): subtyping_regular H0. clear H3 H2.
  inductions H; eauto.
- (*case intersection*)
  intros. apply sub_and in H. destruct H.
  forwards* (OK&WFT1&WFT2): subtyping_regular H0. inverts WFT1.
  forwards* (?&WFTA&?): subtyping_regular H.
  clear H2 H3.
  inductions H0; eauto.
  assert (sub PG A (t_and B1 B2)) by auto.
  apply* s_disj.
  apply findsubtypes_sub_empty with (A1:=B1) (A2:=B2); auto.
 - (*case unit*)
   intros. inductions H0; try solve [inverts* H1; inverts* H4]; auto.
   forwards*: IHsub1.
   forwards*: IHsub2.
   forwards*: subtyping_regular H3.
 - (*case prim*)
   intros. inductions H0; eauto. inverts* H1.
   forwards*: IHsub. inverts* H4.
   forwards*: IHsub. inverts* H4.
   forwards*: IHsub1.
   forwards*: IHsub2.
   inverts* H3.
   forwards*: subtyping_regular H3.
   inductions H3; eauto.
   forwards*: IHsub1 n.
   forwards*: p_in_sub H6 H2.
Defined.
*)

(* Bottom Type Least Subtype *)

(* Lemma 27 *)

Lemma bot_sub_all (PG: envp) : forall A, okenvp PG -> wft PG A -> sub PG t_bot A.
Proof.
  intros.
  dependent induction A; eauto.
Defined.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec (PG: envp) A B := forall C, Ord C -> not (sub PG C (t_and A B)).
Notation "G |- A *s B" := (DisjSpec G A B) (at level 80, A at next level).

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

Inductive DisjAlgo (PG: envp) : typ -> typ -> Prop :=
| da_nfun_l : forall A B,
    (FindSubtypes PG A `inter` FindSubtypes PG B) = [] ->
    FunRange A = t_bot ->
    DisjAlgo PG A B
| da_nfun_r : forall A B,
    (FindSubtypes PG A `inter` FindSubtypes PG B) = [] ->
    FunRange B = t_bot ->
    DisjAlgo PG A B
| da_peel : forall A B,
    (FindSubtypes PG A `inter` FindSubtypes PG B) = [] ->
    DisjAlgo PG (FunRange A) (FunRange B) ->
    DisjAlgo PG A B.
Notation "G |- A *a B" := (DisjAlgo G A B) (at level 80, A at next level).

Lemma Disj_soundness (PG: envp) : forall A B,
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *a B -> PG |- A *s B.
Proof.
Admitted.

Lemma Disj_completeness (PG: envp) : forall A B, okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *s B -> PG |- A *a B.
Proof.
Admitted.

(* Disjont Intersections are Bottom-Like *)

(* Lemma 28 *)

Lemma disj_bot_like (PG: envp) : forall A B,
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *a B -> sub PG (t_and A B) t_bot.
Proof.
Admitted.