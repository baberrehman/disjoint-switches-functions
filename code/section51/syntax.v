(*

-> Section 5.1 in paper
-> Union Types + Null + Intersection Types
-> Nominal types
-> Parametric Polymorphism

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.
Require Import Coq.Strings.String.

(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ
 | t_unit : typ
 | t_bvar  : nat -> typ
 | t_fvar  : var -> typ
 | t_all   : typ -> typ -> typ
 | t_prim  : nat -> typ.

Inductive exp : Set :=  (*r expression *)
 | e_bvar  : nat -> exp
 | e_fvar  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : typ -> typ -> exp -> exp (*r λ(x:A):B. e *)
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp
 | e_tabs   : typ -> exp -> exp
 | e_tapp   : exp -> typ -> exp
 | e_new    : nat -> exp.


(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_top         => t_top
  | t_int         => t_int
  | t_bot         => t_bot
  | t_arrow T1 T2 => t_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_union T1 T2 => t_union (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_and T1 T2   => t_and (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_unit        => t_unit
  | t_bvar J      => If K = J then U else (t_bvar J)
  | t_fvar X      => t_fvar X
  | t_all T1 T2   => t_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | t_prim i      => t_prim i
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i    => e_bvar i
  | e_fvar x    => e_fvar x
  | e_lit i     => e_lit i
  | e_abs A B e1 => e_abs (open_tt_rec K U A) (open_tt_rec K U B) (open_te_rec K U e1)
  | e_app e1 e2 => e_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | e_typeof e1 T1 e2 T2 e3 => e_typeof (open_te_rec K U e1) (open_tt_rec K U T1) (open_te_rec K U e2) (open_tt_rec K U T2) (open_te_rec K U e3)
  | e_null      => e_null
  | e_tabs V e1 => e_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | e_tapp e1 V => e_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | e_new i     => e_new i
  end.

Definition open_te t U := open_te_rec 0 U t.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_bvar nat) => If (k = nat) then e_5 else (e_bvar nat)
  | (e_fvar x) => e_fvar x
  | (e_lit i5) => e_lit i5
  | (e_abs A B e) => e_abs A B (open_ee_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_ee_rec k e_5 e1) (open_ee_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_ee_rec k e_5 e) A (open_ee_rec (S k) e_5 e1) B (open_ee_rec (S k) e_5 e2)
  | e_null    => e_null
  | e_tabs A e => e_tabs A (open_ee_rec k e_5 e)
  | e_tapp e A => e_tapp (open_ee_rec k e_5 e) A
  | e_new i    => e_new i
end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (open_tt T (t_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (t_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type t_top
  | type_int :
      type t_int
  | type_bot :
      type t_bot
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (t_arrow T1 T2)
  | type_union : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_union T1 T2)
  | type_and : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_and T1 T2)
  | type_var : forall X,
      type (t_fvar X)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (t_all T1 T2)
  | type_unit : type t_unit
  | type_prim : forall i, 
      type (t_prim i).

(** Terms as locally closed pre-terms *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     lc_exp (e_fvar x)
 | lc_e_lit : forall i5,
     lc_exp (e_lit i5)
 | lc_e_abs : forall (L:vars) (A B:typ) (e:exp),
      type A -> type B ->
      ( forall x , x \notin L -> lc_exp (open_ee e (e_fvar x)) )  ->
     lc_exp (e_abs A B e)
 | lc_e_app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     lc_exp (e_app e1 e2)
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     lc_exp e ->
     type A ->
     type B ->
     ( forall x , x \notin  L -> lc_exp ( open_ee e1 (e_fvar x)) ) ->
     ( forall x , x \notin  L -> lc_exp ( open_ee e2 (e_fvar x)) ) ->
     lc_exp (e_typeof e A e1 B e2)
 | lec_e_null :
     lc_exp e_null
 | lc_e_tabs : forall L V e1,
      type V ->
      (forall X, X \notin L -> lc_exp (e1 open_te_var X)) ->
      lc_exp (e_tabs V e1)
 | lc_e_tapp : forall e1 V,
      lc_exp e1 ->
      type V ->
      lc_exp (e_tapp e1 V)
 | lc_e_new : forall i,
       lc_exp (e_new i).

(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 Inductive bind : Set :=
 | bind_disj : typ -> bind
 | bind_typ  : typ -> bind.

Notation "X ~*: T" := (X ~ bind_disj T)
 (at level 23, left associativity) : env_scope.

Notation "x ~: T" := (x ~ bind_typ T)
(at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. **)

Definition env := LibEnv.env bind.

(***************************
 *** Equality for types ****
 ***************************)

Lemma eq_dec_nat : forall (n1 n2 : nat), {n1 = n2} + {n1 <> n2}.
Proof.
  decide equality.
Defined.

Lemma eq_dec_var : forall (x y : var), {x = y} + {x <> y}.
Proof.
  intros.
  case_if_eq x y; auto.
Defined.

Lemma eq_dec : forall (x y:typ), {x = y} + {x <> y}.
Proof.
 decide equality; auto.
 apply eq_dec_nat.
 apply eq_dec_var.
 apply eq_dec_nat.
Defined.

Notation "l1 `union` l2" := (set_union eq_dec l1 l2) (at level 80).
Notation "l1 `inter` l2" := (set_inter eq_dec l1 l2) (at level 80).
Notation "l1 `dif` l2" := (set_diff eq_dec l1 l2) (at level 80).

(*******************************)
(*** Environment for P types ***)
(*******************************)


Definition envp := list (nat * typ).

(* Definition PG : envp. *)

Definition domain_envp (l : envp) : list nat := map fst l.

Definition range_envp (l : envp) : list typ := map snd l.

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

Fixpoint nats_to_types (l : list nat) {struct l} : (list typ) :=
  match l with
  | [] => []
  | a :: xs => [t_prim a] ++ (nats_to_types xs)
  end.

(* Ground Types *)

Inductive groundtype : typ -> Prop :=
  | gtype_top :
      groundtype t_top
  | gtype_int :
      groundtype t_int
  | gtype_bot :
      groundtype t_bot
  | gtype_arrow : forall T1 T2,
      groundtype (t_arrow T1 T2)
  | gtype_union : forall T1 T2,
      groundtype T1 ->
      groundtype T2 ->
      groundtype (t_union T1 T2)
  | gtype_and : forall T1 T2,
      groundtype T1 ->
      groundtype T2 ->
      groundtype (t_and T1 T2)
  | gtype_all : forall T1 T2,
      groundtype T1 ->
      groundtype (t_all T1 T2)
  | gtype_unit : 
      groundtype t_unit
  | gtype_prim : forall i, 
      groundtype (t_prim i).

 (** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  disjointness relation in E. This predicates implies
  that T is a type *)

Inductive wft (PG:envp) : env -> typ -> Prop :=
  | wft_top : forall E, 
      wft PG E t_top
  | wft_int : forall E,
      wft PG E t_int
  | wft_bot : forall E,
      wft PG E t_bot
  | wft_arrow : forall E T1 T2,
      wft PG E T1 -> 
      wft PG E T2 -> 
      wft PG E (t_arrow T1 T2)
  | wft_union : forall E T1 T2,
      wft PG E T1 ->
      wft PG E T2 ->
      wft PG E (t_union T1 T2)
  | wft_and : forall E T1 T2,
      wft PG E T1 ->
      wft PG E T2 ->
      wft PG E (t_and T1 T2)
  | wft_var : forall U E X,
      (* groundtype U -> *)
      binds X (bind_disj U) E ->
      wft PG E (t_fvar X) 
  | wft_all : forall L E T1 T2,
      wft PG E T1 ->
      groundtype T1 ->
      (forall X, X \notin L -> 
        wft PG (E & X ~*: T1) (T2 open_tt_var X)) ->
      wft PG E (t_all T1 T2)
  | wft_unit : forall E,
      wft PG E t_unit
  | wft_prim : forall (i : nat) E,
      set_In i (domain_envp PG) ->
      wft PG E (t_prim i).
  
  (** A environment E is well-formed if it contains no duplicate bindings
    and if each type in it is well-formed with respect to the environment
    it is pushed on to. *)

Inductive okenvp : envp -> Prop :=
  | okenvp_empty :
      okenvp []
  | okenvp_sub : forall (PG:envp) (A:typ) (i:nat) E,
     okenvp PG ->
     wft PG E A ->
     ~( set_In i (domain_envp PG)) ->
     okenvp ((i, A) :: PG).
  
Inductive okt (PG : envp) : env -> Prop :=
  | okt_empty :
      okt PG empty
  | okt_typ : forall E x T,
      okt PG E ->
      wft PG E T -> 
      x # E -> 
      okt PG (E & x ~: T)
  | okt_disj : forall E X T,
      okt PG E ->
      wft PG E T ->
      X # E -> 
      groundtype T ->
      okt PG (E & X ~*: T).

#[export]
Hint Constructors type wft okenvp groundtype : core.

(*********************************************)
(**********  FindSubtypes  (LOS)  ************)
(*********************************************)

Definition all_ord (PG : envp) := [t_int; 
  t_unit; t_all t_bot t_bot] ++ nats_to_types (domain_envp PG).


Inductive OSubtypes (PG:envp) (E:env) : typ -> list typ -> Prop :=
  | osubs_top :
      OSubtypes PG E t_top (all_ord PG)
  | osubs_bot : 
      OSubtypes PG E t_bot []
  | osubs_int : 
      OSubtypes PG E t_int [t_int]
  | osubs_arrow : forall A B, 
      OSubtypes PG E (t_arrow A B)  []
  | osubs_union : forall A B,
      forall l1, OSubtypes PG E A l1 ->
      forall l2, OSubtypes PG E B l2 ->
     OSubtypes PG E (t_union A B) (l1 `union` l2)
  | osubs_inter : forall A B,
      forall l1, OSubtypes PG E A l1 ->
      forall l2, OSubtypes PG E B l2 ->
      OSubtypes PG E (t_and A B) (l1 `inter` l2)
  | osubs_unit :
      OSubtypes PG E t_unit [t_unit]
  | osubs_fvar : forall X T,
      binds X (bind_disj T) E ->
      forall l,
      OSubtypes PG E T l ->
      OSubtypes PG E (t_fvar X) ((all_ord PG)  `dif` l)
  | osubs_all : forall A B,
      OSubtypes PG E (t_all A B)  [t_all t_bot t_bot]
  | osubs_prim : forall i,
      OSubtypes PG E (t_prim i) ([t_prim i] ++ 
      nats_to_types (get_all_subtypes PG (t_prim i))).

#[export]
Hint Constructors OSubtypes : core.

(* Ordinary ranges of function subtypes. Two arrows are disjoint
   iff these sets do not overlap (range rule). *)
Inductive ArrowRanges (PG:envp) (E:env) : typ -> list typ -> Prop :=
  | ar_top :
      ArrowRanges PG E t_top (all_ord PG)
  | ar_bot :
      ArrowRanges PG E t_bot []
  | ar_int :
      ArrowRanges PG E t_int []
  | ar_unit :
      ArrowRanges PG E t_unit []
  | ar_prim : forall i,
      ArrowRanges PG E (t_prim i) []
  | ar_arrow : forall A B,
      ArrowRanges PG E (t_arrow A B) [B]
  | ar_union : forall A B l1 l2,
      ArrowRanges PG E A l1 ->
      ArrowRanges PG E B l2 ->
      ArrowRanges PG E (t_union A B) (l1 `union` l2)
  | ar_inter : forall A B l1 l2,
      ArrowRanges PG E A l1 ->
      ArrowRanges PG E B l2 ->
      ArrowRanges PG E (t_and A B) (l1 `inter` l2)
  | ar_fvar : forall X T l,
      binds X (bind_disj T) E ->
      ArrowRanges PG E T l ->
      ArrowRanges PG E (t_fvar X) l
  | ar_all : forall A B,
      ArrowRanges PG E (t_all A B) [].

#[export]
Hint Constructors ArrowRanges : core.

(* defns Subtyping *)
Reserved Notation "PG ; G |= A <: B" (at level 80, A at next level, B at next level).
Inductive sub (PG: envp) : env -> typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall G A,
     okenvp PG ->
     okt PG G ->
     wft PG G A ->
     sub PG G A t_top
 | s_int : forall G,
     okenvp PG ->
     okt PG G ->
     sub PG G t_int t_int
 | s_unit : forall G,
    okenvp PG ->
    okt PG G ->
    sub PG G t_unit t_unit
 | s_arrow : forall G (A1 A2 B1 B2:typ),
     sub PG G B1 A1 ->
     sub PG G A2 B2 ->
     sub PG G (t_arrow A1 A2) (t_arrow B1 B2)
 | s_ora : forall G (A1 A2 A:typ),
     sub PG G A1 A ->
     sub PG G A2 A ->
     sub PG G (t_union A1 A2) A
 | s_orb : forall G (A A1 A2:typ),
     wft PG G A2 ->
     sub PG G A A1 ->
     sub PG G A (t_union A1 A2)
 | s_orc : forall G (A A1 A2:typ),
     wft PG G A1 ->
     sub PG G A A2 ->
     sub PG G A (t_union A1 A2)
 | s_anda : forall G A A1 A2,
     sub PG G A A1 ->
     sub PG G A A2 ->
     sub PG G A (t_and A1 A2)
 | s_andb : forall G A1 A2 A,
     wft PG G A2 ->
     sub PG G A1 A ->
     sub PG G (t_and A1 A2) A
 | s_andc : forall G A1 A2 A,
     wft PG G A1 ->
     sub PG G A2 A ->
     sub PG G (t_and A1 A2) A
 | s_bot : forall G A,
      okenvp PG ->
      okt PG G ->
      wft PG G A ->
      sub PG G t_bot A
 | s_tvar : forall G X,
     okenvp PG ->
     okt PG G ->
     wft PG G (t_fvar X) ->
     sub PG G (t_fvar X) (t_fvar X)
 | s_all : forall L G S1 S2 T1 T2,
      sub PG G S1 T1 ->
      groundtype S1 ->
      (forall X, X \notin L ->
          PG ; (G & X ~*: T1) |=  (S2 open_tt_var X) <: (T2 open_tt_var X)) ->
      PG ; G |= (t_all S1 S2) <: (t_all T1 T2)
 | s_p_refl : forall i E,
     okenvp PG ->
     okt PG E ->
     wft PG E (t_prim i) ->
     PG ; E |= (t_prim i) <: (t_prim i)
 | s_p_sub : forall n1 n2 E,
     okenvp PG ->
     okt PG E ->
     wft PG E (t_prim n1) -> 
     wft PG E (t_prim n2) ->
     set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n2))) ->
     PG ; E |= (t_prim n1) <: (t_prim n2)
where "PG ; G |= A <: B" := (sub PG G A B) : env_scope.

#[export]
Hint Constructors sub lc_exp ok okt : core.

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
  | o_int   : Ord t_int
  | o_arrow : forall t1 t2, Ord t2 -> Ord (t_arrow t1 t2)
  | o_unit  : Ord t_unit
  | o_all   : forall t1 t2, Ord (t_all t1 t2)
  | o_prim  : forall i, Ord (t_prim i).

#[export]
Hint Constructors Ord : core.

(***********************************)
(****  FindSubtypes Properties  ****)
(***********************************)

Lemma list_empty_decide : forall (l : list typ), (l = []) \/ (l <> []).
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

Lemma sub_or (PG:envp) : forall G A B C, PG ; G |= (t_union A B) <: C -> 
  PG ; G |= A <: C /\ PG ; G |= B <: C.
Proof.
intros; inductions H; try solve [split*].
inverts* H1.
specialize (IHsub A B).
forwards* : IHsub.
specialize (IHsub A B).
forwards* : IHsub.
specialize (IHsub1 A B).
specialize (IHsub2 A B).
forwards* : IHsub1.
Defined.

Lemma sub_and (PG:envp) : forall G A B C, PG ; G |= A <: (t_and B C) -> 
  PG ; G |= A <: B /\ PG ; G |= A <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsub1 B C).
specialize (IHsub2 B C).
forwards* : IHsub1.
specialize (IHsub B C).
forwards* : IHsub.
specialize (IHsub B C).
forwards* : IHsub.
inverts* H1.
Defined.

(*  
  Nominal Type Properties
*)

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

Lemma prim_type_in : forall PG E n l,
  OSubtypes PG E (t_prim n) l ->
  forall A, set_In A l ->
  exists (i : nat), A = t_prim i.
Proof.
  intros PG E n l H. inverts H; simpl; intros.
  destruct H. exists*.
  destruct (get_all_subtypes PG (t_prim n)); intros. simpl in H.
  inverts H.
  apply prim_type_in_nats_to_types in H. destruct H.
  exists*.
Qed.

Lemma prim_subtypes_not_empty : forall PG,
  okenvp PG -> 
  forall E i, wft PG E (t_prim i) ->
  forall l, OSubtypes PG E (t_prim i) l -> 
  l <> [].
Proof.
  introv OK WFT.
  unfold not. intros.
  inverts H. simpl in TEMP.
  inverts TEMP.
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
    (*assert (domain_envp ((C, D):: PG) = C :: domain_envp PG) as -> by admit.*)
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

(* Function types are never least ordinary subtypes. *)

Lemma arrow_in_top_bot : forall PG G C l,
  OSubtypes PG G C l ->
  forall A B, set_In (t_arrow A B) l -> False.
Proof.
  intros PG G C l Hos. induction Hos; intros ArrA ArrB Hin.
  - unfold all_ord in Hin. simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]]; try discriminate.
    apply prim_type_in_nats_to_types in Hin. destruct Hin as [i Ei].
    discriminate.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Hin|Hin]; [discriminate|inversion Hin].
  - inversion Hin.
  - apply set_union_elim in Hin. destruct Hin; eauto.
  - apply set_inter_elim1 in Hin. eauto.
  - simpl in Hin. destruct Hin as [Hin|Hin]; [discriminate|inversion Hin].
  - apply set_diff_elim1 in Hin. unfold all_ord in Hin. simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]]; try discriminate.
    apply prim_type_in_nats_to_types in Hin. destruct Hin as [i Ei].
    discriminate.
  - simpl in Hin. destruct Hin as [Hin|Hin]; [discriminate|inversion Hin].
  - simpl in Hin. destruct Hin as [Hin|Hin].
    + discriminate.
    +     apply prim_type_in_nats_to_types in Hin. destruct Hin as [j Ej].
      discriminate.
Qed.

(* If disjoint quantifier is in findsubtypes then it
must be (forall X . Bot -> Bot) *)

Lemma all_in_bot_bot : forall PG G C l,
OSubtypes PG G C l -> 
forall A B, set_In (t_all A B) l ->
t_all A B = t_all t_bot t_bot.
Proof.
  intros PG G C l Hos. induction Hos; intros AllA AllB Hin.
  - unfold all_ord in Hin. simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]]; try discriminate.
    + inversion Hin. reflexivity.
    + apply prim_type_in_nats_to_types in Hin. destruct Hin as [j Ej].
      discriminate.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Hin|Hin]; [discriminate|inversion Hin].
  - inversion Hin.
  - apply set_union_elim in Hin. destruct Hin; eauto.
  - apply set_inter_elim1 in Hin. eauto.
  - simpl in Hin. destruct Hin as [Hin|Hin]; [discriminate|inversion Hin].
  - apply set_diff_elim1 in Hin. unfold all_ord in Hin. simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]]; try discriminate.
    + inversion Hin. reflexivity.
    + apply prim_type_in_nats_to_types in Hin. destruct Hin as [j Ej].
      discriminate.
  - simpl in Hin. destruct Hin as [Hin|Hin].
    + inversion Hin. reflexivity.
    + inversion Hin.
  - simpl in Hin. destruct Hin as [Hin|Hin].
    + discriminate.
    + apply prim_type_in_nats_to_types in Hin. destruct Hin as [j Ej].
      discriminate.
Qed.

(* If ordinary type is a subtype of another type
then it must be in its findsubtypes *)

Lemma ord_in_findsubtypes : forall PG G A B,
  Ord A -> 
  PG ; G |= A <: B -> 
  forall E l, OSubtypes PG E B l -> 
  set_In A l \/
  (exists t1 t2, A = t_arrow t1 t2) \/
  (exists t1 t2, A = t_all t1 t2 /\ set_In (t_all t_bot t_bot) l).
Proof.
  introv Ord. gen B.
  inductions Ord; intros.
  - (*case int*)
   gen l. induction B; simpl; auto; try solve [inverts H]; intros.
   + inverts* H0. left. simpl. auto.
   + inverts H0. simpl. auto.
   + inverts H0.
    inverts* H.
    * destruct (IHB1 H7 l1); auto.
      left. apply set_union_intro. left*.
      destruct H as [H | H].
      destruct H as [x1 [x2]]. inversion H.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * destruct (IHB2 H7 l2); auto.
      left. apply set_union_intro. right*.
      destruct H as [H | H].
      destruct H as [x1 [x2]]. inversion H.
      destruct H as [x1 [x2]]. destruct H. inversion H.
   + apply sub_and in H. destruct H.
     inverts H0.
     destruct (IHB1 H l1); auto.
    * destruct (IHB2 H1 l2); auto.
      left. apply set_inter_intro; auto.
      destruct H2 as [H2 | H2].
      destruct H2 as [x1 [x2]]. inversion H2.
      destruct H2 as [x1 [x2]]. destruct H2. inversion H2.
    * destruct H0 as [H0 | H0].
      destruct H0 as [x1 [x2]]. inversion H0.
      destruct H0 as [x1 [x2]]. destruct H0. inversion H0.
  - (*case arrow — not recorded in OSubtypes *)
    right. left. exists t1 t2. reflexivity.
 - (*case unit*)
   gen l. induction B; simpl; auto; try solve [inverts H]; intros.
   + inverts H0. simpl. left*. 
   + inverts H0.
     inverts H.
     * destruct~ (IHB1 H7 l1).
       left. apply set_union_intro; auto.
       destruct H as [H | H].
       destruct H as [x1 [x2]]. inverts H.
       destruct H as [x1 [x2 [H' H'']]]. inverts H'.
     * destruct~ (IHB2 H7 l2).
       left. apply set_union_intro; auto.
       destruct H as [H | H].
       destruct H as [x1 [x2]]. inverts H.
       destruct H as [x1 [x2 [H' H'']]]. inverts H'.
    + apply sub_and in H. destruct H.
      inverts H0.
      destruct~ (IHB1 H l1).
     * destruct~ (IHB2 H1 l2).
       left. apply set_inter_intro; auto.
       destruct H2 as [H2 | H2].
       destruct H2 as [x1 [x2]]. inverts H2.
       destruct H2 as [x1 [x2 [H2 H3]]]. inverts H2.
     * destruct H0 as [H0 | H0].
       destruct H0 as [x1 [x2]]. inverts H0.
       destruct H0 as [x1 [x2 [H0 H0']]]. inverts H0.
    + inverts H0. simpl. left*.
  - (*case all*) 
   gen l. inductions B; simpl; try solve [inverts H]; intros.
   + right. right. inverts H0. simpl. exists* t1 t2.
   + inverts H0.
     inverts H.
     * destruct~ (IHB1 H7 E l1) as [H | H].
       left. apply~ set_union_intro1.
       destruct H as [Harr | Hall].
       destruct Harr as [x1 [x2]]. discriminate.
       destruct Hall as [x1 [x2 [Heq Hin]]].
       right. right. exists t1 t2. split*.
       apply~ set_union_intro1.
     * destruct~ (IHB2 H7 E l2) as [H | H].
       left. apply~ set_union_intro2.
       destruct H as [Harr | Hall].
       destruct Harr as [x1 [x2]]. discriminate.
       destruct Hall as [x1 [x2 [Heq Hin]]].
       right. right. exists t1 t2. split*.
       apply~ set_union_intro2.
    + inverts H0.
      apply sub_and in H. destruct H.
      destruct (IHB1 H E l1) as [Hin1 | Rest1]; auto.
      * destruct (IHB2 H0 E l2) as [Hin2 | Rest2]; auto.
        -- left. apply set_inter_intro; auto.
        -- destruct Rest2 as [Harr | Hall].
           ++ destruct Harr as [x1 [x2]]. discriminate.
           ++ destruct Hall as [x1 [x2 [_ Hin2]]].
              assert (EQ: t_all t1 t2 = t_all t_bot t_bot).
              { apply all_in_bot_bot with (PG:=PG) (G:=E) (C:=B1) (l:=l1); eauto. }
              rewrite EQ in Hin1.
              right. right. exists t1 t2. split; [reflexivity|].
              apply set_inter_intro; auto.
      * destruct (IHB2 H0 E l2) as [Hin2 | Rest2]; auto.
        -- destruct Rest1 as [Harr | Hall].
           ++ destruct Harr as [x1 [x2]]. discriminate.
           ++ destruct Hall as [x1 [x2 [_ Hin1]]].
              assert (EQ: t_all t1 t2 = t_all t_bot t_bot).
              { apply all_in_bot_bot with (PG:=PG) (G:=E) (C:=B2) (l:=l2); eauto. }
              rewrite EQ in Hin2.
              right. right. exists t1 t2. split; [reflexivity|].
              apply set_inter_intro; auto.
        -- destruct Rest1 as [Harr | Hall];
           destruct Rest2 as [Harr2 | Hall2].
           ++ destruct Harr as [x1 [x2]]. discriminate.
           ++ destruct Harr as [x1 [x2]]. discriminate.
           ++ destruct Harr2 as [x1 [x2]]. discriminate.
           ++ destruct Hall as [x1 [x2 [_ Hin1]]].
              destruct Hall2 as [x3 [x4 [_ Hin2]]].
              right. right. exists t1 t2. split; [reflexivity|].
              apply set_inter_intro; auto.
   + right. right. inverts H0. simpl. exists* t1 t2.
  - (*case P*)
    left. gen l. inductions H; intros.
    + inverts H2. simpl. right. right. right.
      inverts H1.
      forwards*: i_in_nat_to_types H4.
    + inverts H1.
      apply set_union_intro.
      forwards*: IHsub H4.
    + inverts H1.
      apply set_union_intro.
      forwards*: IHsub H6.
    + inverts H1.
      apply set_inter_intro.
      forwards*: IHsub1 H4.
      forwards*: IHsub2 H6.
    + inverts H2. simpl. auto.
    + inverts H4. simpl.
      right*.
Qed.

Lemma ord_sub_findsubtypes_not_empty : forall A,
  Ord A -> (forall t1 t2, A <> t_arrow t1 t2) ->
  forall PG G B, (PG ; G |= A <: B) ->
  forall E l, OSubtypes PG E B l -> l <> [].
Proof.
  unfold not. intros A OrdA NArr PG G B Sub E l Hos Heq. subst.
  eapply ord_in_findsubtypes in Sub; eauto.
  destruct Sub as [Hin | [Harr | Hall]].
  - inversion Hin.
  - destruct Harr as [t1 [t2 Heq]]. apply (NArr t1 t2). auto.
  - destruct Hall as [t1 [t2 [_ Hin]]]. inversion Hin.
Qed.

Lemma all_ord_in_all_ord : forall PG B,
  set_In B (all_ord PG)->
  Ord B.
Proof.
  intros; unfold all_ord in H; simpl in H.
  destruct H as [H | [H | [H | H]]];
   try solve [rewrite <- H; auto].
   apply prim_type_in_nats_to_types in H.
   destruct H as [i].
   inverts* H.
Defined.

Lemma demorgan : forall (P Q R S : Prop), 
~ (P \/ Q \/ R \/ S) -> ~P /\ ~Q /\ ~R /\ ~S.
Proof.
  intros.
  unfold not in *.
  splits; intros; apply H; auto.
Defined.

Lemma bot_sub_all : forall PG G A,
  okenvp PG ->
  okt PG G ->
  wft PG G A -> 
  PG ; G |= t_bot <: A.
Proof.
  intros.
  dependent induction A; eauto.
Qed.

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

Definition DisjAlgo (PG:envp) (E:env) A B := 
  okenvp PG /\
  okt PG E /\
  wft PG E A /\
  wft PG E B /\
  (forall l1 l2, ((OSubtypes PG E A l1) /\ (OSubtypes PG E B l2)) ->
   (l1 `inter` l2) = []) /\
  (forall r1 r2, ((ArrowRanges PG E A r1) /\ (ArrowRanges PG E B r2)) ->
   (r1 `inter` r2) = []).
Notation "PG ; E |= A *a B" := (DisjAlgo PG E A B) (at level 80, E at next level, A at next level).

(* Ground Type Properties *)

Lemma okt_binds_ground : forall PG E,
  okt PG E ->
  forall X T, binds X (bind_disj T) E ->
  groundtype T.
Proof.
  induction 1; intros.
  apply binds_empty_inv in H. inverts H.
  binds_cases H2. forwards*: IHokt B.
  binds_cases H3. forwards*: IHokt B.
  inverts EQ. auto.
Qed. 

Lemma exists_osubtypes_ground : forall PG E A,
  groundtype A ->
  exists l, OSubtypes PG E A l.
Proof.
  introv GT. inductions GT; try solve [exists*].
  destruct~ IHGT1 as [l1].
  destruct~ IHGT2 as [l2]. exists*.
  destruct~ IHGT1 as [l1].
  destruct~ IHGT2 as [l2]. exists*.
Qed.

Lemma exists_osubtypes : forall PG E A,
  okt PG E ->
  wft PG E A ->
  exists l, OSubtypes PG E A l.
Proof.
  introv OK WFT. inductions WFT; try solve [exists*].
  destruct~ IHWFT1 as [l1].
  destruct~ IHWFT2 as [l2]. exists*.
  destruct~ IHWFT1 as [l1].
  destruct~ IHWFT2 as [l2]. exists*.
  forwards* GU: okt_binds_ground H.
  forwards* (l&osubu): exists_osubtypes_ground GU.
Qed.

Lemma exists_arrowranges_ground : forall PG E A,
  groundtype A ->
  exists l, ArrowRanges PG E A l.
Proof.
  introv GT. inductions GT; try solve [exists*].
  - destruct~ IHGT1 as [l1]. destruct~ IHGT2 as [l2]. exists*.
  - destruct~ IHGT1 as [l1]. destruct~ IHGT2 as [l2]. exists*.
Qed.

Lemma exists_arrowranges : forall PG E A,
  okt PG E ->
  wft PG E A ->
  exists l, ArrowRanges PG E A l.
Proof.
  introv OK WFT. induction WFT.
  - exists (all_ord PG). constructor.
  - exists (@nil typ). constructor.
  - exists (@nil typ). constructor.
  - exists (T2 :: nil). constructor.
  - destruct IHWFT1 as [l1]; auto. destruct IHWFT2 as [l2]; auto.
    exists (l1 `union` l2). constructor; auto.
  - destruct IHWFT1 as [l1]; auto. destruct IHWFT2 as [l2]; auto.
    exists (l1 `inter` l2). constructor; auto.
  - forwards* GU: okt_binds_ground H.
    destruct (exists_arrowranges_ground PG E U GU) as [l AR].
    exists l. apply ar_fvar with (T:=U); auto.
  - exists (@nil typ). constructor.
  - exists (@nil typ). constructor.
  - exists (@nil typ). constructor.
Qed.

(* Regularity of disjointness *)

Lemma disj_regular : forall PG E A B,
  DisjAlgo PG E A B ->
  okenvp PG /\ okt PG E /\ wft PG E A /\ wft PG E B.
Proof.
  introv Disj.
  unfold DisjAlgo in Disj.
  destructs~ Disj.
Qed.