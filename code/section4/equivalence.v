(*

-> Section 4 in paper
-> Union Types + Null + Intersection Types
-> Nominal types
-> Subtyping Distributivity

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Lia.


Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top type *)
 | t_bot : typ (*r bottom type *)
 | t_arrow : typ -> typ -> typ (*r function types *)
 | t_union : typ -> typ -> typ (*r intersection *)
 | t_and : typ -> typ -> typ (*r intersection *)
 | t_unit : typ (* null *)
 | t_prim (n:var).

Definition envp : Set := list ( atom * typ ).

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
  | wft_prim : forall i A,
      binds i A PG ->
      wft PG (t_prim i).

Inductive okenvp : envp -> Prop :=
  | okenvp_empty :
      okenvp nil
  | okenvp_cons : forall (PG:envp) (i:var),
      okenvp PG ->
      i `notin` (dom PG) ->
      okenvp ((i, t_top) :: PG)
  | okenvp_sub : forall (PG:envp) (i j:var),
      okenvp PG ->
      wft PG (t_prim j) ->
      i `notin` (dom PG) ->
      okenvp ((i, (t_prim j)) :: PG).

(* defns DSub *)
Inductive declarative_subtyping (PG: envp) : typ -> typ -> Prop :=    (* defn declarative_subtyping *)
 | DS_refl : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG A A
 | DS_trans : forall (A C B:typ),
     declarative_subtyping PG A B ->
     declarative_subtyping PG B C ->
     declarative_subtyping PG A C
 | DS_top : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG A t_top
 | DS_bot : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG t_bot A
 | DS_arrow : forall (A C B D:typ),
     declarative_subtyping PG B A ->
     declarative_subtyping PG C D ->
     declarative_subtyping PG (t_arrow A C) (t_arrow B D)
 | DS_and : forall (A B C:typ),
     declarative_subtyping PG A B ->
     declarative_subtyping PG A C ->
     declarative_subtyping PG A (t_and B C)
 | DS_andl : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG (t_and A B) A
 | DS_andr : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG (t_and A B) B
 | DS_or : forall (A B C:typ),
     declarative_subtyping PG A C ->
     declarative_subtyping PG B C ->
     declarative_subtyping PG (t_union A B) C
 | DS_orl : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG A (t_union A B)
 | DS_orr : forall (B A:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG B (t_union A B)
 | DS_distArr : forall (A B1 B2:typ),
     okenvp PG ->
     wft PG A -> wft PG B1 -> wft PG B2 ->
     declarative_subtyping PG (t_and  (t_arrow A B1)   (t_arrow A B2) ) (t_arrow A (t_and B1 B2))
| DS_distArrU : forall (A1 B A2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow (t_union A1 A2) B)
 | DS_distOr : forall (A1 B A2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_union A1 B)   (t_union A2 B) ) (t_union  (t_and A1 A2)  B)
 | DS_prim : forall i A,
     okenvp PG ->
     binds i A PG ->
     declarative_subtyping PG (t_prim i) A.
(** definitions *)

(* defns Ordinary *)
Inductive ordu : typ -> Prop :=    (* defn ordu *)
 | OU_top :
     ordu t_top
 | OU_bot :
     ordu t_bot
 | OU_int :
     ordu t_int
 | OU_arrow : forall (A B:typ),
     ordu (t_arrow A B)
 | OU_and : forall (A B:typ),
     ordu A ->
     ordu B ->
     ordu (t_and A B)
 | OU_null :
     ordu t_unit
 | OU_prim : forall (i:var),
     ordu (t_prim i).

Inductive ordi : typ -> Prop :=    (* defn ordi *)
 | OI_top :
     ordi t_top
 | OI_bot :
     ordi t_bot
 | OI_int :
     ordi t_int
 | OI_arrow : forall (A B:typ),
     ordu A ->
     ordi B ->
     ordi (t_arrow A B)
 | OI_or : forall (A B:typ),
     ordi A ->
     ordi B ->
     ordi (t_union A B)
 | OI_null :
     ordi t_unit
 | OI_prim : forall (i:var),
     ordi (t_prim i).
(** definitions *)

(* defns Split *)
Inductive splu : typ -> typ -> typ -> Prop :=    (* defn splu *)
 | SpU_or : forall (A B:typ),
     splu (t_union A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2).

Inductive spli : typ -> typ -> typ -> Prop :=    (* defn spli *)
 | SpI_and : forall (A B:typ),
     spli (t_and A B) A B
 | SpI_arrow : forall (A B C D:typ),
     spli B C D ->
     spli (t_arrow A B) (t_arrow A C) (t_arrow A D)
 | SpI_arrowUnion : forall (A D B C:typ),
     ordi D ->
     splu A B C ->
     spli (t_arrow A D) (t_arrow B D) (t_arrow C D)
 | SpI_orl : forall (A B A1 A2:typ),
     spli A A1 A2 ->
     spli (t_union A B) (t_union A1 B) (t_union A2 B)
 | SpI_orr : forall (A B B1 B2:typ),
     ordi A ->
     spli B B1 B2 ->
     spli (t_union A B) (t_union A B1) (t_union A B2).
(** definitions *)

(* defns SSub *)
Inductive algo_sub : envp -> typ -> typ -> Prop :=    (* defn algo_sub *)
 | AS_refl : forall PG A,
     okenvp PG ->
     wft PG A ->
     algo_sub PG A A
 | AS_prim_neq : forall PG i A n1 n2,
     okenvp ((i, A) :: PG) ->
     (* (issupertype PG n1 n2 = true) -> *)
     i <> n1 ->
     algo_sub PG (t_prim n1) (t_prim n2) ->
     algo_sub (((i, A))::PG) (t_prim n1) (t_prim n2)
 | AS_prim_eq : forall PG j n1 n2,
     okenvp (((n1,t_prim j))::PG) ->
     (* (issupertype PG n1 n2 = true) -> *)
     algo_sub PG (t_prim j) (t_prim n2) ->
     algo_sub (((n1,t_prim j))::PG) (t_prim n1) (t_prim n2)
 | AS_top : forall PG (A:typ),
     okenvp PG ->
     wft PG A ->
     algo_sub PG A t_top
 | AS_bot : forall PG (A:typ),
     okenvp PG ->
     wft PG A ->
     algo_sub PG t_bot A
 | AS_arrow : forall PG (A1 A2 B1 B2:typ),
     algo_sub PG B1 A1 ->
     algo_sub PG A2 B2 ->
     algo_sub PG (t_arrow A1 A2) (t_arrow B1 B2)
 | AS_and : forall PG (A B B1 B2:typ),
     spli B B1 B2 ->
     algo_sub PG A B1 ->
     algo_sub PG A B2 ->
     algo_sub PG A B
 | AS_andl : forall PG (A B A1 A2:typ),
     wft PG A2 ->
     spli A A1 A2 ->
     algo_sub PG A1 B ->
     algo_sub PG A B
 | AS_andr : forall PG (A B A1 A2:typ),
     wft PG A1 ->
     spli A A1 A2 ->
     algo_sub PG A2 B ->
     algo_sub PG A B
 | AS_or : forall PG (A B A1 A2:typ),
     splu A A1 A2 ->
     algo_sub PG A1 B ->
     algo_sub PG A2 B ->
     algo_sub PG A B
 | AS_orl : forall PG (A B B1 B2:typ),
     wft PG B2 ->
     splu B B1 B2 ->
     algo_sub PG A B1 ->
     algo_sub PG A B
 | AS_orr : forall PG (A B B1 B2:typ),
     wft PG B1 ->
     splu B B1 B2 ->
     algo_sub PG A B2 ->
     algo_sub PG A B.

#[export] Hint Resolve AS_refl : core.

(******************************************************************************)
(** * Size *)
Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_unit => 1
    | t_prim _ => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_union A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  end.

Fixpoint size_envp (G : envp) := match G with
                                 | nil => 0
                                 | (i, A) :: G => size_envp G + size_typ A + 1
                                     end.

(* Definition size_envp (G : envp) := fold_right plus 0 (map size_typ G). *)

Lemma size_typ_min :
  forall A1, 1 <= size_typ A1.
Proof.
  induction A1; simpl in *; eauto; try lia.
Qed.

Create HintDb SubHd.
Create HintDb FalseHd.

#[export] Hint Resolve OI_top OI_bot OI_int OU_top OU_bot OU_int OU_arrow SpI_and SpU_or : core.
#[export] Hint Constructors algo_sub ordi ordu spli splu : SubHd.

(* Types are Either Ordinary or Splittable *)
Lemma ordu_or_split: forall A,
    ordu A \/ exists B C, splu A B C.
Proof with (eauto with SubHd ; intros).
  intros. induction A...
  - (* and *)
    lets [?|(?&?&?)]: IHA1;
      lets [?|(?&?&?)]: IHA2...
Qed.

Lemma ordi_or_split: forall A,
    ordi A \/ exists B C, spli A B C.
Proof with (eauto with SubHd ; intros).
  intros. induction A...
  - (* arrow *)
    lets [?|(?&?&?)]: ordu_or_split A1;
      lets [?|(?&?&?)]: IHA2...
  - (* and *)
    lets [?|(?&?&?)]: IHA1;
      lets [?|(?&?&?)]: IHA2...
Qed.


(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
                         match T with
                         | exists _ , _ => destruct H
                         | _ /\ _ => destruct H
                         end
         end.

(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)
Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].

#[export] Hint Extern 1 => match goal with
                           | H: _ = _ |- _ => inverts H; fail
                           | H: ordi _ |- _ => inverts H; fail
                           | H: ordu _ |- _ => inverts H; fail
                           | H: spli _ _ _ |- _ => inverts H; fail
                           | H: splu _ _ _ |- _ => inverts H; fail
                         end : FalseHd.

(* splittable types and disjoint types are not overlapping *)
Lemma splu_ord_false : forall A B C,
    splu A B C -> ordu A -> False.
Proof.
  introv. gen B C.
  induction A; intros B C s o;
    try solve [inverts* s];
    try solve [inverts* o];
    inverts o;
    inverts* s.
Qed.

Lemma spli_ord_false : forall A B C,
    spli A B C -> ordi A -> False.
Proof.
  introv. gen B C.
  induction A; intros B C s o;
    try solve [inverts* s];
    try solve [inverts* o];
    inverts o;
    inverts* s.
  applys splu_ord_false; eassumption.
Qed.

#[export] Hint Resolve spli_ord_false splu_ord_false : FalseHd.

(* lemmas for ordinary *)
Lemma spli_keep_ordu_l : forall A B C,
   ordu A -> spli A B C -> ordu B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma spli_keep_ordu_r : forall A B C,
   ordu A -> spli A B C -> ordu C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma splu_keep_ord_l : forall A B C,
   ordi A -> splu A B C -> ordi B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma splu_keep_ord_r : forall A B C,
   ordi A -> splu A B C -> ordi C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

#[export] Hint Immediate spli_keep_ordu_l spli_keep_ordu_r
     splu_keep_ord_l splu_keep_ord_r : SubHd.


(* Subtyping *)
Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

#[export] Hint Resolve typ_size_lg_z : core.

Lemma splu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
Qed.

Lemma spli_decrease_size: forall A B C,
    spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  forwards (?&?): splu_decrease_size H0...
Qed.

Ltac s_spl_size :=
  try repeat match goal with
         | [ H: spli _ _ _ |- _ ] =>
           ( lets (?&?): spli_decrease_size H; clear H)
         | [ H: splu _ _ _ |- _ ] =>
           ( lets (?&?): splu_decrease_size H; clear H)
             end.

(********************************************)
(*                                          *)
(*               Ltac elia                 *)
(*  enhanced lia with split_decrease_size *)
(*                                          *)
(********************************************)
Ltac elia :=
  try solve [pose proof (typ_size_lg_z);
             s_spl_size; simpl in *; try lia].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

Ltac indTypEnvSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  repeat match goal with | [ h : envp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].
(* Splitting types is deterministic *)
(********************************************)
(*                                          *)
(*          Lemma split_unique              *)
(*                                          *)
(********************************************)
Lemma splu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (try eassumption; solve_false; subst~).
  intro T.
  induction T; intros;
    inverts H; inverts H0...
  - forwards (?&?): IHT1 H4 H5...
  - forwards (?&?): IHT2 H6 H7...
Qed.

Lemma spli_unique : forall T A1 A2 B1 B2,
    spli T A1 B1 -> spli T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (try eassumption; solve_false; subst~).
  intro T.
  induction T; intros;
    inverts H; inverts H0...
  - forwards (?&?): IHT2 H4 H5...
  - forwards (?&?): splu_unique H6 H7...
  - forwards (?&?): IHT1 H4 H5...
  - forwards (?&?): IHT2 H6 H7...
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_unify              *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end                *)
(*                                          *)
(********************************************)
Ltac auto_unify :=
  simpl in *;
  try repeat match goal with
         | [ H1: spli ?A  _ _ , H2: spli ?A _ _ |- _ ] =>
           (forwards (?&?): spli_unique H1 H2;
            subst; clear H2)
         | [ H1: splu ?A  _ _ , H2: splu ?A _ _ |- _ ] =>
           (forwards (?&?): splu_unique H1 H2;
            subst; clear H2)
         end.

Ltac inverts_all_ord :=
  repeat match goal with
         | H: ordu (_ _ _) |- _ => inverts H
         | H: ordu (_ _) |- _ => inverts H
         | H: ordi (_ _ _) |- _ => inverts H
         | H: ordi (_ _) |- _ => inverts H
         end.

Ltac inverts_all_spl :=
  repeat match goal with
         | H: splu (_ _ _) _ _ |- _ => inverts H
         | H: splu (_ _) _ _ |- _ => inverts H
         | H: spli (_ _ _) _ _ |- _ => inverts H
         | H: spli (_ _) _ _ |- _ => inverts H
         end.

(******************************************************************************)
(* * wft *)

Ltac wft_inv := match goal with
                  H: wft ?G _ |- wft ?G ?A => match type of H with
                                           context[A] => inverts H; try assumption
                                         end
                end.
#[export] Hint Extern 1 (wft _ _) => wft_inv : core.

Lemma wft_splu_1 : forall G A1 A2 B,
    splu B A1 A2 -> wft G B -> wft G A1.
Proof.
  introv Spl Wf.
  induction* Spl. all: constructor~.
Qed.
Lemma wft_splu_2 : forall G A1 A2 B,
    splu B A1 A2 -> wft G B -> wft G A2.
Proof.
  introv Spl Wf.
  induction* Spl. all: constructor~.
Qed.
Lemma wft_splu : forall G A1 A2 B,
    splu B A1 A2 -> wft G A1 -> wft G A2 -> wft G B.
Proof.
  introv Spl Wf1 Wf2.
  induction* Spl. all: constructor~.
Qed.
#[export] Hint Immediate wft_splu_1 wft_splu_2 wft_splu : core.

Lemma wft_spli_1 : forall G A1 A2 B,
    spli B A1 A2 -> wft G B -> wft G A1.
Proof.
  introv Spl Wf.
  induction* Spl. all: constructor~.
  inverts* Wf.
Qed.
Lemma wft_spli_2 : forall G A1 A2 B,
    spli B A1 A2 -> wft G B -> wft G A2.
Proof.
  introv Spl Wf.
  induction* Spl. all: constructor~.
  inverts* Wf.
Qed.
Lemma wft_spli : forall G A1 A2 B,
    spli B A1 A2 -> wft G A1 -> wft G A2 -> wft G B.
Proof.
  introv Spl Wf1 Wf2.
  induction* Spl. all: constructor*. eauto using wft_splu.
Qed.
#[export] Hint Immediate wft_spli_1 wft_spli_2 wft_spli: core.

Ltac inverts_all_wft :=
  repeat match goal with
         | H: wft _ (_ _ _) |- _ => inverts H
         | H: wft _ (_ _) |- _ => inverts H
         | H: wft _ ?A, Hspl: spli ?A _ _ |- _ => forwards: wft_spli_1 Hspl H; forwards: wft_spli_2 Hspl H; clear H
         | H: wft _ ?A, Hspl: splu ?A _ _ |- _ => forwards: wft_splu_1 Hspl H; forwards: wft_splu_2 Hspl H; clear H
         end.

#[export] Hint Constructors wft okenvp : core.

Lemma wf_typ_weakening : forall p T G,
  wft G T ->
  okenvp (p::G) ->
  wft (p::G) T.
Proof with simpl_env; eauto.
  introv Hwf_typ Hk.
  induction Hwf_typ; intros; subst...
Qed.

Lemma okenvp_uniq : forall G,
  okenvp G -> uniq G.
Proof.
  introv H. induction* H.
Qed.

Lemma wft_in_domain : forall G n,
    wft G (t_prim n) -> n `in` dom G.
Proof.
  introv H.
  inductions H. eauto.
Qed.

Lemma wft_strenthen_prim : forall G m B n,
   wft ((m,B)::G) (t_prim n) -> m <> n -> wft G (t_prim n) .
Proof.
  introv Wf Neq. inductions Wf; eauto.
  inverts* H. injection H0; intros; subst*.
  contradiction.
Qed.

Lemma algo_sub_wft : forall G A B,
    algo_sub G A B -> okenvp G /\ wft G A /\ wft G B.
Proof with split; destruct_conj; eauto using wf_typ_weakening.
  introv H.
  induction* H...
Qed.

#[export] Hint Extern 1 (wft _ ?A) =>  match goal with
                             | H: algo_sub _ _ _ |- _ =>
                               match type of H with context[A] => forwards (?&?&?): algo_sub_wft H end
                             | Hspl: spli ?B A _, H: algo_sub _ _ _ |- _ =>
                               match type of H with context[B] => forwards (?&?&?): algo_sub_wft H end
                             | Hspl: spli ?B _ A, H: algo_sub _ _ _ |- _ =>
                               match type of H with context[B] => forwards (?&?&?): algo_sub_wft H end
                             | Hspl: splu ?B _ A, H: algo_sub _ _ _ |- _ =>
                               match type of H with context[B] => forwards (?&?&?): algo_sub_wft H end
                             end : core.

Lemma okenvp_inv : forall a PG,
    okenvp (a::PG) -> okenvp PG.
Proof.
  introv Ok. inverts~ Ok.
Qed.

#[export] Hint Immediate okenvp_inv : core.

(******************************************************************************)
(* algorithm correctness *)

(* Lemma 13 *)

Lemma algo_sub_arrow_inv : forall G A B C D,
      algo_sub G (t_arrow A B) (t_arrow C D) ->
      (algo_sub G C A) /\ (algo_sub G B D).
Proof with (try eassumption).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  inverts s; inverts_all_spl; inverts_all_ord; inverts_all_wft; try assumption;
    repeat match goal with
           | H: algo_sub _ (t_arrow _ _) (t_arrow _ _) |- _ => forwards (?&?): IH H; elia; clear H
           end.
  all: split; eauto 3 with *.
  (* refl *)
  all: constructor~; wft_inv.
Qed.

Lemma double_split : forall T A1 A2 B1 B2,
    splu T A1 A2 -> spli T B1 B2 ->
    ((exists C1 C2, spli A1 C1 C2 /\ splu B1 C1 A2 /\ splu B2 C2 A2) \/
    (exists C1 C2, spli A2 C1 C2 /\ splu B1 A1 C1 /\ splu B2 A1 C2)) \/
    ((exists C1 C2, splu B1 C1 C2 /\ spli A1 C1 B2 /\ spli A2 C2 B2) \/
    (exists C1 C2, splu B2 C1 C2 /\ spli A1 B1 C1 /\ spli A2 B1 C2)).
Proof with exists; repeat split*.
  introv Hu Hi.
  indTypSize (size_typ T).
  inverts keep Hu; inverts keep Hi.
  - (* spli or *) left. left...
  - (* spli or *) left. right...
  - (* splu and *) right. left...
  - (* splu and *) right. right...
Qed.

Ltac double_split_inv := match goal with
                           H1: spli ?A _ _, H2: splu ?A _ _ |- _ => forwards [ [?|?] | [?|?] ]: double_split H2 H1
                         end; destruct_conj.

Lemma algo_sub_or_inv : forall G A A1 A2 B,
    algo_sub G A B -> splu A A1 A2 ->
    algo_sub G A1 B /\ algo_sub G A2 B.
Proof with (auto_unify; try eassumption; elia; eauto 3 with SubHd).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; solve_false; auto_unify; auto.
  1,2: split; eauto 3 with *.
  1,4,5: (* splu A *)
    repeat match goal with
              H1 : algo_sub _ ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; clear H1; elia
           end; split...
  1,2:  (* double split A *)
    double_split_inv; inverts_all_wft;
      try match goal with
            H1 : algo_sub _ ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; elia
          end; split...
Qed.

Ltac splu_l_inv := match goal with
                     H1 : algo_sub _ ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): algo_sub_or_inv H1 H2; clear H1; elia
                   end.

Lemma algo_sub_orlr_inv : forall G A B B1 B2,
    algo_sub G A B -> ordu A -> splu B B1 B2 ->
    algo_sub G A B1 \/ algo_sub G A B2.
Proof with (solve_false; auto_unify; try eassumption; elia; eauto 3 with SubHd).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; solve_false; auto_unify; auto.
  1,2: eauto 3 with *.
  1: (* double split *)
    double_split_inv; inverts_all_wft;
      repeat match goal with
               H0: ordu ?A, H1 : algo_sub _ ?A ?B, H2 : splu ?B _ _ |- _ => forwards [?|?]: IH H0 H1 H2; clear H1; elia
             end...
  1,2 : match goal with
              H1 : algo_sub _ ?A ?B, H2 : splu ?B _ _ |- _ => forwards [?|?]: IH H1 H2; elia
        end...
Qed.

Ltac splu_r_inv := match goal with
                     H1 : algo_sub _ ?A ?B, H2 : splu ?B _ _, H3: ordu ?A |- _ => forwards[?|?]: algo_sub_orlr_inv H1 H3 H2; clear H1; elia
                     end.

Lemma algo_sub_and_inv : forall G A B B1 B2,
    algo_sub G A B -> spli B B1 B2 -> algo_sub G A B1 /\ algo_sub G A B2.
Proof with (auto_unify; try eassumption; elia; eauto 3 with SubHd).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; inverts_all_wft; solve_false; auto_unify; auto.
  1,2: split; eauto 3 with *.
  1,3,4,5: (* spli B *)
    repeat match goal with
              H1 : algo_sub _ ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): IH H1 H2; clear H1; elia
           end; split...
  1: splu_l_inv; split...
  1,2:  (* double split A *)
    double_split_inv; inverts_all_wft;
      try match goal with
            H1 : algo_sub _ ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): IH H1 H2; elia
          end; split...
Qed.

Ltac spli_r_inv := match goal with
                     H1 : algo_sub _ ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): algo_sub_and_inv H1 H2; clear H1; elia
                   end.

Lemma algo_sub_andlr_inv : forall G A B A1 A2,
    algo_sub G A B -> spli A A1 A2 -> ordi B ->
    algo_sub G A1 B \/ algo_sub G A2 B.
Proof with (try eassumption; elia; eauto 3 with SubHd).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; inverts_all_wft; solve_false; auto_unify; auto;
    repeat match goal with
              H0: ordi ?B, H1 : algo_sub ?A ?B, H2 : spli ?A _ _ |- _ => forwards [?|?]: IH H1 H2 H0; clear H1; elia
    end.
  1,2: eauto 3 with *.
  1,3,4,5:  (* spli A *)
    repeat match goal with
             H1 : algo_sub _ ?A ?B, H2 : spli ?A _ _ |- _ => forwards[?|?]: IH H1 H2; clear H1; elia
                end...
  1: (* double split *)
    double_split_inv; inverts_all_wft;
      repeat match goal with
               H0: ordi ?B, H1 : algo_sub _ ?A ?B, H2 : spli ?A _ _ |- _ => forwards [?|?]: IH H1 H2 H0; clear H1; elia
             end...
  splu_r_inv...
Qed.

Ltac spli_l_inv := match goal with
                     H1 : algo_sub _ ?A ?B, H2 : spli ?A _ _, H3: ordi ?B |- _ => forwards[?|?]: algo_sub_orlr_inv H1 H2 H3; clear H1; elia
                   end.

(********************************************)
(*                                          *)
(*             Ltac auto_inv                *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end               *)
(*                                          *)
(********************************************)
Ltac auto_inv :=
  repeat try match goal with
         | [ H1: algo_sub _ (t_arrow _ _) (t_arrow _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_arrow_inv H1; clear H1)
         | [ H1: algo_sub _ ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ H1: algo_sub _ ?A ?B, H2: spli ?B _ _ |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1 H2; clear H1)
         | [ H1: algo_sub _ ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ordi ?B, H1: algo_sub _ ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_sub_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algo_sub _ (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: algo_sub_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: algo_sub _ ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): algo_sub_or_inv H1 H2; clear H1)
         | [ H1: algo_sub _ (t_union _ _) ?B |- _ ] =>
           try (forwards~ (?&?): algo_sub_or_inv H1; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: algo_sub _ ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_sub_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: algo_sub _ ?A (t_union _ _) |- _ ] =>
           try (forwards~ [?|?]: algo_sub_orlr_inv H1 Hord; clear H1)
             end.

Lemma trans_via_top : forall G A B,
    algo_sub G t_top B -> wft G A -> algo_sub G A B.
Proof.
  introv s w.
  inductions s; inverts_all_wft; eauto 3 with SubHd; solve_false.
  forwards~ : IHs1. forwards~ : IHs2. applys~ AS_and H.
Qed.

(******************************************************************************)
(** * Nominal types *)
Lemma algo_sub_in_domain_1 : forall G n A,
  algo_sub G (t_prim n) A -> n `in` dom G.
Proof with solve_false.
  introv Sub. apply algo_sub_wft in Sub. destruct_conj.
  applys~ wft_in_domain.
Qed.

Lemma algo_sub_in_domain_2 : forall G n A,
  algo_sub G A (t_prim n) -> n `in` dom G.
Proof with solve_false.
  introv Sub. apply algo_sub_wft in Sub. destruct_conj.
  applys~ wft_in_domain.
Qed.

#[export] Hint Immediate algo_sub_in_domain_1 algo_sub_in_domain_2 : core.

Lemma algo_sub_weakening : forall p G S T,
  algo_sub G S T ->
  okenvp (p::G) ->
  algo_sub (p::G) S T.
Proof with eauto using wf_typ_weakening.
  introv Sub Ok.
  induction Sub; intros; subst...
  1: (* prim_neq *)
    { clear IHSub. destruct p. case_eq (eq_dec a n1); intros; subst.
       - false. apply algo_sub_in_domain_1 in Sub.
         apply okenvp_uniq in Ok. inverts Ok.
         rewrite dom_cons in H6. eauto.
       - applys~ AS_prim_neq.
         applys~ AS_prim_neq.
  }
  1: (* prim_eq *)
    { clear IHSub. destruct p. case_eq (eq_dec a n1); intros; subst.
      - false.
        apply okenvp_uniq in Ok. inverts Ok.
         rewrite dom_cons in H5. eauto.
       - applys~ AS_prim_neq.
         applys~ AS_prim_eq.
  }
  all: try constructor~...
  all: try forwards: IHSub...
  all: try forwards: IHSub1...
  all: try forwards: IHSub2...
  all: try eauto 2 with *.
  all: try solve [applys AS_andl; try eassumption; eauto using wf_typ_weakening].
  all: try solve [applys AS_andr; try eassumption; eauto using wf_typ_weakening].
  all: try solve [applys AS_orl; try eassumption; eauto using wf_typ_weakening].
  all: try solve [applys AS_orr; try eassumption; eauto using wf_typ_weakening].
Qed.

Lemma algo_sub_completeness: forall i A G,
    okenvp G -> binds i A G -> algo_sub G (t_prim i) A.
Proof.
  introv WF HB. gen i A.
  induction WF; intros; solve_false.
  - inverts HB.
    + injection H0; intros; subst.
      applys* AS_top.
    + applys~ algo_sub_weakening.
  - inverts HB.
    + injection H1; intros; subst.
      applys* AS_prim_eq.
    + applys algo_sub_weakening.
      applys* IHWF. constructor*.
Qed.

Lemma algo_sub_prim_eq:  forall PG j n1 A,
    okenvp ((n1,t_prim j) :: PG) ->
    algo_sub PG (t_prim j) A ->
    algo_sub (((n1,t_prim j))::PG) (t_prim n1) A.
Proof with try eassumption.
  introv Uni Sub.
  inductions Sub; solve_false;
    assert (wft ((n1, t_prim j) :: PG) (t_prim n1)) by eauto;
    eauto 3 with SubHd.
  - forwards~ : IHSub1... forwards~ : IHSub2...
    eauto 3 with SubHd.
  - forwards~ : IHSub...
    eauto 3 using wf_typ_weakening with SubHd.
  - forwards~ : IHSub...
    eauto 3 using wf_typ_weakening with SubHd.
Qed.

#[export] Hint Resolve algo_sub_prim_eq : SubHd.

Lemma algo_sub_prim_strenthen_head : forall i A G n B,
    algo_sub ((i, A) :: G) (t_prim n) B -> i <> n -> wft G B -> algo_sub G (t_prim n) B.
Proof with try eassumption; eauto 3 with SubHd.
  introv Sub Neq Wf.
  inductions Sub; solve_false...
  all: try assert (okenvp G) by inverts~ H.
  all: assert (HWF: wft ((i, A) :: G) (t_prim n)) by eauto.
  all: assert (wft G (t_prim n)).
  all: inverts HWF as Bind; inverts Bind as Heq;
    try injection Heq; intros; subst*; eauto; try solve [contradiction].
  all: eauto 3 with SubHd.
  - forwards~ : IHSub1. eauto. forwards~ : IHSub2...
Qed.


Lemma algo_sub_prim_ord : forall G n A,
   algo_sub G (t_prim n) A -> ordu A -> ordi A -> A = t_top \/ exists m, A = t_prim m.
Proof.
  introv Sub Ord1 Ord2.
  inductions Sub; solve_false.
  all: try solve [left~].
  all: try solve [right*].
Qed.
(******************************************************************************)
Ltac eassumption_spl :=
  match goal with
    | |- spli _ _ _ => try eassumption
    | |- splu _ _ _ => try eassumption
  end.
#[export] Hint Extern 0 => eassumption_spl : core.

Local Ltac algo_trans_autoIH :=
  match goal with
  | [ IH: forall G : envp, _ , H1: algo_sub _ ?A ?B , H2: algo_sub _ ?B ?C |- algo_sub _ ?A ?C ] =>
    (applys~ IH H1 H2; elia; auto)
  | [ IH: forall G : envp, _ , H1: algo_sub _ ?A ?B  |- algo_sub _ ?A ?C ] =>
    (applys~ IH H1; elia; try constructor~)
  | [ IH: forall G : envp, _ , H2: algo_sub _ ?B ?C |- algo_sub _ ?A ?C ] =>
    (applys~ IH H2; elia; try constructor~)
  end.

Lemma algo_sub_prim_neq : forall i A n m G,
    algo_sub ((i,A)::G) (t_prim n) (t_prim m) -> i <> n -> i <> m.
Proof.
  introv Sub Neq.
  inverts Sub; solve_false.
  - subst. apply okenvp_uniq in H4. inverts H4.
    forwards* : algo_sub_in_domain_2 G m.
Qed.

Lemma algo_sub_trans : forall G A B C, algo_sub G A B -> algo_sub G B C -> algo_sub G A C.
Proof with (solve_false; auto_unify; try eassumption_spl; auto_inv; inverts_all_wft; eauto 3 with SubHd; try solve algo_trans_autoIH).
  introv s1 s2.
  indTypEnvSize (size_envp G + size_typ A + size_typ B + size_typ C).
  forwards(?&?&?): algo_sub_wft s1. forwards(?&?&?): algo_sub_wft s2.
  lets [Hi|(?&?&Hi)]: ordi_or_split C...
  - lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split B...
      lets [Hu'|(?&?&Hu')]: ordu_or_split B...
      lets [Hi''|(?&?&Hi'')]: ordi_or_split A...
      * (* double ord A B *)
        assert (okenvp G) by eauto.
        inverts keep s1; auto_unify...
        ** (* prim neq *)
          lets [Hu''|(?&?&Hu'')]: ordu_or_split C.
          *** forwards~ [?|(?&?)]: algo_sub_prim_ord s2 Hu''; subst; solve_false.
              1: { eauto 4 with SubHd. }
              applys algo_sub_weakening.
              applys~ IH...
              applys~ algo_sub_prim_strenthen_head s2.
              { assert (n2 `in` dom PG) by applys* wft_in_domain.
                apply okenvp_uniq in H. inverts H. intro HF. subst*. }
              { applys wft_strenthen_prim. now eauto.
                applys algo_sub_prim_neq s2.
                applys~ algo_sub_prim_neq s1. }
              now elia. now auto.
          *** auto_inv.
              { applys AS_orl... }
              { applys AS_orr... }
        ** (* prim eq *)
          lets [Hu''|(?&?&Hu'')]: ordu_or_split C.
          *** forwards~ [?|(?&?)]: algo_sub_prim_ord s2 Hu''; subst; solve_false.
              1: { eauto 4 with SubHd. }
              case_eq (eq_dec n1 n2); intros; subst~.
              applys~ algo_sub_prim_eq.
              apply algo_sub_prim_strenthen_head in s2; auto.
              applys IH... now elia.
              { applys wft_strenthen_prim. now eauto.
                applys~ algo_sub_prim_neq s2. }
          *** auto_inv.
              { applys AS_orl... }
              { applys AS_orr... }
        ** (* top *) applys~ trans_via_top.
        ** (* arrow *) inverts~ s2...
           (* *** applys AS_top... *)
           *** applys AS_arrow...
           *** applys AS_orl...
           *** applys AS_orr...
      * applys AS_andl...
      * applys AS_andr...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split A...
      * applys AS_or Hu...
      * assert (algo_sub G x C)...
        assert (algo_sub G x0 C)...
  - applys AS_and Hi...
Qed.

#[export] Hint Resolve algo_sub_trans : SubHd.

Lemma algo_sub_symm_and: forall G A B,
    wft G A -> wft G B -> okenvp G -> algo_sub G (t_and A B) (t_and B A).
Proof with eauto 3 with SubHd.
  intros. applys~ AS_and...
Qed.

Lemma algo_sub_symm_or: forall G A B,
    wft G A -> wft G B -> okenvp G ->
    algo_sub G (t_union A B) (t_union B A).
Proof with eauto 3 with SubHd.
  intros. applys~ AS_or...
Qed.

Ltac split_inter_constructors :=
  applys* SpI_and + applys* SpI_orl +
  applys* SpI_arrow + applys* SpI_orl.
Ltac split_union_constructors :=
  applys* SpU_or + applys* SpU_andl.
Ltac swap_or_r := applys algo_sub_trans; [ | applys algo_sub_symm_or ].
Ltac swap_and_l := applys algo_sub_trans; [ (applys algo_sub_symm_and) | ].
Ltac split_r := applys AS_and; try split_inter_constructors.
Ltac split_l := applys AS_or; try split_union_constructors.
Ltac use_left_l := applys AS_andl; try split_inter_constructors.
Ltac use_right_l := applys AS_andr; try split_inter_constructors.
Ltac use_left_r := applys AS_orl; try split_union_constructors.
Ltac use_right_r := applys AS_orr; try split_union_constructors.

Ltac match_or := split_l; [ use_left_r | use_right_r].
Ltac match_and := split_r; [ use_left_l | use_right_l].
Ltac match_or_rev := split_l; [ use_right_r |  use_left_r ].
Ltac match_and_rev := split_r; [ use_right_l | use_left_l ].
Ltac swap_or_l := applys algo_sub_trans; [ applys algo_sub_symm_or | ].
Ltac swap_and_r := applys algo_sub_trans; [ | (applys algo_sub_symm_and) ].

Lemma algo_sub_distArrU: forall G A B C,
    wft G A -> wft G B -> wft G C -> okenvp G ->
    algo_sub G (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_union A B) C).
Proof with eauto.
  introv.
  indTypSize (size_typ C).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split C.
  - applys AS_and; eauto 3 with SubHd.
    use_left_l... use_right_l...
  - (* split C x x0 *)
    forwards~ Hs1: IH A B x... now elia.
    forwards~ Hs2: IH A B x0... now elia.
    applys AS_and. now eauto 3 with SubHd.
    + applys algo_sub_trans Hs1. match_and...
      applys AS_arrow... eauto 3 with SubHd.
      applys AS_arrow... eauto 3 with SubHd.
    + applys algo_sub_trans Hs2. match_and...
      applys AS_arrow... eauto 3 with SubHd.
      applys AS_arrow... eauto 3 with SubHd.
Qed.

#[export] Hint Resolve algo_sub_distArrU : SubHd.

Local Ltac auto_sub :=
  match goal with
        | |- algo_sub _ (t_arrow (t_union _ _) _) (t_and _ _) => split_r; auto_sub
        | H1: algo_sub _ ?A ?B, H2: algo_sub _ ?B ?C |- algo_sub _ ?A ?C => applys algo_sub_trans H1 H2
        | |- algo_sub _ ?A (t_union ?A _) => use_left_r; auto
        | |- algo_sub _ ?A (t_union _ ?A) => use_right_r; auto
        | |- algo_sub _ (t_and ?A _) ?A => use_left_l; auto
        | |- algo_sub _ (t_and _ ?A) ?A => use_right_l; auto
        | |- algo_sub _ ?A ?A => applys AS_refl; auto_sub
        | |- algo_sub _ (t_arrow _ _) (t_arrow _ _) => applys AS_arrow; auto_sub
        | |- algo_sub _ (t_and _ _) (t_and _ _) => match_and; auto with *
        | |- algo_sub _ (t_and (t_union _ _) (t_union _ _)) (t_union (t_and _ _) _) =>
          match_and; auto with *
        | |- algo_sub _ (t_and (t_union _ _) (t_union _ _)) (t_union _ (t_and _ _)) =>
          swap_or_r; auto with *; match_and; match_or_rev; auto with *

        | |- algo_sub _ _ (t_union _ _) => match_or; try applys AS_refl; auto with *
        | |- algo_sub _ (t_union _ _) (_ (t_union _ _)) => match_or; auto with *
        | |- algo_sub _ (t_and (t_union _ _) _) (t_union (t_and _ _) (t_and _ _)) =>
          match_or; auto with *
        | |- algo_sub _ (t_and _ (t_union _ _)) (t_union (t_and _ _) (t_and _ _)) =>
          swap_and_l; auto with *; match_or; match_and_rev; auto with *

        | |- algo_sub _ (t_and _ _) (_ (t_and _ _)) => match_and; auto with *
        | |- algo_sub _ (t_union _ _) (_ _ (t_union _ _)) => match_or; auto with *
        | |- algo_sub _ (_ _ (t_and _ _)) (t_and _ _) => match_and; auto with *
        | |- _ => auto
  end.


Lemma algo_sub_soundness: forall i j G,
    algo_sub G (t_prim i) (t_prim j) ->
    i=j \/ binds i (t_prim j) G \/ exists A, binds i A G /\ algo_sub G A (t_prim j).
Proof.
  introv Sub.
  inductions Sub; solve_false.
  - now tauto.
  - forwards~ [?|[?|(?&?&?)]]: IHSub.
    right. right. exists. splits*.
    applys~ algo_sub_weakening.
  - right. right. exists (t_prim j0). splits*.
    applys~ algo_sub_weakening.
Qed.

(******************************************************************************)
#[export] Hint Constructors declarative_subtyping : SubHd.

Lemma DS_distArrRev : forall PG (A B1 B2:typ),
     okenvp PG ->
     wft PG A -> wft PG B1 -> wft PG B2 ->
     declarative_subtyping PG (t_arrow A (t_and B1 B2)) (t_and  (t_arrow A B1)   (t_arrow A B2) ).
Proof.
  introv Ok Wf1 Wf2 Wf3.
  applys* DS_and; applys DS_arrow; eauto with SubHd.
Qed.

Lemma DS_distArrURev : forall PG (A1 A2 B:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_arrow (t_union A1 A2) B) (t_and  (t_arrow A1 B)   (t_arrow A2 B) ).
Proof.
  introv Ok Wf1 Wf2 Wf3.
  applys* DS_and; applys DS_arrow; eauto with SubHd.
Qed.

Lemma dsub_symm_and: forall G A B,
    okenvp G -> wft G A -> wft G B -> declarative_subtyping G (t_and A B) (t_and B A).
Proof.
  intros.
  applys DS_and; eauto with SubHd.
Qed.

Lemma dsub_symm_or: forall G A B,
    okenvp G -> wft G A -> wft G B -> declarative_subtyping G (t_union A B) (t_union B A).
Proof.
  intros.
  applys DS_or; eauto with SubHd.
Qed.

#[export] Hint Resolve dsub_symm_and dsub_symm_or : SubHd.

Lemma DS_distAnd : forall PG (A1 A2 B:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_union A1 A2)  B) (t_union  (t_and A1 B)   (t_and A2 B) ).
Proof.
  introv Ok Wf1 Wf2 Wf3.
  applys DS_trans; [ | applys~ DS_distOr].
  applys DS_and; applys DS_trans.
  2,4: applys~ dsub_symm_or.
  all: applys DS_trans; [ | applys~ DS_distOr]; applys DS_and.
  all: applys DS_trans; [ | applys~ dsub_symm_or].
  1: applys* DS_andl.
  all: applys DS_trans.
  1,3,5: applys~ DS_andr.
  all: try solve [applys~ DS_orl]; try solve[applys~ DS_orr].
Qed.

#[export] Hint Resolve DS_distArrRev DS_distArrURev DS_distAnd : SubHd.

Lemma decl_sub_weakening : forall p G S T,
  declarative_subtyping G S T ->
  okenvp (p::G) ->
  declarative_subtyping (p::G) S T.
Proof with eauto 4 using wf_typ_weakening with SubHd.
  introv Sub Ok.
  induction Sub; intros; subst...
  all: constructor...
  destruct p. applys~ binds_cons_3.
Qed.

Lemma dsub_splu: forall G A B C,
    splu A B C -> okenvp G -> wft G A -> declarative_subtyping G B A /\ declarative_subtyping G C A.
Proof with intuition.
  introv Spl Ok Wf.
  induction Spl; inverts_all_wft; intuition eauto.
  all: try forwards (?&?): IHSpl.
  all: eauto 3 with SubHd.
  - applys DS_and. applys~ DS_trans. applys~ DS_andl. now auto.
    applys~ DS_andr.
  - eauto with SubHd.
  - eauto with SubHd.
  - eauto with SubHd.
Qed.

Lemma dsub_spli: forall G A B C,
    spli A B C -> okenvp G -> wft G A -> declarative_subtyping G A B /\ declarative_subtyping G A C.
Proof with intuition.
  introv Spl Ok Wf.
  induction Spl; inverts_all_wft; forwards~ : dsub_splu; intuition eauto.
  all: try forwards (?&?): IHSpl.
  all: eauto 3 with SubHd.
  all: eauto with SubHd.
Qed.

#[export] Hint Resolve dsub_splu dsub_spli : SubHd.


Lemma dsub_or: forall G A B C,
    okenvp G -> wft G A -> splu A B C -> declarative_subtyping G A (t_union B C).
Proof with (inverts_all_wft; eauto 3 with SubHd).
  introv Ok Wf Spl.
  induction Spl; try intuition; eauto 3 with SubHd.
  - applys DS_trans.
    2: { applys* DS_distAnd... }
    applys* DS_and... applys DS_trans. applys* DS_andl.
    applys* IHSpl.
  - applys~ DS_trans. applys~ dsub_symm_and.
    applys DS_trans (t_union (t_and B1 A) (t_and B2 A)).
    1: { applys~ DS_trans.
        2: { applys~ DS_distAnd... }
        applys* DS_and... applys DS_trans. applys* DS_andl.
    applys* IHSpl. }
    applys DS_or.
    applys DS_trans (t_and A B1)...
    applys DS_trans (t_and A B2)...
Qed.

Lemma dsub_and: forall G A B C,
    okenvp G -> wft G A -> spli A B C -> declarative_subtyping G (t_and B C) A.
Proof with (inverts_all_wft; eauto 3 with SubHd).
  introv Ok Wf Spl.
  induction Spl; try intuition; eauto 3 with SubHd.
  - forwards: IHSpl... applys DS_trans...
  - forwards: dsub_or H0... applys DS_trans...
  - applys DS_trans.
    1: { applys DS_distOr... }
    applys DS_or... applys DS_trans...
  - applys DS_trans. 2: { applys dsub_symm_or... }
    applys DS_trans (t_and (t_union B1 A) (t_union B2 A))...
    2: { applys DS_trans. applys DS_distOr...
         applys DS_or... applys DS_trans... }
    applys DS_and.
    applys DS_trans (t_union A B1)...
    applys DS_trans (t_union A B2)...
Qed.

#[export] Hint Resolve dsub_and dsub_or : SubHd.

#[export] Hint Extern 1 (okenvp ?G) =>  match goal with
                             | H: algo_sub _ _ _ |- _ =>
                               match type of H with context[G] => forwards (?&?&?): algo_sub_wft H end
                             end : core.

Ltac inverts_all_wft_2 :=
  repeat match goal with
         | H: wft _ (_ _ _) |- _ => inverts H
         | H: wft _ (_ _) |- _ => inverts H
         | H: wft _ ?A, Hspl: spli ?A _ _ |- _ => forwards: wft_spli_1 Hspl H; forwards: wft_spli_2 Hspl H; clear H
         | H: wft _ ?A, Hspl: splu ?A _ _ |- _ => forwards: wft_splu_1 Hspl H; forwards: wft_splu_2 Hspl H; clear H
         | H: algo_sub _ _ _ |- wft _ _ => forwards (?&?&?): algo_sub_wft H; clear H
         end.

(* Equivalence of subtyping *)
(* Lemma 14 *)

Theorem dsub2asub: forall G A B,
    declarative_subtyping G A B <-> algo_sub G A B.
Proof with (simpl in *; try applys SpI_and; try applys SpU_or; inverts_all_wft_2; try eassumption; eauto 3 with SubHd).
  split; introv H.
  - induction H...
    all: try solve [ auto_sub ].
    + applys~ algo_sub_completeness.
  - induction H; auto with SubHd.
    + (* prim *) applys~ decl_sub_weakening.
    + (* prim eq *) applys DS_trans.
      2: { applys* decl_sub_weakening. }
      applys~ DS_prim.
    + (* and *)
      applys DS_trans (t_and B1 B2)... applys dsub_and...
    + (* andl *)
      forwards (?&?): dsub_spli PG H0...
    + (* andr *)
      forwards (?&?): dsub_spli PG H0...
    +  (* or *)
      applys DS_trans (t_union A1 A2)... applys dsub_or...
    + (* orl *)
      forwards (?&?): dsub_splu PG H0...
    + (* orr *)
      forwards (?&?): dsub_splu PG H0...
Qed.

Lemma wft_dec : forall G A, wft G A \/ ~ wft G A.
Proof.
  intros. induction* A.
  all: try solve [destruct IHA1; destruct IHA2; auto].
  induction G.
  - right. intro HF. inverts* HF.
  - destruct a.
    case_eq (eq_dec a n); intros; subst*.
    destruct IHG.
    + left*. apply wft_in_domain in H0.
      lets (?&?): binds_In_inv H0.
      econstructor. applys* binds_cons.
    + right. intro HF. apply H0.
      inverts HF. rewrite_env (nil ++ [(a,t)] ++ G) in H2.
      apply binds_remove_mid in H2. all: now eauto.
Qed.

#[export] Hint Immediate okenvp_uniq : core.

(* Lemma uniq_dec : forall (G: envp), uniq G \/ ~ uniq G. *)
(* Proof. *)
(*   introv. induction* G. *)
(*   destruct IHG. *)
(*   - destruct a. *)
(*     assert (HIn: a `in` dom G \/ a `notin` dom G) by *)
(*         forwards~ [?|?]: AtomSetNotin.D.FSetDecideAuxiliary.dec_In a (dom G). *)
(*     destruct* HIn. *)
(*     right. intro Uni. inverts~ Uni. *)
(*   - right. intro Uni. inverts~ Uni. *)
(* Qed. *)

Lemma okenvp_dec : forall G, okenvp G \/ ~ okenvp G.
Proof.
  introv. induction* G.
  destruct IHG.
  - destruct a. destruct t.
    all: try solve [right; intro HF; inverts HF].
    + forwards* [?|?]: AtomSetNotin.D.FSetDecideAuxiliary.dec_In a (dom G).
      right*. intro Ok. inverts~ Ok.
    + forwards* [?|?]: wft_dec G (t_prim n).
      * forwards* [?|?]: AtomSetNotin.D.FSetDecideAuxiliary.dec_In a (dom G).
        right*. intro Ok. inverts~ Ok.
      * right; intro HF; inverts~ HF.
  - right*.
Qed.

Lemma algo_sub_prim_dec : forall G n m,
    okenvp G ->
    algo_sub G (t_prim n) (t_prim m) \/ ~ algo_sub G (t_prim n) (t_prim m).
Proof.
  introv Ok. gen n m.
  induction G; intros.
  - right. intro HF. forwards : algo_sub_wft HF. destruct_conj.
    inverts H0. inverts H3.
  - forwards* [?|?]: IHG n m.
    + left. applys~ algo_sub_weakening.
    + destruct a. case_eq (a==n); intros; subst.
      * case_eq (n==m); intros; subst*.
        destruct t; try solve [inverts Ok].
        ** right; intro HF.
           inverts HF; solve_false.
        ** forwards* [?|?]: IHG n1 m.
           *** left. applys algo_sub_trans.
               2: applys~ algo_sub_weakening H2.
               applys* AS_prim_eq.
           *** right; intro HF.
               inverts HF; solve_false.
      * right; intro HF. apply H.
        forwards~ : algo_sub_prim_neq HF.
        applys~ algo_sub_prim_strenthen_head HF.
        applys* wft_strenthen_prim H1.
Qed.

(* Decidability of subtyping *)

(* Lemma 15 *)

Theorem decidability : forall G A B,
    algo_sub G A B \/ not (algo_sub G A B).
Proof with (simpl in *; solve_false; jauto; elia; try solve [right; intros HF; auto_inv; inverts HF; simpl in *; solve_false]; eauto 3 with SubHd).
  introv.
  indTypSize (size_typ A + size_typ B).
  lets [?|?]: okenvp_dec G. 2: { right. intro HF. applys* H. }
  lets [?|?]: wft_dec G A. 2: { right. intro HF. applys* H0. }
  lets [?|?]: wft_dec G B. 2: { right. intro HF. applys* H1. }
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - lets [Hi'|(?&?&Hi')]: ordi_or_split A.
    + lets [Hu|(?&?&Hu)]: ordu_or_split A.
      * lets [Hu'|(?&?&Hu')]: ordu_or_split B.
        ** (* all ordinary *)
          destruct A; destruct B...
          *** forwards [IHA1|IHA1] : IH B1 A1...
              forwards [IHA2|IHA2] : IH A2 B2...
          *** applys~ algo_sub_prim_dec.
        ** (* spl > B, S-orl/r *)
          forwards [IHA1|IHA1] : IH A x...
          forwards [IHA2|IHA2] : IH A x0...
      * forwards [IHA1|IHA1] : IH x B...
        forwards [IHA2|IHA2] : IH x0 B...
    + (* spl < A, S-andl/r *)
      forwards [IHA1|IHA1] : IH x B...
      forwards [IHA2|IHA2] : IH x0 B...
  - (* spl < B, S-and *)
    forwards [IHA1|IHA1] : IH A x...
    forwards [IHA2|IHA2] : IH A x0...
Qed.
