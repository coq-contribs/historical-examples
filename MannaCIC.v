(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                               May 1st 1998                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 Manna.v                                  *)
(****************************************************************************)
    (*******************************************************************)
    (* f : nat->nat is an increasing and unbounded function            *)
    (* lambo(f)(n) = inf {m:nat| f(m)>n}                               *)
    (* is computed using the following algorithm :                     *)
    (* lambo f n = if f(0) > n the 0 else limbo(1)                     *)
    (*        where limbo(i) = if f(i) > n then 0                      *)
    (*                         else let j = limbo(2i) in               *)
    (*                  if f(j+i) > n then j else j+i                  *)
    (*******************************************************************)


Require Import Relation_Definitions.

Definition one : nat := 1.

(* Addition and multiplication by 2 *)
Fixpoint add (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

Definition twice (n : nat) : nat := add n n.

Definition peano :
  forall P : nat -> Prop,
  P 0 -> (forall u : nat, P u -> P (S u)) -> forall n : nat, P n := nat_ind.


(* Operator for pattern-matching *)
 Definition nat_match (n : nat) (P : nat -> Prop) (h1 : P 0)
   (h2 : forall m : nat, P (S m)) : P n :=
   peano P h1 (fun (m : nat) (ind : P m) => h2 m) n.

(* Properties of addition                         *)
Theorem add_nO : forall n : nat, add n 0 = n.
intro; symmetry  in |- *; apply plus_n_O.
Qed.

Theorem add_ass : forall u v w : nat, add (add u v) w = add u (add v w).
intros.
elim u; auto.
intros; simpl in |- *.
elim H; auto.
Qed.

(* Induction de contenu positif                        *)
Definition peano_set :
  forall P : nat -> Set,
  P 0 -> (forall u : nat, P u -> P (S u)) -> forall n : nat, P n := nat_rec.

(* Absurdity *)

 Theorem abs : forall A : Prop, False -> A.
 intros; elim H; auto.
 Qed.

(* An axiomatized order relation on natural numbers *)

 Parameter inf : nat -> nat -> Prop.

 Axiom tran_inf : transitive nat inf.
 Axiom infOO : inf 0 0.
 Axiom infS_inf : forall n m : nat, inf (S n) (S m) -> inf n m.
 Axiom inf_infS : forall n m : nat, inf n m -> inf (S n) (S m).
 Axiom infS : forall n : nat, inf n (S n).
 Axiom absO : inf one 0 -> False.

 Definition sup (n m : nat) : Prop := inf (S m) n.

(* Properties of this order *)

 Lemma re_inf : forall n : nat, inf n n.
 intro; elim n.
 apply infOO.
 intros; apply inf_infS; auto.
 Qed.
      
 Lemma infO : forall n : nat, inf 0 n.
 intro; elim n.
 apply infOO.
 intros; apply (tran_inf 0 n0 (S n0)); auto.
 apply infS.
 Qed.

 Lemma infS_O : forall n : nat, inf (S n) 0 -> False.
 intro; elim n; intros.
 apply absO; auto.
 elim H.
 apply (tran_inf (S n0) (S (S n0)) 0); auto.
 apply infS.
 Qed.

 Lemma infSn_n : forall n : nat, inf (S n) n -> False.
 intro; elim n; intros.
 apply absO; auto.
 elim H.
 apply infS_inf; auto.
 Qed.

 Lemma inf_sup_abs : forall n m : nat, inf n m -> sup n m -> False.
 intros; apply (infSn_n n).
 apply (tran_inf (S n) (S m) n); auto.
 apply inf_infS; auto.
 Qed.

(* A lemma : (sup n m)->(sup (twice n) (S m)) *)

 Lemma inf_add : forall n m : nat, inf m (add n m).
 intros; elim n.
 apply re_inf.
 intros; apply (tran_inf m (add n0 m) (add (S n0) m)); auto.
 simpl in |- *; apply infS.
 Qed.

 Lemma sup_twice : forall n m : nat, sup n m -> sup (twice n) (S m).
 intros n m; elim n; intros.
 apply abs.
 apply (infS_O m H).
 apply (inf_infS (S m) (add n0 (S n0))).
 apply (tran_inf (S m) (S n0) (add n0 (S n0))); auto.
 apply inf_add.
 Qed.

(* Program Lambo *)

(* Hypotheses *)
Variable f : nat -> nat.

(* f is unbounded *)
Hypothesis Unbound : forall n : nat, {y : nat | sup (f y) n}.

(* f is increasing *)
Hypothesis Increas : forall n m : nat, inf n m -> inf (f n) (f m).

(* There is a procedure to decide if inf or sup hold *)

Axiom inf_sup : forall x y : nat, {inf x y} + {sup x y}.
Axiom inf_sup0 : forall x y : nat, inf x y \/ sup x y.

(* We give n : nat and try to compute lambo(n) *)
Variable n : nat.

 Definition Inf (m : nat) : Prop := inf (f m) n.
 Definition Sup (m : nat) : Prop := sup (f m) n.

(* We only use the following properties of Inf and Sup *)

 Definition bound : {y : nat | sup (f y) n} := Unbound n.

 Definition Inf_Sup (u : nat) : {Inf u} + {Sup u} := inf_sup (f u) n.

 Definition Inf_Sup_abs (u : nat) : Inf u -> Sup u -> False :=
   inf_sup_abs (f u) n.

(* F is increasing is used this way *)

 Lemma infInf : forall u v : nat, inf u v -> Inf v -> Inf u.
 intros; apply (tran_inf (f u) (f v) n); auto.
 apply Increas; auto.
 Qed.

(* Setifications *)
 Definition Small (m : nat) : Prop := forall i : nat, inf (S i) m -> Inf i.

 Lemma SmallO : Small 0.
 red in |- *; intros; apply abs; apply (infS_O i H).
 Qed.

(* The initial specification *)
 Definition Lambo : Set := {m : nat | Sup m &  Small m}.

 Fact Lem1 : forall m : nat, Inf m -> Small (S m).
 red in |- *; intros; apply (infInf i m); auto.
 apply infS_inf; auto.
 Qed.

(* Transformation of the specification *)
 Definition Lambo1 : Set := {m : nat | Inf m &  Sup (S m)} + {Sup 0}.

 Lemma Reduct1 : Lambo1 -> Lambo.
 intro h; elim h.
 intro h1; elim h1; intros m f1 f2.
 red in |- *; exists (S m); auto.
 apply Lem1; auto.
 intro; red in |- *; exists 0; auto.
 exact SmallO.
 Qed.

(* Intermediate function *)
 Definition Limbo (i : nat) : Set :=
   sup i 0 -> {m : nat | Inf m &  Sup (add i m)} + {Sup 0}.

(* (add one m)=(S m) by Beta reduction *)

 Lemma Reduct2 : Limbo one -> Lambo1.
 intro; apply H.
 apply (re_inf one).
 Qed.

(* Termination *)

(* A parametrized order *)
 Definition bd (y u v : nat) : Prop := sup u v /\ inf v y.

(* Property to be well-formed *)
 Definition wf_bd (y i : nat) : Set :=
   forall P : nat -> Set,
   (forall v : nat, (forall u : nat, bd y u v -> P u) -> P v) -> P i.

(* Some property of bd *)

 Fact Lem2 : forall y1 y2 u v : nat, bd y1 u v -> inf v y2 -> bd y2 u v.
 intros; elim H; intros.
 red in |- *; auto.
 Qed.

 Fact Lem3 : forall y u v w : nat, bd y u v -> bd y v w -> sup y w.
 intros; apply (tran_inf (S w) v y); auto.
 elim H0; auto.
 elim H; auto.
 Qed.

 Lemma Term : forall i y : nat, sup i y -> wf_bd y i.
 red in |- *; intros i y h P q.
 apply q.
 intros.
 apply except.
 apply (inf_sup_abs i y); auto. 
 elim H; auto.
 Qed.

(* Proof of (wf_bd y) by induction on y *)

 Lemma cas_base : forall i : nat, sup i 0 -> wf_bd 0 i.
 red in |- *; intros i h P q.
 apply q.
 intros; apply except.
 apply (inf_sup_abs i 0); auto.
 elim H; auto.
 Qed.

 Lemma cas_ind : forall i y : nat, wf_bd y i -> wf_bd (S y) i.
 red in |- *; intros.
 apply H; intros.
 apply H0; intros.
 elim (inf_sup v y); intros.
 apply H1.
 apply (Lem2 (S y) y u v); auto.
 apply H0; intros.
 apply except.
 apply (infSn_n v).
 apply (tran_inf (S v) (S y) v); auto.
 apply (Lem3 (S y) u0 u v); auto.
 Qed.

Theorem Wf1 : forall y i : nat, sup i 0 -> wf_bd y i.
intros; elim y.
apply cas_base; auto.
intros; apply cas_ind; auto.
Qed.

(* Actually we will use a simpler induction scheme *)

 Definition Induct (y i : nat) (P : nat -> Set) : Set :=
   (forall k : nat, (inf k y -> P (twice k)) -> P k) -> P i.

(* Proof of the induction scheme *)
Theorem wf_Ind :
 forall y i : nat, sup i 0 -> forall P : nat -> Set, Induct y i P.
intros.
elim y; red in |- *; intros.
apply H0; intros.
apply except.
apply (inf_sup_abs i 0); auto.
apply H0; intros.
apply H1; intros.
elim (inf_sup k n0); intros.
apply H2; auto.
apply H1; intros.
apply except.
apply (inf_sup_abs (twice k) (S n0)); auto.
apply sup_twice; auto.
Qed.

(* Proof of the Limbo's program  *)

 Fact Lem4 : forall u v : nat, Sup u -> Inf v -> inf v u.
 intros.
 elim (inf_sup0 v u); intros.
 apply H1.
 apply abs.
 apply (Inf_Sup_abs u); auto.
 apply (infInf u v); auto.
 apply (tran_inf u (S u) v); auto.
 apply infS.
 Qed.

 Definition LimboSig (i : nat) : Set := {m : nat | Inf m &  Sup (add i m)}.

 Lemma LimboLem : forall i : nat, sup i 0 -> Inf 0 -> LimboSig i.
 intros; elim bound.
 intros.
 apply (wf_Ind x i H LimboSig); intros.
 elim (Inf_Sup (add k 0)); intros.
 elim H1; intros.
 elim (Inf_Sup (add k x0)); intros.
 red in |- *; exists (add k x0); auto.
 unfold twice in q.
 elim add_ass; auto.
 red in |- *; exists x0; auto.
 apply Lem4; auto.
 elim (add_nO k); auto.
 red in |- *; exists 0; auto.
 Qed.

 Lemma Prog : forall i : nat, Limbo i.
 red in |- *; intros.
 elim (Inf_Sup 0); intros.
 left; apply (LimboLem i H a).
 right; auto.
 Qed.

(* Final proof *)
Theorem LamboProg : Lambo.
exact (Reduct1 (Reduct2 (Prog one))).
Qed.




(* $Id$ *)