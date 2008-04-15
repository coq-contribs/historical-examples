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


(* This a reconstruction in Coq V8.0 syntax of the file Tarski.v from CoC V4.4

   Until CoC V4.8, the Section mechanism were more Automath-like: a
   Discharge command had the effect of resetting the local section of
   variables to a previous point. At this time, syntax extensions
   were not incrementally declarable but hard-wired in the yacc parser.

   The first known version of Tarski.v goes back to CoC V1.10. Until
   CoC V4.3, it was called Tarski.ml (there were no stand-alone parser
   before V4.3).
*)

(****************************************************************************)
(*                                                                          *)
(*                          Constructions in Caml                           *)
(*		                                                            *)
(*                           Tarski's theorem                               *)
(*		                                                            *)
(*             CAML V2.5    Constructions V4.3     Vernacular V1.1          *)
(****************************************************************************)

(* Preliminaries  *)

Section AND.

(* La conjonction dans le calcul minimal de 2nd ordre, selon Russell *)
  Variable p q : Prop.  

(* AND p q  proves any prop r which follows from p and q *)

  Definition AND := forall r : Prop, (p -> q -> r) -> r.  

(* Pairing, as conjunction introduction *)

  	Variable h1 : p.  
  	Variable h2 : q.  
  
		Theorem and : AND.
		Proof fun (r : Prop) (h : p -> q -> r) => h h1 h2.  

End AND.

Notation "A /\ B" := (AND A B) : type_scope.

(* Tarski's fixed-point theorem *)

Section Tarski.

(* All the hypotheses *)

  Variable A : Type.  
  Variable R : A -> A -> Prop.  
  Variable Rtrans : forall x y z : A, R x y -> R y z -> R x z.  
  Variable F : (A -> Prop) -> A.  
  Variable Upperb : forall (P : A -> Prop) (x : A), P x -> R x (F P).  
  Variable
    Least :
      forall (P : A -> Prop) (x : A),
      (forall y : A, P y -> R y x) -> R (F P) x.  
  Variable f : A -> A.  
  Variable Incr : forall x y : A, R x y -> R (f x) (f y).  

(* The construction of the proof *)

  Definition P0 (x : A) := R x (f x).  
  Definition x0 := F P0.  

(* the proof that x0 is a fixed point*)

Section lemme1.

  	Variable x : A.  
  	Variable h1 : R x (f x).  
  	Theorem lemme1 : R x (f x0).
	Proof Rtrans x (f x) (f x0) h1 (Incr x x0 (Upperb P0 x h1)).  

End lemme1.
  
Lemma fact1 : R x0 (f x0).
Proof Least P0 (f x0) lemme1.  
  
Lemma fact2 : R (f x0) x0.
Proof Upperb P0 (f x0) (Incr x0 (f x0) fact1).  

Theorem Tarski : R x0 (f x0) /\ R (f x0) x0.
Proof and (R x0 (f x0)) (R (f x0) x0) fact1 fact2.  

End Tarski.

(* An application : Knaster-Tarski's theorem *)

Section Knaster.

  Variable U : Type.   
(* The current universe *)

  Definition set := U -> Prop.  
  Definition Subset (x y : set) := forall u : U, x u -> y u.  
  Definition Equal (x y : set) := Subset x y /\ Subset y x.  
  Definition Class := set -> Prop.  
  Definition Map := set -> set.  
  Variable Phi : Map.  
  Variable Incr : forall x y : set, Subset x y -> Subset (Phi x) (Phi y).  
(* Here F will be union, defined as follows *)

(* (Over C x) iff x contains all the elements of all the sets in C *)
  Definition Over (C : Class) (x : set) := forall y : set, C y -> Subset y x.  
  Definition Union (C : Class) (u : U) := forall x : set, Over C x -> x u.  
(* Union has all the required properties *)

  Definition Subset_trans (x y z : set) (h1 : Subset x y) 
    (h2 : Subset y z) (u : U) (h3 : x u) := h2 u (h1 u h3).  
  Definition Union_upperb (C : Class) (x : set) (h1 : C x) 
    (u : U) (h2 : x u) (y : set) (h3 : Over C y) := 
    h3 x h1 u h2.  
  Definition Union_least (C : Class) (x : set)
    (h1 : forall y : set, C y -> Subset y x) (u : U) 
    (h2 : Union C u) := h2 x h1.  
(* We may now instantiate the general theorem *)

  Definition Stable (x : set) := Subset x (Phi x).  
  Definition S := Union Stable.  

Lemma Knaster : Equal S (Phi S).
Proof Tarski set Subset Subset_trans Union Union_upperb Union_least Phi Incr.
							 
End Knaster.

(* Timing: 12.19s (was 53.53s) on Vax 780 *)
