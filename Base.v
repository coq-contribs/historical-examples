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


(* This a reconstruction in Coq V8.0 syntax of (a subset of) the file
   Base.v from CoC V4.4

   In CoC V4.4, there were a command "Inductive I : t := c1:t1 | ... | cn:tn." 
   to macro-generate second-order inductive definition.

   At this time, the Section mechanism were more Automath-like: a
   Discharge command had the effect of resetting the local section of
   variables to a previous point. At this time, syntax extensions
   were not incrementally declarable but hard-wired in the yacc parser.

   To avoid the command Inductive be interpreted as the construction
   of a primitive inductive type in the Calculus of Inductive
   Constructions, the effect of the command has been macro-expanded as
   it was the case in CoC V4.3. At this time, the file Base.v did not
   exist and its contents were in the files Manna.v and Format.v.
*)

(* Data and Spec were aliases for Prop/Set (meaningful for extraction) *)

Notation Data := Set.
Notation Spec := Data.

Definition nat := forall A : Spec, (A -> A) -> A -> A.

Definition O : nat := fun (A : Spec) (s : A -> A) (x : A) => x.
Definition S (n : nat) : nat :=
  fun (A : Spec) (s : A -> A) (z : A) => s (n A s z).

Definition one : nat := S O.

Definition void := forall C : Prop, C.
Notation "{}" := void.

Definition and (A B : Prop) := forall C : Prop, (A -> B -> C) -> C.

Notation "A /\ B" := (and A B) : type_scope.

Section conj.

Variable A B : Prop.

Definition conj (x : A) (y : B) : A /\ B :=
  fun (C : Prop) (z : A -> B -> C) => z x y.

End conj.

Notation "< A , B > ( a , b )" := (conj A B a b) (at level 20, A, B at level 20).

Section and_projections.

Variable A B : Prop.
Variable x : A /\ B.

    Theorem proj1 : A.
    Proof x A (fun (y : A) (z : B) => y). 
    
    Theorem proj2 : B.
    Proof x B (fun (y : A) (z : B) => z). 

End and_projections.

Notation "< A , B > 'Fst' ( x )" := (proj1 A B x) (at level 20, A, B at level 20).
Notation "< A , B > 'Snd' ( x )" := (proj2 A B x) (at level 20, A, B at level 20).

Definition prod (A B : Spec) := forall C : Spec, (A -> B -> C) -> C.

Notation "A & B" := (prod A B) (at level 50).

Section prod.

Variable A B : Spec.

Definition pair (x : A) (y : B) : A & B :=
  fun (C : Spec) (z : A -> B -> C) => z x y.

End prod.

Section projections.

Variable A B : Spec.
Variable x : A & B.

    Theorem fst : A.
    Proof x A (fun (y : A) (z : B) => y). 
    
    Theorem snd : B.
    Proof x B (fun (y : A) (z : B) => z). 

End projections.

Definition sumor (A : Spec) (B : Prop) :=
  forall C : Spec, (A -> C) -> (B -> C) -> C.
Notation "A + { B }" := (sumor A B) : type_scope.

Section sumor.

Variable A : Spec.
Variable B : Prop.

Definition inleft (x : A) : A+{B} :=
  fun (C : Spec) (y : A -> C) (z : B -> C) => y x.
Definition inright (x : B) : A+{B} :=
  fun (C : Spec) (y : A -> C) (z : B -> C) => z x.

End sumor.

Definition sumbool (A B : Prop) := forall C : Spec, (A -> C) -> (B -> C) -> C.
Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Definition or (A B : Prop) := forall C : Prop, (A -> C) -> (B -> C) -> C.
Notation "A \/ B" := (or A B) : type_scope.

Section or.

Variable A : Prop.
Variable B : Prop.

Definition or_introl (x : A) : or A B :=
  fun (C : Prop) (y : A -> C) (z : B -> C) => y x.
Definition or_intror (x : B) : or A B :=
  fun (C : Prop) (y : A -> C) (z : B -> C) => z x.

End or.

Definition Sig (A : Spec) (P : A -> Prop) :=
  forall C : Spec, (forall x : A, P x -> C) -> C.
Notation "< A > 'Sig' ( P )" := (Sig A P) (at level 20, A at level 20).

Section sig.

Variable A : Spec.
Variable P : A -> Prop.
Definition exist (x : A) (p : P x) : Sig A P :=
  fun (B : Spec) (f : forall a : A, P a -> B) => f x p.

End sig.


(* Connecteur existentiel double *)

Definition Sig2 (A : Spec) (P Q : A -> Prop) :=
  forall B : Spec, (forall x : A, P x -> Q x -> B) -> B.

Section sig2.

Variable A : Spec.
Variable P Q : A -> Prop.
Definition exist2 (x : A) (p : P x) (q : Q x) : Sig2 A P Q :=
  fun (B : Spec) (f : forall a : A, P a -> Q a -> B) => f x p q.

End sig2.

(* Egalite *)
Definition eq (A : Spec) (x y : A) := forall P : A -> Prop, P x -> P y.
Notation "< A > x = y " := (eq A x y) (at level 20, A, x, y at level 20).

Section refl_equal.

 Variable A : Spec.
 Variable x : A.
 
  Theorem refl_equal : < A > x = x.
  Proof fun (P : A -> Prop) (h : P x) => h.
 
End refl_equal.

Section f_equal.

 Variable A B : Spec.
 Variable f : A -> B.
 Variable x y : A.

Theorem f_equal : < A > x = y -> < B > f x = f y.
 Proof
   fun h : < A > x = y =>
   h (fun u : A => < B > f x = f u) (refl_equal B (f x)).

End f_equal.

(* Propriete de transitivite *)
Definition trans (A : Spec) (R : A -> A -> Prop) :=
  forall x y z : A, R x y -> R y z -> R x z.
