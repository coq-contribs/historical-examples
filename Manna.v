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


(* This file is a translation to Coq V8.0 syntax of the file Manna.v
   from CoC version 4.4 (even if noted V4.5 in the header).

   At this time, no "Require" mechanism existed to automatize the
   dependency in the file Base.v.

   At this time, the Section mechanism were more Automath-like: a
   Discharge command had the effect of resetting the local section of
   variables to a previous point.

   Previous versions of Manna.v existed in CoC V4.2 with name lambo.ml
   (there were no stand-alone parser before V4.3) and in CoC V4.3 (at this
   time, Base.v was not yet isolated from the file).

   A version of the original development adapted to the Calculus of
   Inductive Constructions and to the standard library of Coq was
   distributed as part of the user contribution LYON/PROGRAMS, in
   directory ALG, until Coq V6.3.

   The summary of the algorithm in French below is taken from the
   version in CoC V4.2. A typical application is the computation of an
   approximant of the square root of some number. The algorithm is
   described in "Zohar Manna, Richard J. Waldinger. The origin of the
   binary-search paradigm. In the Proceedings of IJCAR '85, pages
   222-224".
*)

(****************************************************************************)
(*                                                                          *)
(*                          Constructions in Caml                           *)
(*		                                                            *)
(*                                 V4.5                                     *)
(*                       La fonction Lambo                                  *)
(****************************************************************************)

    (********************************************************************)
    (*                                                                  *)
    (*  Si f:nat->nat  et n:nat alors lambo(f)(n)=inf{m:nat|f(m)>n}     *)
    (*  f est supposee croissante et non bornee,                        *)
    (*  l'algorithme developpe est :                                    *)
    (*        lambo(f)(n) = if f(0) > n then 0                          *)
    (*                                  else limbo(1)+1                 *)
    (*        where rec limbo(p) = if f(p) > n then 0                   *)
    (*                                         else                     *)
    (*                          let inter = limbo(2*p) in               *)
    (*                          if f(inter+p) > n then inter            *)
    (*                                            else inter + p        *)
    (*                                                                  *)
    (********************************************************************)

Require Import Base.

Definition one : nat := S O.

(* Addition et multiplication par 2 *)
Definition add (n m : nat) : nat := n nat S m.

Definition twice (n : nat) : nat := add n n.

(* Induction de contenu nul sur les entiers				*)
Axiom
  nat_ind :
    forall (n : nat) (P : nat -> Prop),
    P O -> (forall m : nat, P m -> P (S m)) -> P n.

(* Operateur de pattern-matching *)
 Definition nat_match (n : nat) (P : nat -> Prop) (h1 : P O)
   (h2 : forall m : nat, P (S m)) : P n :=
   nat_ind n P h1 (fun (m : nat) (ind : P m) => h2 m).

(* Proprietes de l'addition 						*)
Theorem add_nO : forall n : nat, < nat > add n O = n.
Proof
  fun n : nat =>
  nat_ind n (fun u : nat => < nat > add u O = u) (refl_equal nat O)
    (fun u : nat => f_equal nat nat S (add u O) u).

Theorem add_ass :
 forall u v w : nat, < nat > add (add u v) w = add u (add v w).
Proof
  fun u v w : nat =>
  nat_ind u (fun m : nat => < nat > add (add m v) w = add m (add v w))
    (refl_equal nat (add v w))
    (fun m : nat => f_equal nat nat S (add (add m v) w) (add m (add v w))).

(* Induction de contenu positif						*)
Axiom
  nat_rec :
    forall (n : nat) (P : nat -> Spec),
    P O -> (forall m : nat, P m -> P (S m)) -> P n.

(* L'absurde *)

 Theorem abs : forall A : Prop, {} -> A.
 Proof fun (A : Prop) (h : {}) => h A.

(* Relation d'ordre sur les entiers *)

 Variable inf : nat -> nat -> Prop.

 Axiom tran_inf : trans nat inf.
 Axiom infOO : inf O O.
 Axiom infS_inf : forall n m : nat, inf (S n) (S m) -> inf n m.
 Axiom inf_infS : forall n m : nat, inf n m -> inf (S n) (S m).
 Axiom infS : forall n : nat, inf n (S n).
 Axiom absO : inf one O -> {}.

 Definition sup (n m : nat) : Prop := inf (S m) n.

(* Proprietes de cette relation *)

 Lemma re_inf : forall n : nat, inf n n.
 Proof
   fun n : nat =>
   nat_ind n (fun u : nat => inf u u) infOO
     (fun (u : nat) (h : inf u u) => inf_infS u u h).
      
 Lemma infO : forall n : nat, inf O n.
 Proof
   fun n : nat =>
   nat_ind n (inf O) infOO
     (fun (u : nat) (h : inf O u) => tran_inf O u (S u) h (infS u)).


 Lemma infS_O : forall n : nat, inf (S n) O -> {}.
 Proof
   fun n : nat =>
   nat_ind n (fun u : nat => inf (S u) O -> {}) absO
     (fun (u : nat) (h : inf (S u) O -> {}) (t : inf (S (S u)) O) =>
      h (tran_inf (S u) (S (S u)) O (infS (S u)) t)).


 Lemma infSn_n : forall n : nat, inf (S n) n -> {}.
 Proof
   fun n : nat =>
   nat_ind n (fun u : nat => inf (S u) u -> {}) absO
     (fun (u : nat) (h : inf (S u) u -> {}) (t : inf (S (S u)) (S u)) =>
      h (infS_inf (S u) u t)).

 Lemma inf_sup_abs : forall n m : nat, inf n m -> sup n m -> {}.
 Proof
   fun (n m : nat) (h1 : inf n m) (h2 : sup n m) =>
   infSn_n n (tran_inf (S n) (S m) n (inf_infS n m h1) h2).

(* On aura besoin d'un lemme disant que (sup n m)->(sup (twice n) (S m)) *)

 Lemma inf_add : forall n m : nat, inf m (add n m).
 Proof
   fun n m : nat =>
   nat_ind n (fun u : nat => inf m (add u m)) (re_inf m)
     (fun (u : nat) (h : inf m (add u m)) =>
      tran_inf m (add u m) (add (S u) m) h (infS (add u m))).

 Lemma sup_twice : forall n m : nat, sup n m -> sup (twice n) (S m).
 Proof
   fun n m : nat =>
   nat_match n (fun u : nat => sup u m -> sup (twice u) (S m))
     (fun h : sup O m => abs (sup (twice O) (S m)) (infS_O m h))
     (fun (u : nat) (h : sup (S u) m) =>
      inf_infS (S m) (add u (S u))
        (tran_inf (S m) (S u) (add u (S u)) h (inf_add u (S u)))).


Axiom except : forall A : Spec, {} -> A.

(* Programme Lambo *)

(* Hypotheses *)
Variable f : nat -> nat.

(* f est non bornee							*)
Axiom Unbound : forall n : nat, < nat > Sig  (fun y : nat => sup (f y) n).

(* f est croissante							*)
Axiom Increas : forall n m : nat, inf n m -> inf (f n) (f m).

(* inf ou sup de contenu positif et de contenu nul			*)

Axiom inf_sup : forall x y : nat, {inf x y} + {sup x y}.
Axiom inf_sup0 : forall x y : nat, (inf x y) \/ (sup x y).

Variable n : nat.

 Definition Inf (m : nat) : Prop := inf (f m) n.
 Definition Sup (m : nat) : Prop := sup (f m) n.

(* On utilisera seulement les proprietes suivantes de Inf et Sup : *)

 Definition bound : < nat > Sig  (fun y : nat => sup (f y) n) := Unbound n.

 Definition Inf_Sup (u : nat) : {Inf u} + {Sup u} := inf_sup (f u) n.

 Definition Inf_Sup_abs (u : nat) : Inf u -> Sup u -> {} := inf_sup_abs (f u) n.

(* La maniere dont on utilise l'hypothese f est croissante *)

 Lemma infInf : forall u v : nat, inf u v -> Inf v -> Inf u.
 Proof
   fun (u v : nat) (h1 : inf u v) (h2 : Inf v) =>
   tran_inf (f u) (f v) n (Increas u v h1) h2.

(* Specifications *)
 Definition Small (m : nat) : Prop := forall i : nat, inf (S i) m -> Inf i.

 Lemma SmallO : Small O.
 Proof fun (i : nat) (h : inf (S i) O) => abs (Inf i) (infS_O i h).

 Definition Lambo : Spec := Sig2 nat Sup Small.

 Lemma Lem1 : forall m : nat, Inf m -> Small (S m).
 Proof
   fun (m : nat) (h : Inf m) (i : nat) (q : inf (S i) (S m)) =>
   infInf i m (infS_inf i m q) h.

 Definition Lambo1 : Spec := Sig2 nat Inf (fun m : nat => Sup (S m)) + {Sup O}.

 Lemma Reduct1 : Lambo1 -> Lambo.
 Proof
   fun h : Lambo1 =>
   h Lambo
     (fun h1 : Sig2 nat Inf (fun m : nat => Sup (S m)) =>
      h1 Lambo
        (fun (m : nat) (f1 : Inf m) (f2 : Sup (S m)) =>
         exist2 nat Sup Small (S m) f2 (Lem1 m f1)))
     (fun h2 : Sup O => exist2 nat Sup Small O h2 SmallO).

 Definition Limbo (i : nat) : Spec :=
   sup i O -> Sig2 nat Inf (fun m : nat => Sup (add i m)) + {Sup O}.

(* (add one m)=(S m) par Beta reduction *)

 Lemma Reduct2 : Limbo one -> Lambo1.
 Proof fun h : Limbo one => h (re_inf one).

(* Le probleme de terminaison *)

(* Une relation parametree						*)
 Definition bd (y u v : nat) : Prop := (sup u v) /\ (inf v y).

(* Propriete d'etre bien formee						*)
 Definition wf_bd (y i : nat) : Spec :=
   forall P : nat -> Spec,
   (forall v : nat, (forall u : nat, bd y u v -> P u) -> P v) -> P i.

(* Quelques proprietes de bd : *)

 Lemma Lem2 : forall y1 y2 u v : nat, bd y1 u v -> inf v y2 -> bd y2 u v.
 Proof
   fun (y1 y2 u v : nat) (h1 : bd y1 u v) (h2 : inf v y2) =>
   < sup u v, inf v y2 > (< sup u v, inf v y1 > Fst  (h1), h2).

 Lemma Lem3 : forall y u v w : nat, bd y u v -> bd y v w -> sup y w.
 Proof
   fun (y u v w : nat) (h1 : bd y u v) (h2 : bd y v w) =>
   tran_inf (S w) v y (< sup v w, inf w y > Fst  (h2))
     (< sup u v, inf v y > Snd  (h1)).

 Lemma Term : forall i y : nat, sup i y -> wf_bd y i.
 Proof
   fun (i y : nat) (h : sup i y) (P : nat -> Spec)
     (q : forall v : nat, (forall u : nat, bd y u v -> P u) -> P v) =>
   q i
     (fun (u : nat) (g : bd y u i) =>
      except (P u) (inf_sup_abs i y (< sup u i, inf i y > Snd  (g)) h)).

(* Preuve de (wf_bd y) par induction sur y *)

 Lemma cas_base : forall i : nat, sup i O -> wf_bd O i.
 Proof
   fun (i : nat) (h : sup i O) (P : nat -> Spec)
     (q : forall v : nat, (forall u : nat, bd O u v -> P u) -> P v) =>
   q i
     (fun (u : nat) (g : bd O u i) =>
      except (P u) (inf_sup_abs i O (< sup u i, inf i O > Snd  (g)) h)).

 Lemma cas_ind : forall i y : nat, wf_bd y i -> wf_bd (S y) i.
 Proof
   fun (i y : nat) (ind : wf_bd y i) (P : nat -> Spec)
     (q : forall v : nat, (forall u : nat, bd (S y) u v -> P u) -> P v) =>
   ind P
     (fun (v : nat) (g : forall u : nat, bd y u v -> P u) =>
      q v
        (fun (u : nat) (h : bd (S y) u v) =>
         inf_sup v y (P u) (fun t1 : inf v y => g u (Lem2 (S y) y u v h t1))
           (fun t2 : sup v y =>
            q u
              (fun (w : nat) (l : bd (S y) w u) =>
               except (P w)
                 (infSn_n v
                    (tran_inf (S v) (S y) v (Lem3 (S y) w u v l h) t2)))))).

Theorem Wf : forall y i : nat, sup i O -> wf_bd y i.
 Proof
   fun (y i : nat) (h : sup i O) =>
   nat_rec y (fun u : nat => wf_bd u i) (cas_base i h) (cas_ind i).

(* En fait on utilise quelque chose de plus simple *)

(* Un scheme d'induction ad-hoc *)
Definition Ind (y i : nat) (P : nat -> Spec) : Spec :=
  (forall k : nat, (inf k y -> P (twice k)) -> P k) -> P i.

Theorem wf_Ind :
 forall y i : nat, sup i O -> forall P : nat -> Spec, Ind y i P.
 Proof
   fun (y i : nat) (h : sup i O) (P : nat -> Spec) =>
   nat_rec y (fun u : nat => Ind u i P)
     (fun q : forall k : nat, (inf k O -> P (twice k)) -> P k =>
      q i (fun r : inf i O => except (P (twice i)) (inf_sup_abs i O r h)))
     (fun (u : nat) (ind : Ind u i P)
        (q : forall k : nat, (inf k (S u) -> P (twice k)) -> P k) =>
      ind
        (fun (k : nat) (r : inf k u -> P (twice k)) =>
         q k
           (fun t : inf k (S u) =>
            inf_sup k u (P (twice k)) r
              (fun v : sup k u =>
               q (twice k)
                 (fun s : inf (twice k) (S u) =>
                  except (P (twice (twice k)))
                    (inf_sup_abs (twice k) (S u) s (sup_twice k u v))))))).

(* Preuve de Limbo *)

 Lemma Lem4 : forall u v : nat, Sup u -> Inf v -> inf v u.
  Proof
    fun (u v : nat) (h1 : Sup u) (h2 : Inf v) =>
    inf_sup0 v u (inf v u) (fun t1 : inf v u => t1)
      (fun t2 : sup v u =>
       abs (inf v u)
         (Inf_Sup_abs u (infInf u v (tran_inf u (S u) v (infS u) t2) h2) h1)).

 Definition LimboSig (i : nat) : Spec := Sig2 nat Inf (fun m : nat => Sup (add i m)).

 Lemma LimboLem : forall i : nat, sup i O -> Inf O -> LimboSig i.
 Proof
   fun (i : nat) (h1 : sup i O) (h2 : Inf O) =>
   bound (LimboSig i)
     (fun (y : nat) (hy : Sup y) =>
      wf_Ind y i h1 LimboSig
        (fun (k : nat) (hk : inf k y -> LimboSig (twice k)) =>
         Inf_Sup (add k O) (LimboSig k)
           (fun t1 : Inf (add k O) =>
            hk (Lem4 y k hy (add_nO k Inf t1)) (LimboSig k)
              (fun (m : nat) (u1 : Inf m) (u2 : Sup (add (twice k) m)) =>
               Inf_Sup (add k m) (LimboSig k)
                 (fun s1 : Inf (add k m) =>
                  exist2 nat Inf (fun p : nat => Sup (add k p)) 
                    (add k m) s1 (add_ass k k m Sup u2))
                 (fun s2 : Sup (add k m) =>
                  exist2 nat Inf (fun p : nat => Sup (add k p)) m u1 s2)))
           (fun t2 : Sup (add k O) =>
            exist2 nat Inf (fun p : nat => Sup (add k p)) O h2 t2))).

 Lemma Prog : forall i : nat, Limbo i.
 Proof
   fun (i : nat) (h : sup i O) =>
   Inf_Sup O (LimboSig i + {Sup O})
     (fun t1 : Inf O => inleft (LimboSig i) (Sup O) (LimboLem i h t1))
     (fun t2 : Sup O => inright (LimboSig i) (Sup O) t2).

(* Programme final *)
Theorem LamboProg : Lambo.
Proof Reduct1 (Reduct2 (Prog one)).
