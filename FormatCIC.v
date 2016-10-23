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
(*                                 Format.v                                 *)
(****************************************************************************)

    
    (**********************************************************************)
    (* A list of words separated by white characters (space or line feed) *)
    (* is given. The program produces a formated list, that is the same   *)
    (* list of words separated by just one line-feed or space in order to *)
    (* put the maximum number of words on the same line.                  *)
    (**********************************************************************)


Section Format.

(* Environment *)

(****************************************************************************)
(* The non-white characters (letters) are indexed by a type Ind.            *)
(* The white spaces (separators) are                                        *)
(* indexed by the type bool (space = true and linefeed = false)             *)
(* The data structure is a type of lists with two constructors for cons of  *)
(* letters and cons of separators                                           *)
(****************************************************************************)


 Parameter Induct : Set.   
                                        
 Inductive l_ch : Set :=
   | nil : l_ch
   | consbl : bool -> l_ch -> l_ch
   | consltr : Induct -> l_ch -> l_ch.

 Definition l_ch_it (C : Set) (x : C) (f1 : bool -> C -> C)
   (f2 : Induct -> C -> C) : l_ch -> C :=
   fix F (l : l_ch) : C :=
     match l with
     | nil => x
     | consbl b l0 => f1 b (F l0)
     | consltr i l0 => f2 i (F l0)
     end.

 Definition nat_it (C : Set) (x : C) (f : C -> C) : 
   nat -> C :=
   fix F (n : nat) : C := match n with
                          | O => x
                          | S m => f (F m)
                          end.

 Let conssp := consbl true. 
 Let conslf := consbl false. 

(* case definition *)

Section Casebl_section.

 Variable A : Set.                                                    
 Variable c : l_ch.
 Variable xnil : A.
 Variable xbl xltr : A -> A.
 Definition Casebl : A :=
   l_ch_it A xnil (fun b : bool => xbl) (fun i : Induct => xltr) c.

End Casebl_section.

(* Length function *)

 Definition lgth (l : l_ch) : nat := Casebl nat l 0 S S.              

(* Append function *)

 Definition app (l m : l_ch) : l_ch := l_ch_it l_ch m consbl consltr l.   

 Let appsp (l m : l_ch) := app l (conssp m).                        

 Let applf (l m : l_ch) := app l (conslf m).          

(* Maximal allowed length of a line *)

 Parameter max : nat.                                                   

(* Predicate that recognize a word : sequenz (eventually empty) of letters *) 

Inductive word : l_ch -> Prop :=
  | wordnil : word nil
  | wordltr : forall (j : Induct) (l : l_ch), word l -> word (consltr j l).

(* Predicate that recognize a non-empty sequenz of separators *)

Inductive space : l_ch -> Prop :=
  | space_bl : forall b : bool, space (consbl b nil)
  | space_co_bl : forall (b : bool) (l : l_ch), space l -> space (consbl b l).

(* We give an axiomatisation of predicates inf and sup on integers.     *)
(* We will cut  a line according these predicates.                      *)
(* inf n means  n < max and sup n means n >= max                        *)

 Parameter inf sup : nat -> Prop.                                    
 Axiom ax1 : forall n : nat, {inf n} + {sup n}.                       

 Let inflg (m : l_ch) := inf (lgth m).                            

 Let suplg (m : l_ch) := sup (lgth m).                            

 Let plus_l_ch (m : l_ch) (n : nat) : nat := nat_it nat n S (lgth m).

(* The words must be of length less than max. We define a predicate valide. *)
(* A proof of (valide l) gives a decomposition of the list of characters    *)
(* in words of length less than max, separated by spaces                    *)

Inductive valide : l_ch -> Set :=
  | vword : forall m : l_ch, word m -> inflg m -> valide m
  | vapp :
      forall m1 m2 p : l_ch,
      word m1 ->
      inflg m1 -> space m2 -> valide p -> valide (app m1 (app m2 p)).

(* The empty list is valide if 0<max *)

 Hypothesis infmax : inf 0.                                         

(* A list will be non-valid if it contains a too long word *)

Inductive NV : l_ch -> Prop :=
  | NVword : forall l : l_ch, word l -> suplg l -> NV l
  | NVapp1 : forall l m : l_ch, NV l -> NV (app l m)
  | NVapp2 : forall l m : l_ch, NV l -> NV (app m l).

(* We show that every list satisfies valide or NV, this is an informative *)
(* proof (a preprocessing of the text).                                    *)

Inductive val_or_no (l : l_ch) : Set :=
  | inval : valide l -> val_or_no l
  | inNV : NV l -> val_or_no l.

(* To add a space to a valid list is easy *)

Remark valbl : forall (b : bool) (l : l_ch), valide l -> valide (consbl b l).
intros; apply (vapp nil (consbl b nil) l); auto.
apply wordnil.
apply space_bl.
Qed.

(* For adding a letter to a valid list, we need to test whether max *)
(* is overheaded.                                                   *) 

Remark valltr :
 forall (i : Induct) (l : l_ch), valide l -> val_or_no (consltr i l).
intros; elim H; intros.
elim (ax1 (S (lgth m))); intros.
apply (inval (consltr i m)).
apply vword; auto.
apply wordltr; auto.
apply (inNV (consltr i m)).
apply NVword; auto.
apply wordltr; auto.
elim (ax1 (S (lgth m1))); intros.
apply (inval (consltr i (app m1 (app m2 p)))).
apply (vapp (consltr i m1) m2 p); auto.
apply wordltr; auto.
apply (inNV (consltr i (app m1 (app m2 p)))).
apply (NVapp1 (consltr i m1) (app m2 p)).
apply NVword; auto.
apply wordltr; auto.
Qed.

(* The complete proof is by induction on the structure of the list *)

Lemma preproc : forall l : l_ch, val_or_no l.
intro; elim l; intros.
apply (inval nil).
apply vword; auto.
apply wordnil.
elim H; intros.
apply (inval (consbl b l0)).
apply valbl; auto.
apply (inNV (consbl b l0)).
apply (NVapp2 l0 (consbl b nil)); auto.
elim H; intros.
apply valltr; auto.
apply (inNV (consltr i l0)).
apply (NVapp2 l0 (consltr i nil)); auto.
Qed.

(* We define the relation "two lists are equivalent", the intended meaning *)
(* is that they represent the same list of words.                          *)

Section Equivalence.

Inductive Eq : l_ch -> l_ch -> Prop :=
  | Eq_nil : Eq nil nil
  | Eq_bl_nil : forall (b : bool) (l : l_ch), Eq l nil -> Eq (consbl b l) nil
  | Eq_co_bl :
      forall (b c : bool) (l m : l_ch),
      Eq l m -> Eq (consbl b l) (consbl c m)
  | Eq_co_ltr :
      forall (i : Induct) (l m : l_ch),
      Eq l m -> Eq (consltr i l) (consltr i m)
  | Eq_bl_bl :
      forall (b c : bool) (l m : l_ch),
      Eq l (consbl b m) -> Eq (consbl c l) (consbl b m)
  | Eq_tran : forall l m n : l_ch, Eq l m -> Eq m n -> Eq l n.

(* Properties of equivalence *)

(* Reflexivity *)

 Theorem Eq_re : forall l : l_ch, Equivalence.Eq l l.
 intro; elim l; intros.
 apply Eq_nil.
 apply Eq_co_bl; auto.
 apply Eq_co_ltr; auto.
 Qed.

(* Eq stability with respect to append *)

 Theorem Eq_app :
  forall l m n : l_ch,
  Equivalence.Eq m n -> Equivalence.Eq (app l m) (app l n).
 intros; elim l; intros; auto.
 apply (Eq_co_bl b b (app l0 m) (app l0 n)); auto.
 apply (Eq_co_ltr i (app l0 m) (app l0 n)); auto.
 Qed.

(* particular case n=nil, directly proved *)

 Theorem Eq_app_nil :
  forall l m : l_ch, Equivalence.Eq m nil -> Equivalence.Eq (app l m) l.
 intros; elim l; intros; auto.
 apply (Eq_co_bl b b (app l0 m) l0); auto.
 apply (Eq_co_ltr i (app l0 m) l0); auto.
 Qed.

(* Adding more than one separator does not change anything *)
 Theorem Eq_space_bl :
  forall (b : bool) (l m n : l_ch),
  space l ->
  Equivalence.Eq m (consbl b n) -> Equivalence.Eq (app l m) (consbl b n).
 intros.
 elim H; intros.
 apply (Eq_bl_bl b b0 m n); auto.
 apply (Eq_bl_bl b b0 (app l0 m) n); auto.
 Qed.

(* Adding separators at the beginning of the list is equivalent to nil *)
 Theorem Eq_space_nil :
  forall m : l_ch, space m -> Equivalence.Eq (app m nil) nil.
 intros; elim H; intros.
 apply (Eq_bl_nil b nil Eq_nil); auto.
 apply (Eq_bl_nil b (app l nil) H1); auto.
 Qed.

(* Adding separators is equivalent to add a space *)
 Theorem Eq_space :
  forall l m n : l_ch,
  space l -> Equivalence.Eq m n -> Equivalence.Eq (app l m) (conssp n).
 intros; elim H; intros.
 apply (Eq_co_bl b true m n); auto.
 apply (Eq_bl_bl true b (app l0 m) n); auto.
 Qed.

End Equivalence.

(* Definition of the predicate formn : nat->l_ch->Prop. (formn n l) means that
 l is a formated list with n characters on its last line *)

Inductive formn : nat -> l_ch -> Prop :=
  | fword : forall m : l_ch, word m -> inflg m -> formn (lgth m) m
  | fwordinf :
      forall (p : nat) (m1 : l_ch) (b : bool) (m2 : l_ch),
      inf (plus_l_ch m1 p) ->
      word m1 ->
      formn p (consbl b m2) -> formn (plus_l_ch m1 p) (appsp m1 m2)
  | fwordsup :
      forall (p : nat) (m1 : l_ch) (b : bool) (m2 : l_ch),
      sup (plus_l_ch m1 p) ->
      word m1 ->
      inflg m1 -> formn p (consbl b m2) -> formn (lgth m1) (applf m1 m2)
  | fsp :
      forall (p : nat) (i : Induct) (m : l_ch),
      formn p (consltr i m) -> formn (S p) (conssp (consltr i m)).

(* Program's specification for a list l : there exists n : nat and m : list *)
(* such that (formn n m) and (Eq l m)                                       *)

 Inductive SigFormat (l : l_ch) : Set :=
     ExFormat :
       forall (n : nat) (m : l_ch), formn n m -> Format.Eq l m -> SigFormat l.

(* Two lemmas *)

Lemma Lem1 :
 forall (b : bool) (p m1 m2 : l_ch) (n : nat) (h1 : word m1) 
   (h2 : inflg m1) (t1 : formn n (consbl b m2))
   (t2 : Format.Eq p (consbl b m2)), SigFormat (app m1 p).
intros.
elim (ax1 (plus_l_ch m1 n)); intros.
apply (ExFormat (app m1 p) (plus_l_ch m1 n) (appsp m1 m2)).
apply (fwordinf n m1 b m2); auto.
apply (Eq_app m1 p (conssp m2)); auto.
apply (Eq_tran p (consbl b m2) (conssp m2)); auto.
apply (Eq_co_bl b true m2 m2); auto.
apply Eq_re.
apply (ExFormat (app m1 p) (lgth m1) (applf m1 m2)).
apply (fwordsup n m1 b m2); auto.
apply (Eq_app m1 p (conslf m2)); auto.
apply (Eq_tran p (consbl b m2) (conslf m2)); auto.
apply (Eq_co_bl b false m2 m2); auto.
apply Eq_re.
Qed.

Let prop2 (m1 m2 p : l_ch) (n : nat) (u : l_ch) :=
  formn n u -> Format.Eq p u -> SigFormat (app m1 (app m2 p)).             

Lemma Lem2 :
 forall (m1 m2 p : l_ch) (h1 : word m1) (h2 : inflg m1) 
   (h3 : space m2) (n : nat) (p0 : l_ch), prop2 m1 m2 p n p0.
intros.
elim p0; intros.
red in |- *; intros.
apply (ExFormat (app m1 (app m2 p)) (lgth m1) m1).
apply (fword m1); auto.
apply (Eq_app_nil m1 (app m2 p)); auto.
apply (Eq_tran (app m2 p) (app m2 nil) nil); auto.
apply (Eq_app m2 p nil); auto.
apply (Eq_space_nil m2); auto.
red in |- *; intros.
apply (Lem1 b (app m2 p) m1 l n); auto.
apply (Eq_space_bl b m2 p l); auto.
red in |- *; intros.
apply (Lem1 true (app m2 p) m1 (consltr i l) (S n)); auto.
apply (fsp n i l); auto.
apply (Eq_space m2 p (consltr i l)); auto.
Qed.

(* Formatting of a valid list *)

 Theorem format : forall l : l_ch, valide l -> SigFormat l.
 intros.
 elim H; intros.
 apply (ExFormat m (lgth m) m).
 apply (fword m); auto.
 apply Eq_re.
 elim H0; intros.
 apply (Lem2 m1 m2 p w i s n m); auto.
 Qed.

(* Formatting of a list : this function will detect if the list is not valid *)

 Theorem format_all : forall l : l_ch, SigFormat l + {NV l}.
 intro; elim (preproc l); intros.
 left; apply format; auto.
 right; auto.
 Qed.

End Format.


(* $Id$ *)