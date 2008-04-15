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


(* This file is a translation to Coq V8.0 syntax of the file Format.v
   from CoC version 4.4.

   At this time, no "Require" mechanism existed to automatize the
   dependency in the file Base.v.

   At this time, the Section mechanism were more Automath-like: a
   Discharge command had the effect of resetting the local section of
   variables to a previous point.

   Previous versions of Format.v existed in CoC V4.2 with name
   formal.ml (there were no stand-alone parser before V4.3) and in CoC
   V4.3 (at this time, the subset of Base.v used by Format.v was not
   yet isolated from the file).

   To avoid the command Inductive be interpreted as the construction
   of a primitive inductive type in the Calculus of Inductive
   Constructions, the effect of the command has been macro-expanded as
   it was the case in CoC V4.3.

   A version of the original development adapted to the Calculus of
   Inductive Constructions and to the standard library of Coq was
   distributed as part of the user contribution LYON/PROGRAMS, in
   directory ALG, until Coq V6.3.
*)

(****************************************************************************)
(*                                                                          *)
(*                          Constructions in Caml                           *)
(*                                                                          *)
(*                           Programme de mise en page                      *)
(*                             Christine Paulin                             *)
(*             CAML V2.5    Constructions V4.4     Vernacular V1.1          *)
(****************************************************************************)

    (********************************************************************)
    (* Une liste de mots separes par des blancs (espace sp ou retour a  *)
    (* la ligne lf) est donnee, on veut en faire une liste formatee     *)
    (* ie la meme liste de mots separes par juste un espace ou un lf de *)
    (* maniere a mettre le maximum de mots par ligne sans depasser un   *)
    (* nombre max de caracteres.                                        *)
    (********************************************************************)

Require Import Base.

(* Le programme : *)
(* Environnement *)

(* La structure de donnees : Ce sont des listes de caracteres, c'est a dire *)
(* essentiellement une structure dont on sait tester si le premier element  *)
(* est un blanc (ie un linefeed ou un space) ou une lettre,                 *)
(* les lettres sont indicees par un ensemble donne Ind, les blancs par bool *)

 Variable Ind : Spec.                                           
 Definition l_ch :=
   forall A : Spec, A -> (bool -> A -> A) -> (Ind -> A -> A) -> A.

 Definition nil : l_ch :=
   fun (A : Spec) (x0 : A) (x1 : bool -> A -> A) (x2 : Ind -> A -> A) => x0.
 Definition consbl (b : bool) (l : l_ch) : l_ch :=
   fun (A : Spec) (x0 : A) (x1 : bool -> A -> A) (x2 : Ind -> A -> A) =>
   x1 b (l A x0 x1 x2).
 Definition consltr (i : Ind) (l : l_ch) : l_ch :=
   fun (A : Spec) (x0 : A) (x1 : bool -> A -> A) (x2 : Ind -> A -> A) =>
   x2 i (l A x0 x1 x2).

 Definition conssp := consbl true. 
 Definition conslf := consbl false. 

(* Predicat d'induction sur ce type de donnee : *)

 Hypothesis
   LCH_Ind :
     forall (x : l_ch) (P : l_ch -> Prop),
     P nil ->
     (forall (b : bool) (l : l_ch), P l -> P (consbl b l)) ->
     (forall (i : Ind) (l : l_ch), P l -> P (consltr i l)) -> P x.                                                    

 Hypothesis
   LCH_rec :
     forall (x : l_ch) (P : l_ch -> Spec),
     P nil ->
     (forall (b : bool) (l : l_ch), P l -> P (consbl b l)) ->
     (forall (i : Ind) (l : l_ch), P l -> P (consltr i l)) -> P x.                                                    

(* Definition par cas sans distinguer les lettres ni le lf du sp *)

Section Casebl.

 Variable A : Spec.                                                    
 Definition Casebl (c : l_ch) (xnil : A) (xbl xltr : A -> A) : A :=
   c A xnil (fun b : bool => xbl) (fun i : Ind => xltr).                            

End Casebl.

(* Fonction longueur d'une liste *)

 Definition lgth (l : l_ch) : nat := Casebl nat l O S S.              

(* Fonction Append d'une liste a une autre *)

 Definition app (l m : l_ch) : l_ch := l l_ch m consbl consltr.   

 Definition appsp (l m : l_ch) := app l (conssp m).                        

 Definition applf (l m : l_ch) := app l (conslf m).          

(* Longueur maximale des lignes *)

 Variable max : nat.                                                   

(* Predicat qui reconnait un mot (suite eventuellement vide de lettres) *)

 Definition word (l : l_ch) : Prop :=
   forall P : l_ch -> Prop,
   P nil -> (forall (i : Ind) (m : l_ch), P m -> P (consltr i m)) -> P l.

 Definition wordnil : word nil :=
   fun (P : l_ch -> Prop) (h1 : P nil)
     (h2 : forall (i : Ind) (m : l_ch), P m -> P (consltr i m)) => h1.

 Definition wordltr (j : Ind) (l : l_ch) (h : word l) : 
   word (consltr j l) :=
   fun (P : l_ch -> Prop) (h1 : P nil)
     (h2 : forall (i : Ind) (m : l_ch), P m -> P (consltr i m)) =>
   h2 j l (h P h1 h2).

(* Predicat qui reconnait une suite non vide de lf et sp *)
 Definition space (l : l_ch) : Prop :=
   forall P : l_ch -> Prop,
   (forall b : bool, P (consbl b nil)) ->
   (forall (b : bool) (m : l_ch), P m -> P (consbl b m)) -> P l.

 Definition space_bl : forall b : bool, space (consbl b nil) :=
   fun (c : bool) (P : l_ch -> Prop) (h1 : forall b : bool, P (consbl b nil))
     (h2 : forall (b : bool) (m : l_ch), P m -> P (consbl b m)) => 
   h1 c.

 Definition space_co_bl :
   forall (b : bool) (l : l_ch), space l -> space (consbl b l) :=
   fun (c : bool) (l : l_ch) (h : space l) (P : l_ch -> Prop)
     (h1 : forall b : bool, P (consbl b nil))
     (h2 : forall (b : bool) (m : l_ch), P m -> P (consbl b m)) =>
   h2 c l (h P h1 h2).

(* On axiomatise les relations inf et sup qui nous permettent de decider  *)
(* quand il faut couper une ligne *)

(* inf n est mis pour n < max et sup n pour n >:= max *)

 Variable inf sup : nat -> Prop.                                    
 Hypothesis ax1 : forall n : nat, {inf n} + {sup n}.                       

 Definition inflg (m : l_ch) := inf (lgth m).                            

 Definition suplg (m : l_ch) := sup (lgth m).                            

 Definition plus (m : l_ch) (n : nat) : nat := lgth m nat S n. 

(* Les mots des listes que l'on utilise doivent toujours etre de longueur  *)
(* inferieure strictement au max: on definit un predicat valide :          *)
(* Se donner une preuve de valide l c'est se donner une decomposition de   *)
(* la liste de caracteres en mots separes par des espaces. On a de plus a  *)
(* chaque fois une preuve que le mot est de longueur inferieure a max      *)

 Definition valide (l : l_ch) :=
   forall P : l_ch -> Spec,
   (forall m : l_ch, word m -> inflg m -> P m) ->
   (forall m1 m2 p : l_ch,
    word m1 -> inflg m1 -> space m2 -> P p -> P (app m1 (app m2 p))) -> 
   P l.

(* Les deux constructeurs de listes valides : *)

 Definition vword : forall m : l_ch, word m -> inflg m -> valide m :=
   fun (x : l_ch) (h1 : word x) (h2 : inflg x) (P : l_ch -> Spec)
     (t1 : forall m : l_ch, word m -> inflg m -> P m)
     (t2 : forall m1 m2 p : l_ch,
           word m1 -> inflg m1 -> space m2 -> P p -> P (app m1 (app m2 p))) =>
   t1 x h1 h2.

 Definition vapp :
   forall m1 m2 p : l_ch,
   word m1 -> inflg m1 -> space m2 -> valide p -> valide (app m1 (app m2 p)) :=
   fun (x1 x2 m : l_ch) (h1 : word x1) (h2 : inflg x1) 
     (h3 : space x2) (h : valide m) (P : l_ch -> Spec)
     (t1 : forall l : l_ch, word l -> inflg l -> P l)
     (t2 : forall m1 m2 p : l_ch,
           word m1 -> inflg m1 -> space m2 -> P p -> P (app m1 (app m2 p))) =>
   t2 x1 x2 m h1 h2 h3 (h P t1 t2).

(* (valide l) correspond a un preprocessing du texte *)

(* Pour en particulier que la liste vide soit valide il faut que O<max  *)
(* On se place dans ce cas *)

 Hypothesis infmax : inf O.                                         

(* On definit un predicat pour les listes non valides. Cela revient a   *)
(* trouver un mot "trop long" a l'interieur de la liste.                *)

 Definition NV (x : l_ch) :=
   forall P : l_ch -> Prop,
   (forall l : l_ch, word l -> suplg l -> P l) ->
   (forall l m : l_ch, P l -> P (app l m)) ->
   (forall l m : l_ch, P l -> P (app m l)) -> P x.

(* Les trois constructeurs de listes non valides : *)

 Definition NVword : forall l : l_ch, word l -> suplg l -> NV l :=
   fun (x : l_ch) (h1 : word x) (h2 : suplg x) (P : l_ch -> Prop)
     (t1 : forall l : l_ch, word l -> suplg l -> P l)
     (t2 : forall l m : l_ch, P l -> P (app l m))
     (t3 : forall l m : l_ch, P l -> P (app m l)) => 
   t1 x h1 h2.

 Definition NVapp1 : forall l m : l_ch, NV l -> NV (app l m) :=
   fun (x y : l_ch) (h : NV x) (P : l_ch -> Prop)
     (t1 : forall l : l_ch, word l -> suplg l -> P l)
     (t2 : forall l m : l_ch, P l -> P (app l m))
     (t3 : forall l m : l_ch, P l -> P (app m l)) => 
   t2 x y (h P t1 t2 t3).

 Definition NVapp2 : forall l m : l_ch, NV l -> NV (app m l) :=
   fun (x y : l_ch) (h : NV x) (P : l_ch -> Prop)
     (t1 : forall l : l_ch, word l -> suplg l -> P l)
     (t2 : forall l m : l_ch, P l -> P (app l m))
     (t3 : forall l m : l_ch, P l -> P (app m l)) => 
   t3 x y (h P t1 t2 t3).

(* On va donc pour toute liste montrer qu'elle est soit valide soit non *)
(* valide : *)

 Definition val_or_no (l : l_ch) := valide l + {NV l}.
 Definition inval (l : l_ch) := inleft (valide l) (NV l).
 Definition inNV (l : l_ch) := inright (valide l) (NV l).

(* Ajouter un espace a une liste valide ne pose pas de problemes *)

 Definition valbl (b : bool) (l : l_ch) (h : valide l) : valide (consbl b l) :=
   vapp nil (consbl b nil) l wordnil infmax (space_bl b) h.      

(* Ajouter une lettre demande de tester si on ne depasse pas max :       *)
(* On a besoin de valide p dans l'hypothese d'induction on fait donc une *)
(* preuve double. *)

Section Valltr.

Variable i : Ind.
Variable l : l_ch.

 Definition Valltr := valide l & val_or_no (consltr i l).              
 Definition Vfst := fst (valide l) (val_or_no (consltr i l)).  
 Definition Vsnd := snd (valide l) (val_or_no (consltr i l)).           
 Definition Vand := pair (valide l) (val_or_no (consltr i l)).           

End Valltr.

 Lemma valltr :
  forall (i : Ind) (l : l_ch), valide l -> val_or_no (consltr i l).
 Proof
   fun (i : Ind) (l : l_ch) (h : valide l) =>
   Vsnd i l
     (h (Valltr i)
        (fun (m : l_ch) (t1 : word m) (t2 : inflg m) =>
         Vand i m (vword m t1 t2)
           (ax1 (S (lgth m)) (val_or_no (consltr i m))
              (fun h1 : inflg (consltr i m) =>
               inval (consltr i m) (vword (consltr i m) (wordltr i m t1) h1))
              (fun h2 : suplg (consltr i m) =>
               inNV (consltr i m) (NVword (consltr i m) (wordltr i m t1) h2))))
        (fun (m1 m2 p : l_ch) (t1 : word m1) (t2 : inflg m1) 
           (t3 : space m2) (f : Valltr i p) =>
         Vand i (app m1 (app m2 p)) (vapp m1 m2 p t1 t2 t3 (Vfst i p f))
           (ax1 (S (lgth m1)) (val_or_no (consltr i (app m1 (app m2 p))))
              (fun h11 : inflg (consltr i m1) =>
               inval (consltr i (app m1 (app m2 p)))
                 (vapp (consltr i m1) m2 p (wordltr i m1 t1) h11 t3
                    (Vfst i p f)))
              (fun h12 : suplg (consltr i m1) =>
               inNV (consltr i (app m1 (app m2 p)))
                 (NVapp1 (consltr i m1) (app m2 p)
                    (NVword (consltr i m1) (wordltr i m1 t1) h12)))))).
      

(* La preuve generale est une induction sur la structure de la liste, le  *)
(* cas non-valide se repercute, le cas valide a ete traite dans valbl et  *)
(* valltr *)

 Definition preproc (l : l_ch) : valide l + {NV l} :=
   LCH_rec l val_or_no (inval nil (vword nil wordnil infmax))
     (fun (b : bool) (m : l_ch) (h : val_or_no m) =>
      h (val_or_no (consbl b m))
        (fun h1 : valide m => inval (consbl b m) (valbl b m h1))
        (fun h2 : NV m => inNV (consbl b m) (NVapp2 m (consbl b nil) h2)))
     (fun (i : Ind) (m : l_ch) (h : val_or_no m) =>
      h (val_or_no (consltr i m)) (valltr i m)
        (fun t : NV m => inNV (consltr i m) (NVapp2 m (consltr i nil) t))).

(* On va donc maintenant definir les predicats "l est formatee" et "l et m
   sont equivalentes" puis prouver All l Ex m (format m)&(equiv l m) *)

(* De'finition de l'equivalence de deux listes de caracteres : c'est  *)
(* un predicat donne par ces proprietes de stabilite. *)

 Definition Eq (x y : l_ch) :=
   forall R : l_ch -> l_ch -> Prop,
   R nil nil ->
   (forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil) ->
   (forall (b c : bool) (l m : l_ch), R l m -> R (consbl b l) (consbl c m)) ->
   (forall (i : Ind) (l m : l_ch), R l m -> R (consltr i l) (consltr i m)) ->
   (forall (b c : bool) (l m : l_ch),
    R l (consbl b m) -> R (consbl c l) (consbl b m)) ->
   (forall l m n : l_ch, R l m -> R m n -> R l n) -> R x y.

 Definition Eq_nil : Eq nil nil :=
   fun (R : l_ch -> l_ch -> Prop) (h0 : R nil nil)
     (h1 : forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil)
     (h2 : forall (b c : bool) (l m : l_ch),
           R l m -> R (consbl b l) (consbl c m))
     (h3 : forall (i : Ind) (l m : l_ch),
           R l m -> R (consltr i l) (consltr i m))
     (h4 : forall (b c : bool) (l m : l_ch),
           R l (consbl b m) -> R (consbl c l) (consbl b m))
     (h5 : forall l m n : l_ch, R l m -> R m n -> R l n) => h0.

 Definition Eq_bl_nil :
   forall (b : bool) (l : l_ch),
   Eq l nil -> Eq (consbl b l) nil :=
   fun (d : bool) (x : l_ch) (h : Eq x nil) 
     (R : l_ch -> l_ch -> Prop) (h0 : R nil nil)
     (h1 : forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil)
     (h2 : forall (b c : bool) (l m : l_ch),
           R l m -> R (consbl b l) (consbl c m))
     (h3 : forall (i : Ind) (l m : l_ch),
           R l m -> R (consltr i l) (consltr i m))
     (h4 : forall (b c : bool) (l m : l_ch),
           R l (consbl b m) -> R (consbl c l) (consbl b m))
     (h5 : forall l m n : l_ch, R l m -> R m n -> R l n) =>
   h1 d x (h R h0 h1 h2 h3 h4 h5).

 Definition Eq_co_bl :
   forall (b c : bool) (l m : l_ch),
   Eq l m -> Eq (consbl b l) (consbl c m) :=
   fun (d e : bool) (x y : l_ch) (h : Eq x y)
     (R : l_ch -> l_ch -> Prop) (h0 : R nil nil)
     (h1 : forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil)
     (h2 : forall (b c : bool) (l m : l_ch),
           R l m -> R (consbl b l) (consbl c m))
     (h3 : forall (i : Ind) (l m : l_ch),
           R l m -> R (consltr i l) (consltr i m))
     (h4 : forall (b c : bool) (l m : l_ch),
           R l (consbl b m) -> R (consbl c l) (consbl b m))
     (h5 : forall l m n : l_ch, R l m -> R m n -> R l n) =>
   h2 d e x y (h R h0 h1 h2 h3 h4 h5).

 Definition Eq_co_ltr :
   forall (i : Ind) (l m : l_ch),
   Eq l m -> Eq (consltr i l) (consltr i m) :=
   fun (j : Ind) (x y : l_ch) (h : Eq x y) (R : l_ch -> l_ch -> Prop)
     (h0 : R nil nil)
     (h1 : forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil)
     (h2 : forall (b c : bool) (l m : l_ch),
           R l m -> R (consbl b l) (consbl c m))
     (h3 : forall (i : Ind) (l m : l_ch),
           R l m -> R (consltr i l) (consltr i m))
     (h4 : forall (b c : bool) (l m : l_ch),
           R l (consbl b m) -> R (consbl c l) (consbl b m))
     (h5 : forall l m n : l_ch, R l m -> R m n -> R l n) =>
   h3 j x y (h R h0 h1 h2 h3 h4 h5).

 Definition Eq_bl_bl :
   forall (b c : bool) (l m : l_ch),
   Eq l (consbl b m) -> Eq (consbl c l) (consbl b m) :=
   fun (d e : bool) (x y : l_ch) (h : Eq x (consbl d y))
     (R : l_ch -> l_ch -> Prop) (h0 : R nil nil)
     (h1 : forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil)
     (h2 : forall (b c : bool) (l m : l_ch),
           R l m -> R (consbl b l) (consbl c m))
     (h3 : forall (i : Ind) (l m : l_ch),
           R l m -> R (consltr i l) (consltr i m))
     (h4 : forall (b c : bool) (l m : l_ch),
           R l (consbl b m) -> R (consbl c l) (consbl b m))
     (h5 : forall l m n : l_ch, R l m -> R m n -> R l n) =>
   h4 d e x y (h R h0 h1 h2 h3 h4 h5).

 Definition Eq_tran :
   forall l m n : l_ch, Eq l m -> Eq m n -> Eq l n :=
   fun (x y z : l_ch) (t1 : Eq x y) (t2 : Eq y z)
     (R : l_ch -> l_ch -> Prop) (h0 : R nil nil)
     (h1 : forall (b : bool) (l : l_ch), R l nil -> R (consbl b l) nil)
     (h2 : forall (b c : bool) (l m : l_ch),
           R l m -> R (consbl b l) (consbl c m))
     (h3 : forall (i : Ind) (l m : l_ch),
           R l m -> R (consltr i l) (consltr i m))
     (h4 : forall (b c : bool) (l m : l_ch),
           R l (consbl b m) -> R (consbl c l) (consbl b m))
     (h5 : forall l m n : l_ch, R l m -> R m n -> R l n) =>
   h5 x y z (t1 R h0 h1 h2 h3 h4 h5) (t2 R h0 h1 h2 h3 h4 h5).

(* Proprietes deduites des proprietes precedentes : *)

(* Eq est relexive : *)

 Definition Eq_re (l : l_ch) : Eq l l :=
   LCH_Ind l (fun u : l_ch => Eq u u) Eq_nil
     (fun (b : bool) (m : l_ch) => Eq_co_bl b b m m)
     (fun (i : Ind) (m : l_ch) => Eq_co_ltr i m m).
