
Require Import Coq.Init.Datatypes.
Require Import Maps.
Require Import Coq.Strings.String.
Require Import Quotient.
Import Quotient.Quotient.
Require Import Context.
Require Import Coq.Lists.List.

Module UTLCWOSE.


    
Definition literal := string.

Definition disjoint_sum (A B : Prop) : Prop :=
    (A \/ B) /\ (A -> ~ B).

Definition ctxId := id.


(* Dynamic Typed Lambda calculus with fixpoint,
 type inference is nt so trivial*)
(*
Inductive ty : Type :=
    | TList : ty -> ty 
    | TNum : ty 
    | TBool : ty
    | TPair : ty -> ty -> ty
    | TFun : ty -> ty -> ty.
*)



Inductive tm : Type :=
    (* Predicate *)
    (*| atomp : tm -> tm *)
    | pairp : tm -> tm 
    (* Operator*) 
    | car : tm -> tm 
    | cdr : tm -> tm 
    | cond : tm -> tm -> tm -> tm 
    | sapp : tm -> tm -> tm
    | sadd : tm -> tm -> tm 
    | smult : tm -> tm -> tm 
    | sneg : tm -> tm
    | sinverse : tm -> tm 
    | scomp : tm -> tm -> tm 
    | soutput : tm -> tm
    (* Constructor *)
    | SVar : id -> tm
    | STrue : tm 
    | SFalse : tm 
    | SNum : Quot -> tm 
    (* All Quotient *)
    | SDouble : literal -> tm
    | SString : literal -> tm 
    | SPair : tm -> tm -> tm
    | SFun : id -> tm  -> tm
    | SSymbol : tm -> tm
    (* Statement *)
    | SSeq : tm -> tm -> tm
    | SLet : id -> tm -> tm -> tm.

Fixpoint subst (i : id) (to : tm) (org : tm) : tm :=
    match org with
    | pairp k => pairp (subst i to k)
    | car p => car (subst i to p)
    | cdr p => cdr (subst i to p)
    | cond j b1 b2 => cond (subst i to j) (subst i to b1) (subst i to b2)
    | sapp f x => sapp (subst i to f) (subst i to x)
    | sadd n m => sadd (subst i to n) (subst i to m)
    | smult n m => smult (subst i to n) (subst i to m)
    | sneg n => sneg (subst i to n)
    | sinverse n => sinverse (subst i to n)
    | scomp n m => scomp (subst i to n) (subst i to m)
    | soutput x => soutput (subst i to x)
    | SVar i' => if (eq_id_dec i i') then to else org
    | SPair p1 p2 => SPair (subst i to p1) (subst i to p2)
    | SFun x body => if (eq_id_dec i x) then org else SFun x (subst i to body)
    | SSeq b1 b2 => SSeq (subst i to b1) (subst i to b2)
    | SLet s bind body => if (eq_id_dec i s) 
                            then SLet s (subst i to bind) body
                            else SLet s (subst i to bind) (subst i to body)
    
    | _ => org
    end.

Notation " [ x := y ] k" := (subst x y k) (at level 50).
Inductive Value : tm -> Prop :=
    | vTrue : Value STrue
    | vFalse : Value SFalse
    | vNum : forall q, Value (SNum q)
    | vDouble : forall s, Value (SDouble s)
    | vString : forall s, Value (SString s)
    | vPair : forall pre post,
        Value pre ->
        Value post ->
        Value (SPair pre post)
    | vFun : forall id tm, 
        Value (SFun id tm)
    | vSymbol : forall q pre post,
            q <> (SPair pre post) ->
            Value (SSymbol q).

Definition Env := Context.Context (type := tm).

(* I should make (Value tm)*)



Definition Output := list tm.


Inductive step : (tm * Output) -> (tm * Output) -> Prop :=
    | spairp0 : forall j j' o1 o2,
                step (j ,o1) (j', o2) ->
                step ((pairp j), o1) ((pairp j'), o2)
    | spairpT : forall j pre post o1,
                Value j ->
                j = SPair pre post ->
                step ((pairp j), o1) (STrue, o1)
    | spairpF : forall j pre post o1,
                Value j ->
                j <> SPair pre post ->
                step ((pairp j), o1) (SFalse, o1)
    | scar0 : forall j j' o1 o2,
                step (j, o1) (j' , o2) ->
                step ((car j), o1) ((car j'), o2)
    | scar1 : forall pre post o1,
                Value pre ->
                Value post ->
                step ((car (SPair pre post)), o1) (pre, o1)
    | scdr0: forall j j' o1 o2,
                step (j, o1) (j', o2) ->
                step ((cdr j), o1) ((cdr j'), o2)
    | scdr1 : forall pre post o1,
                Value pre ->
                Value post ->
                step ((cdr (SPair pre post)), o1) (post, o1)
    | scond0 : forall j j' a b o1 o2,
                step (j, o1) (j', o2) ->
                step ((cond j a b), o1) ((cond j' a b), o2)
    | scondT : forall a b o1,
                step ((cond STrue a b), o1) (a, o1)
    | scondF : forall a b o1,
                step ((cond SFalse a b), o1) (b, o1)
    | sapp0 : forall f f' x o1 o2,
                step (f, o1) (f', o2) ->
                step ((sapp f x), o1) ((sapp f' x), o2)
    | sapp1 : forall f x x' o1 o2,
                Value f ->
                step (x, o1) (x', o2) ->
                step ((sapp f x), o1) ((sapp f x'), o2)
    | sapp2 : forall id body arg o1,
                Value arg ->
                step ((sapp (SFun id body) arg), o1) (([ id := arg ] body), o1)
    | sadd0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((sadd a b), o1) ((sadd a' b), o2)
    | sadd1 : forall a b b' o1 o2,
                Value a ->
                step (b, o1) (b', o2) ->
                step ((sadd a b), o1) ((sadd a b'), o2)
    | sadd2 : forall a b o1,
                step ((sadd (SNum a) (SNum b)), o1) ((SNum (qplus a b)), o1)
    
    | smult0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((smult a b), o1) ((smult a' b), o2)
    | smult1 : forall a b b' o1 o2,
                Value a ->
                step (b, o1) (b', o2) ->
                step ((smult a b), o1) ((smult a b'), o2)
    | smult2 : forall a b o1,
                step ((smult (SNum a) (SNum b)), o1) ((SNum (qmultply a b)), o1)
    | sneg0 : forall a a' o1 o2,
                step (a, o1) (a', o2) ->
                step ((sneg a), o1) ((sneg a'), o2)
    | sneg1 : forall a o1,
                step ((SNum a), o1) ((SNum (qneg a)), o1)
    | sinv0 : forall a a' o1 o2,
                step (a, o1) (a', o2) ->
                step ((sinverse a), o1) ((sinverse a'), o2)
    | sinv1 : forall a o1 (p : ~iszero a),
                step ((sinverse (SNum a)), o1) ((SNum (qinv a p)), o1)
    (* If it's zero, stuck *)
    | scomp0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((scomp a b), o1) ((scomp a' b), o2)
    | scomp1 : forall a b b' o1 o2,
                Value a ->
                step (b, o1) (b', o2) ->
                step ((scomp a b), o1) ((scomp a b'), o2)
    | scomp2 : forall a b o1,
                step ((scomp (SNum a) (SNum b)), o1) ((SNum (qcomp a b)), o1)
    
    | soutput0 : forall a a' o1 o2,
                step (a, o1) (a', o2) ->
                step ((soutput a), o1) ((soutput a'), o2)
    | soutput1 : forall a o1,
                Value a ->
                step ((soutput a), o1) (STrue, (cons a o1))
    | ssymbol : forall a b o1,
                step ((SSymbol (SPair a b)), o1) ((SPair (SSymbol a) (SSymbol b)), o1)
    | sseq0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((SSeq a b), o1) ((SSeq a' b), o2)
    | sseq1 : forall a b  o1,
                Value a ->
                step ((SSeq a b), o1) (b, o1)
    | slet0 : forall i bind bind' body o1 o2,
                step (bind, o1) (bind', o2) ->
                step ((SLet i bind body), o1) ((SLet i bind' body), o2)
    | slet1 : forall i bind body o1,
                Value bind ->
                step ((SLet i bind body), o1) (([ i := bind ] body), o1).
   
Notation "a ==> b" := (step a b) (at level 30).

Definition first {A B: Type} (x : A * B) : A :=
    match x with
        | (a, b) => a
    end.
        

Definition stuck ( term : tm * Output) : Prop :=
    (~ Value (first term)) \/ (~ exists next, term ==> next).

Inductive TRC {Z : Type} (rel : Z -> Z -> Prop) : Z -> Z -> Prop :=
    | trcRefl : forall (x : Z), ((TRC rel) x x)
    | trcTrans : forall (x y z : Z), rel x y -> rel y z -> ((TRC rel) x z).

Definition multistep := TRC step.

Notation "a ==>* b" := (multistep a b) (at level 29).









