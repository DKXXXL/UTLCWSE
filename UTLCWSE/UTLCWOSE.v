Require Import SfLib.
Require Import Coq.Strings.String.
Require Import Quotient.
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
    (* Constructor *)
    | SVar : id -> tm
    | STrue : tm 
    | SFalse : tm 
    | SNum : Quotient.Quot -> tm 
    (* All Quotient *)
    | SDouble : literal -> tm
    | SString : literal -> tm 
    | SPair : tm -> tm -> tm
    | SFun : id -> tm -> ctxId -> tm
    | SSymbol : tm -> tm
    (* Statement *)
    | SSeq : tm -> tm -> tm
    | SLet : id -> tm -> tm -> tm.


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
    | vFun : forall id tm ctx, 
        Value (SFun id tm ctx)
    | vSymbol : forall q pre post,
            q <> (SPair pre post) ->
            Value (SSymbol q).


Inductive step : tm -> tm -> Prop :=
    | spairp0 : forall j j',
                step j j' ->
                step (pairp j) (pairp j')
    | spairpT : forall j pre post,
                Value j ->
                j = SPair pre post ->
                step (pairp j) STrue
    | spairpF : forall j pre post,
                Value j ->
                j <> SPair pre post ->
                step (pairp j) SFalse

    | scar0 : forall j j',
                step j j' ->
                step (car j) (car j')
    | scar1 : forall pre post,
                Value pre ->
                Value post ->
                step (car (SPair pre post)) pre
    | scdr0: forall j j',
                step j j' ->
                step (cdr j) (cdr j') 
    | scdr1 : forall pre post,
                Value pre ->
                Value post ->
                step (cdr (SPair pre post)) post
    | scond0 : forall j j' a b,
                step j j' ->
                step (cond j a b) (cond j' a b)
    | scondT : forall a b,
                step (cond STrue a b) a
    | scondF : forall a b,
                step (cond SFalse a b) b
    | sapp0 : forall f f' x,
                step f f' ->
                step (sapp f x) (sapp f' x)
    | sapp1 : forall f x x',
                Value f ->
                step x x' ->
                step (sapp f x) (sapp f x')
    | sapp2 : forall id body 
    | sadd0 : forall a a' b,
                step a a' ->
                step (sadd a b) (sadd a' b)
    | sadd1 : forall a b b',
                Value a ->
                step b b' ->
                step (sadd a b) (sadd a b')
    | sadd2 : forall a b,
                step (sadd (SNum a) (SNum b)) (SNum (qplus a b))
    
    | smult0 : forall a a' b,
                step a a' ->
                step (smult a b) (smult a' b)
    | smult1 : forall a b b',
                Value a ->
                step b b' ->
                step (smult a b) (smult a b')
    | smult2 : forall a b,
                step (smult (SNum a) (SNum b)) (SNum (qmultply a b))
    | sneg0 : forall a a',
                step a a' ->
                step (sneg a) (sneg a')
    | sneg1 : forall a,
                step (SNum a) (SNum (qneg a))
    | sinv0 : forall a a',
                step a a' ->
                step (sinverse a) (sinverse a')
    | sinv1 : forall a (p : ~iszero a),
                step (sinverse (SNum a)) (SNum (qinv a p))
    (* If it's zero, stuck *)
    | scomp0 : forall a a' b,
                step a a' ->
                step (scomp a b) (scomp a' b)
    | scomp1 : forall a b b',
                Value a ->
                step b b' ->
                step (scomp a b) (scomp a b')
    | scomp2 : forall a b,
                step (scomp (SNum a) (SNum b)) (SNum (qcomp a b))
    | 
    
    









