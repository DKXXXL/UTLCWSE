Require Import SfLib.
Require Import Coq.Strings.String.
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
    | atomp : tm -> tm 
    | pairp : tm -> tm 
    | eqp : tm -> tm -> tm
    (* Operator*) 
    | car : tm -> tm 
    | cdr : tm -> tm 
    | cond : tm -> tm -> tm -> tm 
    | sadd : tm -> tm -> tm 
    | ssub : tm -> tm -> tm 
    | smult : tm -> tm -> tm 
    | sdivide : tm -> tm -> tm 
    | setcar : tm -> tm
    | setcdr : tm -> tm 
    | setv : id -> tm -> tm 
    (* Constructor *)
    | STrue : tm 
    | SFalse : tm 
    | SNum : nat -> nat -> tm 
    (* All Quotient *)
    | SDouble : literal -> tm
    | SString : literal -> tm 
    | SPair : tm -> tm -> tm
    | SFun : id -> tm -> ctxId -> tm
    | SSymbol : tm -> tm
    | SCont : tm -> tm s
    (* Statement *)
    | SSeq : tm -> tm -> tm
    | SLet : id -> tm -> tm
    | SLetc : id -> tm -> tm.


Inductive Value : tm -> Prop :=
    | vTrue : Value STrue
    | vFalse : Value SFalse
    | vNum : forall n d, Value (SNum n d)
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






