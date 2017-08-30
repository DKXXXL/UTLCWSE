Require Import SfLib.
Require Import Coq.Strings.String.
Module UTLCWOSE.
    
Definition literal := string.

Definition disjoint_sum (A B : Prop) : Prop :=
    (A \/ B) /\ (A -> ~ B).

Definition ctxId := id.
(* Dynamic Typed Lambda calculus with fixpoint,
 type inference is nt so trivial*)
Inductive ty : Type :=
    | TList : ty -> ty 
    | TNum : ty 
    | TBool : ty
    | TPair : ty -> ty -> ty
    | TFun : ty -> ty -> ty.




Inductive tm : Type :=
    (* Predicate *)
    | atomp : tm -> tm 
    | pairp : tm -> tm 
    | eqp : tm -> tm -> tm 
    | quote : tm -> tm 
    (* Operator*) 
    | car : tm -> tm 
    | cdr : tm -> tm 
    | cond : tm -> tm -> tm -> tm 
    | sadd : tm -> tm -> tm 
    | ssub : tm -> tm -> tm 
    | smult : tm -> tm -> tm 
    | sdivide : tm -> tm -> tm 
    (* Constructor *)
    | cons : tm -> tm -> tm
    | SNum : literal -> tm 
    | SString : literal -> tm 
    | Strue : tm 
    | Sfalse : tm 
    | SFun : id -> tm -> ctxId -> tm
    (* Statement *)
    | SSeq : tm -> tm -> tm
    | SLet : id -> tm -> tm.

