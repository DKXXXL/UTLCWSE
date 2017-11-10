
Require Import Coq.Init.Datatypes.
Require Import Maps.
Require Import Coq.Strings.String.
Require Import Quotient.
Import Quotient.Quotient.
Require Import Context.
Require Import Coq.Lists.List.
Require Import LibTactics.

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
    | zerop : tm -> tm
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
    | SNum : Quot -> tm 
    (* All Quotient *)
    | SDouble : literal -> tm
    | SString : literal -> tm 
    | SPair : tm -> tm -> tm
    | SFun : id -> tm  -> tm
    | SSymbol : tm -> tm
    (* Statement *)
    | SSeq : tm -> tm -> tm
    | SLet : id -> tm -> tm -> tm
    | SFix : id -> id -> tm -> tm
    | SSys : id -> tm -> tm.

Hint Constructors tm.

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
    | SSys d x => SSys d (subst i to x)
    | SVar i' => if (eq_id_dec i i') then to else org
    | SPair p1 p2 => SPair (subst i to p1) (subst i to p2)
    | SFun x body => if (eq_id_dec i x) then org else SFun x (subst i to body)
    | SSeq b1 b2 => SSeq (subst i to b1) (subst i to b2)
    | SLet s bind body => if (eq_id_dec i s) 
                            then SLet s (subst i to bind) body
                            else SLet s (subst i to bind) (subst i to body)
    | SFix f x body => if (eq_id_dec i f)
                            then org
                            else if (eq_id_dec i x)
                                then org
                                else SFix f x (subst i to body)
    
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
    | vFix : forall idf idx tm,
        Value (SFix idf idx tm)
    | vSymbol : forall q,
            (forall pre post,
            q <> (SPair pre post)) ->
            Value (SSymbol q).

Hint Constructors Value.

Definition Env := Context.Context (type := tm).

(* I should make (Value tm)*)



Definition Output := list (id * tm).


Inductive step : (tm * Output) -> (tm * Output) -> Prop :=
    | spairp0 : forall j j' o1 o2,
                step (j ,o1) (j', o2) ->
                step ((pairp j), o1) ((pairp j'), o2)
    | spairpT : forall j pre post o1,
                Value j ->
                j = SPair pre post ->
                step ((pairp j), o1) (STrue, o1)
    | spairpF : forall j o1,
                Value j ->
                (forall pre post, j <> SPair pre post) ->
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
    | sapp3 : forall idf idx body arg o1,
                Value arg ->
                step ((sapp (SFix idf idx body) arg), o1) (([idf := (SFix idf idx body)] [idx := arg] body), o1)
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
                step ((sneg (SNum a)), o1) ((SNum (qneg a)), o1)
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
    

    | ssys0 : forall d a a' o1 o2,
                    step (a, o1) (a', o2) ->
                    step (SSys d a, o1) (SSys d a', o2)
    | ssys1 : forall d a o1,
                    Value a ->
                    step (SSys d a, o1) (STrue, (d,a):: o1)
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

Hint Constructors step.

Definition first {A B: Type} (x : A * B) : A :=
    match x with
        | (a, b) => a
    end.

Definition second {A B: Type} (x : A * B) : B :=
    match x with
        | (a, b) => b
    end.

Definition no_next (term : tm * Output) : Prop :=
    (~exists next, term ==> next).

Definition stuck ( term : tm * Output) : Prop :=
    (~ Value (first term)) \/ (no_next term).

Inductive TRC {Z : Type} (rel : Z -> Z -> Prop) : Z -> Z -> Prop :=
    | trcRefl : forall (x : Z), ((TRC rel) x x)
    | trcTrans : forall (x y z : Z), rel x y -> rel y z -> ((TRC rel) x z).

Definition multistep := TRC step.

Notation "a ==>* b" := (multistep a b) (at level 29).

Inductive machine {P O : Type} 
    (step : P*(list O) -> P*(list O) -> Prop) 
    (value : P -> Prop)
    (program : P) : P -> nat -> list O -> Prop :=
    | mO : machine step value program program 0 nil
    | mS : forall (a a' : P) (o1 o2 : list O) n,
        machine step value program a n o1 ->
        step (a, o1) (a', o2) ->
        machine step value program a' (S n) o2
    | mP : forall t' n o,
        machine step value program t' n o ->
        value t' ->
        machine step value program t' (S n) o.
(*
Definition machStep := machine step Value.

Definition intepreterCorrect (intep : nat -> tm -> Output) :=
    forall (n : nat) (t t': tm) (o : Output) 
    (mach : machStep t t' n o), 
    exists (m: nat) (t' : tm), intep m t = o.


Definition transformationCorrect (transf : tm -> tm) :=
    forall (n : nat) (t t': tm) (o : Output) (mach : machStep t t' n o),
    exists (m:nat) (t'' : tm), machStep (transf t) t' m o.
*)
Definition determinism {Z : Type} (step : Z -> Z -> Prop) :=
    forall x y1 y2, 
        step x y1 ->
        step x y2 ->
        y1 = y2.

Ltac general_val_ X u v :=
        match v with
          | 0 => X;(generalize dependent u)
          | _ => general_val_ ltac:(X; generalize dependent u) v
        end.
    
Ltac glize := general_val_ idtac.

Ltac forwardALL :=
    match goal with
     | H : ( _ -> _) |- _ => forwards* : H; generalize H; clear H; forwardALL
     | H : _ |- _ => idtac; intros
     end.


     Theorem Value_not_Steppable:
     forall x y o1 o2,
         Value x ->
         ~ (step (x, o1) (y, o2)).
 
     unfold not; intros x y o1 o2 h1;
     glize y o1 o2 0.
     induction h1; intros o2 o1 y h2; 
     inversion h2; subst.
     destruct (H a b eq_refl).
 Qed.
 

Ltac getInfo :=
 match goal with
 | H : (_,_) = _ |- _ => inversion H; subst; (try clear H) ; getInfo
 | |- _ => idtac
 end.


Ltac contra_ValueNotSteppable :=
try (intros;subst;
    match goal with
    | H0 : (step (?X, _) _) , H1 : Value ?X |- _ =>
    (destruct (Value_not_Steppable _ _ _ _ H1 H0); fail)
    | H0 : (step (_ ?X, _) _) , H1 : Value ?X |- _ =>
        (inversion H0; subst; try (clear H0; contra_ValueNotSteppable); fail)
    | |- _ => idtac
    end
).


Ltac IntroDestructAndAuto_Step :=
try (intros;subst;
try match goal with
| H : step (_ _ ,_) _ |- _ => inversion H; subst; clear H
end; 
subst;
forwardALL; subst;
try contra_ValueNotSteppable;
try match goal with
| H : _ = _ |- _ => inversion H; subst; clear H
end;
eauto
).

Ltac cpos H :=
    pose H as HIHIHI; generalize HIHIHI; clear HIHIHI; intro.





    Ltac Strong_contra_ValueNotSteppable :=
    try (
       match goal with
       | H: step (?X, _) _ |- _ => 
       assert (Value X);  eauto; 
       contra_ValueNotSteppable ; fail
       | H: step (?P ?X, _) _ |- _ =>
           inversion H; subst; clear H; Strong_contra_ValueNotSteppable; fail
       | |- _ => idtac
       end
    ).
   

Lemma detStep0 :
    forall x y y' o1 o2 o3,
        step (x, o1) (y, o2) ->
        step (x, o1) (y', o3) ->
        y = y'.
Proof.

    intros x y y' o1 o2 o3 h1;
    glize y' o3 0. 
    remember (x, o1) as s1;
    remember (y, o2) as s2.
    glize x y o1 o2 0.
    induction h1;
    intros; getInfo;
        IntroDestructAndAuto_Step;
        Strong_contra_ValueNotSteppable.
    destruct (H6 pre post eq_refl).
    destruct (H0 pre post eq_refl).                                                  
    assert (qinv a p = qinv a p0);
    try eapply qinv_det;subst; eauto.
    rewrite H; auto.

(* It's said to be the side effect from eauto. 
    No worry.
*)
    Unshelve.
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    auto. auto. 
 
Qed.
    

Lemma detStep1:
    forall x y y' o1 o2 o3,
        step (x, o1) (y, o2) ->
        step (x, o1) (y', o3) ->
            o2 = o3.

    intros x y y' o1 o2 o3 h1;
    glize y' o3 0. 
    remember (x, o1) as s1;
    remember (y, o2) as s2.
    glize x y o1 o2 0.
    induction h1;
    intros; getInfo;
    IntroDestructAndAuto_Step;
    Strong_contra_ValueNotSteppable.
    (* Again ..*)
    Unshelve. 
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    auto. auto.
Qed.

Theorem step_determinsm:
    determinism step.
    unfold determinism.
    intros.
    destruct x;
    destruct y1;
    destruct y2.
    assert (t0 = t1). eapply detStep0; eauto.
    assert (o0 = o1). eapply detStep1; eauto.
    subst; auto.
Qed.


(*
    Classify Unstuck Program.
    Without typing it.
    It's the most important part;
    or I cannot do induction on 'tm'.
*)

(*
    After Consideration,
    unstuck program is hard to classify without
    the help of typing. (And I also want sthing strong as sum type)
    (At least the two branch of if can give different type)
    So I only deal with those without free variable.
    And that makes the 'value' of the 'machine' changes
    to 'stuck' (no next step).
    I hope that makes things easier.
*)

(*
    The Whole VEmeschc is to verify:
        cps transform;
        name elimination;
        backend;
    Three parts. 
    A 'closed' program is all this need to compile.
    It's actually a variation of Emeschc.
    Parser and ToC is not going to be verified.
*)

(*
    Later, proof will largely be inductions on
    a closed program.
    I need an algorithm to check a 'tm' is closed or not.
*)

Definition no_step (t : tm) :=
    forall o, no_next (t, o).

Definition machStep := machine step no_step.

Definition intepreterCorrect (intep : nat -> tm -> Output) :=
    forall (n : nat) (t t': tm) (o : Output) 
    (mach : machStep t t' n o), 
    exists (m: nat) (t' : tm), intep m t = o.


Definition transformationCorrect (transf : tm -> tm) :=
    forall (n : nat) (t t': tm) (o : Output) (mach : machStep t t' n o),
    exists (m:nat) (t'' : tm), machStep (transf t) t' m o.

Inductive free : id -> tm -> Prop :=
    | fpairp : forall i x,
                free i x ->
                free i (pairp x)
    | fzerop : forall i x,
                free i x ->
                free i (zerop x)
    | fcar : forall i x,
                free i x ->
                free i (car x)
    | fcdr : forall i x,
                free i x ->
                free i (cdr x)
    | fapp0 : forall i x y,
                free i x ->
                free i (sapp x y)
    | fapp1 : forall i x y,
                free i y ->
                free i (sapp x y)
    | fadd0 : forall i x y,
                free i x ->
                free i (sadd x y)
    | fadd1 : forall i x y,
                free i y ->
                free i (sadd x y)
    | fmult0 : forall i x y,
                free i x ->
                free i (smult x y)
    | fmult1 : forall i x y,
                free i y ->
                free i (smult x y)
    | fcomp0 : forall i x y,
                free i x ->
                free i (sadd x y)
    | fcomp1 : forall i x y,
                free i y ->
                free i (sadd x y)

    
