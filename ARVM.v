(* Non-Pointer (All Referenced) Virtual Machine *)

Module ARVM.

  Definition unit_ptlong := nat.
  
  Inductive R_Ty : unit_ptlong -> Type :=
  | _rt_int : R_Ty 1
  | _rt_float : R_Ty 1
  | _rt_dbl : R_Ty 1
  | _rt_bool : R_Ty 1
  | _rt_char : R_Ty 1
  | _rt_cons : R_Ty 2
  (* fixed length*)                  
  | _rt_str : forall n, R_Ty n
  | _rt_qsym : forall n, R_Ty n.
  
  Inductive R_pt {x:unit_ptlong} : nat -> R_Ty x -> Type :=.

  Inductive R_Const {x:unit_ptlong} : R_Ty x -> Type :=.

  Inductive R_Syscall : Type :=
  | _rs_obj : nat -> R_Syscall.


  Require Import JMeq.
  
  Inductive R_op : Type :=
  | _ro_add : forall id1 id2 id3 (x: R_Ty 1),
                R_pt id1 x ->
                R_pt id2 x ->
                R_pt id3 x ->
                R_op
  (*
   _ro_car; _ro_cdr : 
   _ro_set_car; _ro_set_cdr
   *)
                  
  | _ro_alloc : forall id1 x (y: R_Ty x),
                  JMeq y _rt_cons ->
                  R_pt id1 y ->
                  R_op
  | _ro_cons : forall id1 id2 id3 x1 x2 (y1 : R_Ty x1) (y2 : R_Ty x2),
                 R_pt id1 _rt_cons ->
                 R_pt id2 y1 ->
                 R_pt id3 y2 ->
                 R_op
  | _ro_car : forall id1 id2 x (y : R_Ty x),
                R_pt id1 y ->
                R_pt id2 _rt_cons ->
                R_op
  | _ro_cdr : forall id1 id2 x (y: R_Ty x),
                R_pt id1 y ->
                R_pt id2 _rt_cons ->
                R_op
  | _ro_cast : forall id1 id2 x' (x : R_Ty x') (y :R_Ty x'),
                 R_pt id1 x ->
                 R_pt id2 y ->
                 R_op
  | _ro_input : forall id1 x,
                  R_pt id1 (_rt_str x) ->
                  R_Syscall ->
                  R_op
  | _ro_output : forall id1 x,
                   R_pt id1 (_rt_str x) ->
                   R_Syscall ->
                   R_op
  | _ro_label : nat -> R_op
  | _ro_jump : nat -> R_op
  | _ro_if: forall id1,
              R_pt id1 _rt_bool ->
              list R_op ->
              list R_op ->
              R_op
  | _ro_assgn : forall id1 id2 x (y:R_Ty x) (y' : R_Ty x),
                  R_pt id1 y ->
                  R_pt id2 y' ->
                  R_op
  (* repoint the pointer to new pointer*)
  | _ro_mutate : forall id1 id2 (size start continue : unit_ptlong)
                        (y: R_Ty size) (z: R_Ty continue) ,
                   R_pt id1 y ->
                   size > start + continue ->
                   R_pt id2 z ->
                   R_op
  (* Mutate the object pointed by the pointer*)
  | _ro_syscall : R_Syscall -> R_op.

End ARVM.

