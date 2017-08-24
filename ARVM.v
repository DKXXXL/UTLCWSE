(* Non-Pointer (All Referenced) Virtual Machine *)

Require Import SfLib.
Require Import Coq.Strings.String.


Module ARVM.

  Definition unit_ptlong := nat.
  Definition literal := string.
  Definition syscall_id := nat.
  Definition typename := string.

  (* Weak typing *)
  (* Fixed Sized typing *)
  (* No customized typing *)
  
  
  Inductive R_Ty : unit_ptlong -> Type :=
  | _rt_int : R_Ty 1
  | _rt_float : R_Ty 1
  | _rt_dbl : R_Ty 1
  | _rt_bool : R_Ty 1
  | _rt_char : R_Ty 1
  | _rt_pointer : forall size, R_Ty size -> R_Ty 1
  (* A meta-type. For expressability. *)
  (* fixed length*)                  
  | _rt_str : forall n, R_Ty n (* Str *)
  | _rt_qsym : forall n, R_Ty n (* Quote, symbol, meta*)
  | _rt_data : forall n, typename -> R_Ty n 
  (* Customized Data type, 
  typename is annotation
  customerized type is identified by name and size
  *)
  .
  
  
  Inductive R_Const {x:unit_ptlong} : literal -> R_Ty x -> Type :=
  | _r_const : forall const ty, R_Const const ty. 

  Inductive R_pt {x:unit_ptlong} : id -> R_Ty x -> Type :=
  | _r_alloc : forall id ty, R_pt id ty
  | _r_cast : forall id (y z : R_Ty x), 
                R_pt id y ->
                R_pt id z
  | _r_ro : forall id ty const,
              R_Const const ty ->
              R_pt id ty.
  (* Read only data retrieved. 
  Get the pointer points to the read_only data *)




  Inductive R_Syscall : Type :=
  | _rs_obj : syscall_id -> R_Syscall.

  
  Inductive R_op : Type :=
  | _ro_add : forall id1 id2 id3 (x: R_Ty 1),
                R_pt id1 x ->
                R_pt id2 x ->
                R_pt id3 x ->
                R_op
  (*
   _ro_car; _ro_cdr : 
   _ro_set_car; _ro_set_cdr
   
                  
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
                 *)
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
  (*
  | _ro_repoint : forall id1 id2 x (y:R_Ty x) (y' : R_Ty x),
                  R_pt id1 y ->
                  R_pt id2 y' ->
                  R_op *)
  (* repoint the pointer to new pointer*)
  (** Deprecated: I don't need some pointer to be mutable **)
  | _ro_assign : forall src dst x (y:R_Ty x) ,
                  R_pt src y ->
                  R_pt dst y ->
                  R_op
  (* Copy the object from src to dst, weaker than mutate, type-safe *)

  | _ro_set' : forall src dst x (y:R_Ty x) (y' : R_Ty x),
                  R_pt src y ->
                  R_pt dst y' ->
                  R_op
  (* Copy the object from src to dst, weaker than mutate, type-unsafe *)

  | _ro_mutate : forall src dst (size start continue : unit_ptlong)
                        (y: R_Ty size) (z: R_Ty continue) ,
                   R_pt src y ->
                   size > start + continue ->
                   R_pt dst z ->
                   R_op
  (* Copy the data from src to dst*)
  | _ro_syscall : R_Syscall -> R_op.

End ARVM.

