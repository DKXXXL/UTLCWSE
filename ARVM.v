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

  
  Inductive R_op : Type :=
  | _ro_add : forall id1 id2 id3 (x: R_Ty 1),
                R_pt id1 x ->
                R_pt id2 x ->
                R_pt id3 x ->
                R_op
  | _ro_cons : forall id1 id2 id3 x' y' (x:R_Ty x') (y: R_Ty y') ,
                 R_pt id1 _rt_cons ->
                 R_pt id2 x ->
                 R_pt id3 y ->
                 R_op
  | _ro_strloc : forall id1 x ,
                   R_pt id1 (_rt_str x) ->
                   R_op
  | _ro_symloc : forall id1 x ,
                   R_pt id1 (_rt_qsym x)->
                   R_op
  | _ro_cast : forall id1 id2 x' (x : R_Ty x') (y :R_Ty x'),
                 R_pt id1 x ->
                 R_pt id2 y ->
                 R_op
  | _ro_input : forall id1 x (y: R_Ty x),
                  R_pt id1 y ->
                  R_Syscall ->
                  R_op
  | _ro_output : forall id1 x (y:R_Ty x),
                   R_pt id1 y ->
                   R_Syscall ->
                   R_op
  | _ro_label : nat -> R_op
  | _ro_jump : nat -> R_op
  | _ro_if: forall id1,
              R_pt id1 _rt_bool ->
              list R_op ->
              list R_op ->
              R_op
  | _ro_assgn1 : forall id1 id2 x (y:R_Ty x),
                   R_pt id1 y ->
                   R_pt id2 y ->
                   R_op
  | _ro_assgn2 : forall id1 x (y:R_Ty x),
                   R_pt id1 y ->
                   R_Const y ->
                   R_op
  | _ro_syscall : R_Syscall -> R_op.

End ARVM.

