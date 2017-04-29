Module ConceptualVM.

  
  Inductive C_Ty : Prop :=
  | _t_int : C_Ty
  | _t_pt : C_Ty
  | _t_float : C_Ty
  | _t_dbl: C_Ty
  | _t_bool : C_Ty
  | _t_char : C_Ty.
  
  Inductive C_Reg :nat -> C_Ty -> Type :=
  | _c_reg : forall n ty, C_Reg n ty.


  Inductive C_Const {X:Type} : C_Ty -> X -> Type :=.

  Definition unit_ptlong := nat.

  Definition VC_Reg id ty regnum := {x : C_Reg id ty | id < regnum}.

  
  Inductive C_op (regnum : nat) : Type :=
  | _op_add : forall ty id1 id2 id3,
                VC_Reg id1 ty regnum ->
                VC_Reg id2 ty regnum ->
                VC_Reg id3 ty regnum ->
                C_op regnum
(*  | _op_alloc : forall id1,
                  VC_Reg id1 _t_pt regnum ->
                  unit_ptlong ->
                  C_op regnum
*)  
(* Infinite Memory *)
  | _op_load : forall id1 id2 ty ,
                 VC_Reg id1 ty regnum ->
                 VC_Reg id2 _t_pt regnum ->
                 C_op regnum
  | _op_store : forall id1 id2 ty,
                  VC_Reg id1 _t_pt regnum ->
                  VC_Reg id2 ty regnum ->
                  C_op regnum
  | _op_label : nat -> C_op regnum
  | _op_jump : nat -> C_op regnum
  | _op_if: forall id1,
              VC_Reg id1 _t_bool regnum ->
              list (C_op regnum) ->
              list (C_op regnum) ->
              C_op regnum
  | _op_eq : forall ty id1 id2 id3,
               VC_Reg id1 ty regnum ->
               VC_Reg id2 ty regnum ->
               VC_Reg id3 _t_bool regnum ->
               C_op regnum
  | _op_not : forall id1 id2,
                VC_Reg id1 _t_bool regnum ->
                VC_Reg id2 _t_bool regnum ->
                C_op regnum
  | _op_and : forall id1 id2 id3,
                VC_Reg id1 _t_bool regnum ->
                VC_Reg id2 _t_bool regnum ->
                VC_Reg id3 _t_bool regnum ->
                C_op regnum
  | _op_cast : forall id1 id2 ty1 ty2,
                 VC_Reg id1 ty1 regnum ->
                 VC_Reg id2 ty2 regnum ->
                 C_op regnum
  | _op_assign : forall id1 ty X (x:X)  ,
                   VC_Reg id1 ty regnum ->
                   C_Const ty x ->
                   C_op regnum.

  
  Definition C_Program n := list (C_op n).

  Check length.


  Print list.


  Require Import List.
  

  Definition S_Regs := list nat.
  Definition VS_Regs (regnum ptlength: nat) (x: S_Regs) :=
    (forall y, In y x -> y < ptlength) /\
    (length x = regnum).
  Definition S_Stack := list nat.
  Definition VS_Stack (ptlength :nat) (x:S_Stack) := (forall y, In y x -> y < ptlength). 
  
  Inductive C_Mach_State {regnum ptlength : nat} (registers:S_Regs) (stack:S_Stack)
  :VS_Regs regnum ptlength registers ->
   VS_Stack ptlength stack ->
   C_Program regnum ->
   C_Program regnum -> Prop :=
  | cms : forall (p: VS_Regs regnum ptlength registers)
                 (q: VS_Stack ptlength stack)
                 (runned unrunned : C_Program regnum),
            C_Mach_State registers stack p q runned unrunned.
  

  Parameter pt_length : nat.
  Parameter reg_num : nat.
  (* Unlimited Register Number*)
  Definition CMS := C_Mach_State (regnum := reg_num) (ptlength := pt_length).
End ConceptualVM.
