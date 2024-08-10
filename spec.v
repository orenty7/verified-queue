
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import VQueue.queue.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.veric.version. 
Print release.

Definition t_list := Tstruct _list_t noattr.

Fixpoint listrep (values: list Z) (ptr: val) : mpred :=
  match values with
  | x::xs => 
      EX tail_ptr: val, 
        (malloc_token Ews t_list ptr 
        * data_at Ews t_list ((Vint (Int.repr x)), tail_ptr) ptr 
        * listrep xs tail_ptr)
  | nil => !! (ptr = nullval) && emp
  end.

Definition listrep_boxed (values: list Z) (dptr: val): mpred := 
  EX ptr, 
    data_at Ews (tptr t_list) ptr dptr *
    listrep values ptr. 

Lemma listrep_local_facts:
  forall values ptr,
   listrep values ptr |--
   !! (is_pointer_or_null ptr /\ (ptr = nullval <-> values = nil)).
Proof.
  intros.
  destruct values;
  unfold listrep.
  - entailer!.
    split; reflexivity.
  - Intros tail_ptr.
    fold listrep.
    entailer!.
    split.
    + intros ptr_is_null.
      subst.
      eapply field_compatible_nullval.
      eassumption.
    + intros E.
      discriminate.
Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall values ptr,
   listrep values ptr |-- valid_pointer ptr.
Proof.
  intros.
  destruct values.
  - entailer!.
    assert (ptr_is_null: ptr = nullval). { apply H. reflexivity. }
    subst.
    entailer!.
  - unfold listrep.
    Intros tail_ptr.
    fold listrep.
    entailer!.
Qed.
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.


Definition cons_spec: ident * funspec :=
  DECLARE _cons
    WITH values: list Z, new_value: Z, ptr: val, gv: globals
    PRE  [ tint, tptr t_list ]
      PROP (Int.min_signed <= new_value <= Int.max_signed) 
      PARAMS (Vint (Int.repr new_value); ptr)
      GLOBALS (gv)
      SEP (listrep values ptr; mem_mgr gv)
    POST [ (tptr t_list) ]
      EX new_ptr: val,
        PROP ()  
        RETURN (new_ptr)  
        SEP (listrep (new_value::values) new_ptr; mem_mgr gv).

Definition uncons_spec: ident * funspec := 
  DECLARE _uncons
    WITH head: Z, tail: list Z, dptr: val, gv: globals
    PRE [ tptr (tptr t_list) ]
      PROP () 
      PARAMS (dptr)
      GLOBALS (gv)
      SEP (
        listrep_boxed (head::tail) dptr;
        mem_mgr gv)
    POST [ tint ]
      PROP ()
      RETURN (Vint (Int.repr head))
      SEP (
        listrep_boxed tail dptr;
        mem_mgr gv).

Definition nreverse_spec: ident * funspec := 
  DECLARE _nreverse
    WITH values: list Z, ptr: val
    PRE [ tptr t_list ]
      PROP ()
      PARAMS (ptr)
      SEP (listrep values ptr)
    POST [ tptr t_list ]
      EX ptr: val,
        PROP ()
        RETURN (ptr)
        SEP (listrep (rev values) ptr).

Definition delete_list_spec: ident * funspec := 
  DECLARE _delete_list
    WITH values: list Z, ptr: val, gv: globals
    PRE [ tptr t_list ]
      PROP ()
      PARAMS (ptr)
      GLOBALS (gv)
      SEP (listrep values ptr; mem_mgr gv)
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (mem_mgr gv).

Definition t_queue := Tstruct _queue_t noattr.

Definition queuerep (values: list Z) (ptr: val) : mpred :=
  EX (output input: list Z) (output_ptr input_ptr: val), 
    !!(values = app output (rev input)) && (* values = output ++ rev input *)
    (malloc_token Ews t_queue ptr) * 
    (data_at Ews t_queue (input_ptr, output_ptr) ptr) *
    (listrep input input_ptr) * 
    (listrep output output_ptr).

Definition norm_queuerep (values: list Z) (ptr: val) : mpred :=
  EX (output input: list Z) (output_ptr input_ptr: val), 
    !!(output <> []) && 
    !!(values = app output (rev input)) &&
    (malloc_token Ews t_queue ptr) * 
    (data_at Ews t_queue (input_ptr, output_ptr) ptr) *
    (listrep input input_ptr) * 
    (listrep output output_ptr).

Definition new_queue_spec: ident * funspec := 
  DECLARE _new_queue
    WITH gv: globals
    PRE [ ]
      PROP () 
      PARAMS ()
      GLOBALS (gv)
      SEP (mem_mgr gv)
    POST [ tptr t_queue ]
      EX queue_ptr, 
        PROP ()
        RETURN (queue_ptr)
        SEP (queuerep [] queue_ptr; mem_mgr gv).

Definition push_back_spec: ident * funspec := 
  DECLARE _push_back
    WITH queue_ptr: val, queue_state: list Z, new_value: Z, gv: globals
    PRE [ tptr t_queue, tint ]
      PROP (Int.min_signed <= new_value <= Int.max_signed) 
      PARAMS (queue_ptr; (Vint (Int.repr new_value)))
      GLOBALS (gv)
      SEP (queuerep queue_state queue_ptr; mem_mgr gv)
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (queuerep (app queue_state [new_value]) queue_ptr; mem_mgr gv).

Definition normalize_spec: ident * funspec :=
  DECLARE _normalize
    WITH queue_ptr: val, head: Z, rest: list Z, gv: globals
    PRE [ tptr t_queue ]
      PROP ()
      PARAMS (queue_ptr)
      GLOBALS (gv)
      SEP (queuerep (head::rest) queue_ptr; mem_mgr gv)
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (norm_queuerep (head::rest) queue_ptr; mem_mgr gv).

Definition pop_front_spec: ident * funspec :=
  DECLARE _pop_front
    WITH queue_ptr: val, head: Z, rest: list Z, gv: globals
    PRE [ tptr t_queue ]
      PROP ()
      PARAMS (queue_ptr)
      GLOBALS (gv)
      SEP (queuerep (head::rest) queue_ptr; mem_mgr gv)
    POST [ tint ]
      PROP ()
      RETURN (Vint (Int.repr head))
      SEP (queuerep rest queue_ptr; mem_mgr gv).


Definition delete_queue_spec: ident * funspec := 
  DECLARE _delete_queue
    WITH values: list Z, ptr: val, gv: globals
    PRE [ tptr t_queue ]
      PROP ()
      PARAMS (ptr)
      GLOBALS (gv)
      SEP (queuerep values ptr; mem_mgr gv)
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (mem_mgr gv).

Definition Gprog : funspecs := ltac: (with_library prog [ 
  cons_spec; 
  uncons_spec;
  nreverse_spec; 
  delete_list_spec;

  new_queue_spec;
  push_back_spec; 
  normalize_spec;
  pop_front_spec;
  delete_queue_spec
]).

Lemma body_cons: semax_body Vprog Gprog f_cons cons_spec.
Proof.
  start_function.
  forward_call (t_list, gv).
  Intros vret.
  forward_if (
    PROP ()
    LOCAL (temp _new_cell vret; gvars gv; temp _value (Vint (Int.repr new_value)); temp _tail ptr)
    SEP (
      mem_mgr gv;
      malloc_token Ews t_list vret * data_at_ Ews t_list vret;
      listrep values ptr
    )
  ).
  - destruct vret; subst;
    try (
      unfold is_pointer_or_null in PNvret;
      contradiction
    ).
    + unfold is_pointer_or_null in PNvret.
      simpl in PNvret.
      subst.
      entailer!.
    + simpl.
      entailer!.
  - forward_call.
    entailer!.
  - forward.
    entailer!.
    destruct vret; subst;
    try (
      unfold is_pointer_or_null in PNvret;
      contradiction
    ).
    + unfold is_pointer_or_null in PNvret.
      simpl in PNvret.
      subst.
      unfold nullval in H.
      simpl in H.
      contradiction.
    + simpl.
      entailer!. 
  - Intros.
    forward.
    forward.
    forward.
    Exists vret.
    entailer!.
    unfold listrep.
    fold listrep.
    Exists ptr.
    entailer!.
Qed.

Lemma body_uncons: semax_body Vprog Gprog f_uncons uncons_spec.
Proof.
  start_function.
  unfold listrep_boxed.
  Intros ptr.
  forward.
  unfold listrep.
  fold listrep.
  Intros tail_ptr.
  forward.
  forward.
  forward.   
  forward.
  forward_call (t_list, ptr, gv).
  { entailer!.
    destruct ptr;
    try (entailer!).
    simpl.
    entailer!. }
  forward.
  forward.
  unfold listrep_boxed.
  Exists tail_ptr.
  entailer!.
Qed.

Lemma body_nreverse: semax_body Vprog Gprog f_nreverse nreverse_spec.
Proof.
  start_function.
  forward.
  forward.

  forward_while (EX s1 s2 prev_ptr curr_ptr,
    PROP (values = app (rev s1) s2)
    LOCAL (
      temp _curr curr_ptr; 
      temp _prev prev_ptr;
      temp _list ptr
    )
    SEP (listrep s1 prev_ptr; listrep s2 curr_ptr)
  ).
  - Exists (@nil Z) values.
    Exists nullval ptr.
    unfold listrep.
    entailer!.
  - entailer!.
  - destruct s2.
    { unfold listrep.
      fold listrep.
      Intros.
      subst curr_ptr.
      contradiction. }
    unfold listrep. fold listrep.
    Intros tail_ptr.
    forward.
    forward.
    forward.
    forward.
    Exists ((z::s1), s2, curr_ptr, tail_ptr).
    entailer!.
    { simpl. rewrite <- app_assoc. simpl. reflexivity. }
    entailer!. 
    unfold listrep. 
    fold listrep.
    Exists prev_ptr.
    entailer!.
  - forward.
    assert (s2_empty: s2 = []).
    { apply H1. reflexivity. } 
    subst. 
    Exists prev_ptr.
    entailer!.
    rewrite app_nil_r.
    rewrite rev_involutive.
    unfold listrep.
    entailer!.
Qed.

Lemma body_delete_list: semax_body Vprog Gprog f_delete_list delete_list_spec.
Proof.
  start_function.
  forward_while (EX values ptr,
    PROP () 
    LOCAL (gvars gv; temp _list ptr) 
    SEP (listrep values ptr; mem_mgr gv)
  ).
  - entailer!.
    Exists values ptr.
    entailer!.
  - entailer!.
  - forward.
    destruct values0.
    { unfold listrep. Intros. subst. contradiction. }
    unfold listrep.
    fold listrep.
    Intros tail_ptr.
    forward.
    forward_call (t_list, ptr0, gv).
    + destruct ptr0;
      try contradiction.
      simpl.
      entailer!.
    + Exists (values0, tail_ptr).
      entailer!.
      entailer!.
  - forward.
    entailer!.
    assert (values0_is_nil: values0 = []).
    { apply H. reflexivity. }
    rewrite values0_is_nil.
    unfold listrep.
    entailer!.
Qed.

Lemma body_new_queue: semax_body Vprog Gprog f_new_queue new_queue_spec.
Proof.
  start_function.
  forward_call (t_queue, gv).
  Intros vret.
  forward_if (
    PROP ()
    LOCAL (temp _queue_ptr vret; gvars gv)
    SEP (
      malloc_token Ews t_queue vret;
      data_at_ Ews t_queue vret;
      mem_mgr gv
    )
  ).
  - destruct vret;
    try contradiction.
    + inversion PNvret. subst.
      simpl.
      entailer!.
    + simpl. entailer!.
  - forward_call.
    entailer!.
  - forward.
    entailer!.
    destruct vret;
    try contradiction.
    + inversion PNvret. subst.
      contradiction.
    + simpl. entailer!.
  - forward.
    forward.
    forward.
    Exists vret.
    unfold queuerep.
    Exists (@nil Z) (@nil Z) nullval nullval.
    entailer!.
    unfold listrep.
    entailer!.
Qed.

Lemma body_push_back: semax_body Vprog Gprog f_push_back push_back_spec.
Proof.
  start_function.
  forward.
  forward_call.
  Intros new_input_ptr.
  forward.
  entailer!.
  unfold queuerep.
  
  Exists output (new_value :: input).
  Exists output_ptr new_input_ptr.
  entailer!.
  simpl.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma body_normalize: semax_body Vprog Gprog f_normalize normalize_spec.
Proof.
  start_function.
  forward.
  forward_if.
  + forward.
    forward_call.
    Intros reversed_input_ptr.
    forward.
    forward.
    unfold norm_queuerep.
    Exists (rev input) (@nil Z) reversed_input_ptr nullval.
    entailer!.
    - assert (output_is_nil: output = []).
      { apply H5. reflexivity. }
      subst.
      simpl in H.
      split.
      * intros input_is_nil.
        rewrite input_is_nil in H.
        discriminate.
      * rewrite H.
        simpl.
        rewrite app_nil_r.
        reflexivity.
    - assert (output_is_nil: output = []).
      { apply H5. reflexivity. }
      subst.
      entailer!.
  + forward.
    entailer!.
    unfold norm_queuerep.
    Exists output input output_ptr input_ptr.
    entailer!.
    apply H0.
    apply H5.
    reflexivity.
Qed.

Lemma body_pop_front: semax_body Vprog Gprog f_pop_front pop_front_spec.
Proof.
  start_function.
  forward_call.
  unfold norm_queuerep.
  Intros output input output_ptr input_ptr.

  destruct output as [|output_head output_tail].
  { contradiction. }
  inversion H0.
  subst.
  clear H H0.

  unfold_data_at (data_at _ _ _ queue_ptr).
  rewrite (field_at_data_at _ _ (DOT _out) _ _).
  
  sep_apply (data_at_local_facts 
    Ews 
    (nested_field_type t_queue (DOT _out)) 
    output_ptr 
    (field_address t_queue (DOT _out) queue_ptr)
  ).
  
  Intros.
  forward_call (output_head, output_tail, (field_address t_queue (DOT _out) queue_ptr), gv).
  - unfold listrep_boxed.
    Exists output_ptr.
    entailer!.
  - forward.
    unfold queuerep.
    Exists output_tail input.
    unfold listrep_boxed.
    Intros output_tail_ptr.
    Exists output_tail_ptr.
    Exists input_ptr.
    entailer!.
    unfold_data_at (data_at _ _ _ queue_ptr).
    entailer!.
Qed.


Lemma body_delete_queue: semax_body Vprog Gprog f_delete_queue delete_queue_spec.
Proof.
  start_function.
  forward.
  forward_call.
  forward.
  forward_call.
  forward_call (t_queue, ptr, gv).
  { entailer!.
    apply field_compatible_isptr in H1.
    destruct ptr;
    try contradiction.
    simpl.
    entailer!. }
  entailer!.
Qed.
