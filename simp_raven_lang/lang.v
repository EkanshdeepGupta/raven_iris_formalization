From stdpp Require Export strings.
From stdpp Require Import gmap list.
From iris.program_logic Require Export language ectx_language ectxi_language.

Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp 
| EqOp | NeOp | LtOp
| GtOp | LeOp | GeOp
| AndOp | OrOp.

Inductive un_op : Set :=
| NotBoolOp | NegOp.

Section expr.

Inductive typ :=
| TpInt | TpLoc | TpBool | TpUnit.

Global Instance typ_eq_decision : EqDecision typ.
Proof. solve_decision. Qed.

Scheme Equality for typ.

Record loc := Loc { loc_car : Z }.

(* Type class instances for loc *)
Global Instance loc_eq_decision : EqDecision loc.
Proof.
  solve_decision.
Qed.

Global Instance loc_countable : Countable loc.
Proof.
  refine (inj_countable' loc_car (λ x, Loc x) _).
  intros [x]. simpl. f_equal.
Qed.

Definition fld_name := string.
Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

Definition var := string.
Definition proc_name := string.

Inductive expr :=
| Var (x : var)
| Val (v : val)
| UnOp (op : un_op) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| IfE (e1 e2 e3 : expr)
| StuckE (* stuck expression *)
with
val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc).

Global Instance val_dec_eq : EqDecision val.
Proof.
  solve_decision.
Qed.

End expr.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : expr) *)
| IfS (e : expr) (s1 s2 : stmt)
| Assign (v : var) (e : expr)
(* | Free (e : expr) *)
| SkipS
| StuckS (* stuck statement *)
(* | ExprS (e : expr) *)
| Call (v : var) (proc : proc_name) (args : list expr)
| FldWr (v : var) (fld : fld_name) (e2 : expr) 
| FldRd (v : var) (e : expr) (fld : fld_name)
| CAS (v : var) (e1 : expr) (fld : fld_name) (e2 : expr) (e3 : expr)
| Alloc (v : var) (fs: list (fld_name * val))
| Spawn (proc : proc_name) (args : list expr)
.

Definition stmt_append (s1 s2 : stmt) : stmt :=
  Seq s1 s2.


Section state.

Inductive heap_addr :=
| heap_addr_constr:  loc -> fld_name -> heap_addr.

Global Instance heap_addr_eq : EqDecision heap_addr.
Proof. solve_decision. Qed.

Global Declare Instance heap_addr_countable : Countable heap_addr.

(* Heap maps locations to field-value pairs *)
Definition heap := gmap heap_addr val.

(* Stack frame contains local variables and current statement *)



Definition stack_id := Z.

Record stack_frame := StackFrame {
  locals : gmap var val;
  (* curr_stmt : stmt; *)
  (* ret_var : option var; *)
  (* ret_stack := stack_id; *)
}.

Definition stack_map := gmap stack_id stack_frame.

Record proc := Proc {
  proc_name_val : proc_name;
  proc_args : list (var * typ);
  proc_local_vars : list (var * typ);
  proc_stmt : stmt;
}.

(* Global state combines heap and stack *)
Record state := State {
  global_heap : heap;
  (* stack : list stack_frame;  *)
  (* moving stack frames from state to runtime_expr *)
  procs : gmap proc_name proc;
  stack : gmap stack_id stack_frame;
  max_stack_id : Z;
}.

Definition fresh_stk_id (σ : state) := (Z.to_nat (σ.(max_stack_id)) + 1, State σ.(global_heap) σ.(procs) σ.(stack) (1 + σ.(max_stack_id))).

(* Empty state *)
Definition empty_state : state := State ∅ ∅ ∅ 0.

(* Helper functions for state manipulation *)
Definition update_heap (σ : state) (l : loc) (f : fld_name) (v : val) : state :=
  let h := σ.(global_heap) in

  (* let fields := default ∅ (h !! l) in
  let new_fields := <[f := v]> fields in *)
  State (<[heap_addr_constr l f := v]> h) σ.(procs) σ.(stack) σ.(max_stack_id).

(* Definition stack := list stack_frame. *)

Definition lookup_heap (σ : state) (l : loc) (f : fld_name) : option val :=
  σ.(global_heap) !! (heap_addr_constr l f).

  
Definition update_frame_lvar (frame : stack_frame) (x : var) (v : val) : stack_frame :=
  StackFrame (<[x := v]> frame.(locals)) .

Definition update_lvar (σ : state) (x : var) (stk_id : stack_id) (v : val) : state :=
  let s := σ.(stack) in
  let s := 
    match s !! stk_id with
    | None => s
    | Some stk_frm =>
      let new_stk_frame := update_frame_lvar stk_frm x v in
      (<[stk_id := new_stk_frame]> s) 
    end
  in
  State σ.(global_heap) σ.(procs) σ.(stack) σ.(max_stack_id).

Definition lookup_lvar (σ : state) (x : var) (stk_id : stack_id) : option val :=
  match σ.(stack) !! stk_id with
  | Some stk_frame => stk_frame.(locals) !! x
  | None => None
  end.

Definition update_stack (σ : state) (stk_id : stack_id) (frame : stack_frame) :=
  State σ.(global_heap) σ.(procs) (<[stk_id := frame]> σ.(stack)) σ.(max_stack_id).

Definition lookup_proc (σ : state) (pr_name : proc_name) : option proc :=
  σ.(procs) !! pr_name.

(* Substitute formal arguments with actual expressions *)
Fixpoint subst_expr (e : expr) (subst : list (var * expr)) : expr :=
  match e with
  | Var x => match find (λ p, bool_decide (p.1 = x)) subst with
             | Some (_, e') => e'
             | None => Var x
             end
  | Val v => Val v
  | UnOp op e => UnOp op (subst_expr e subst)
  | BinOp op e1 e2 => BinOp op (subst_expr e1 subst) (subst_expr e2 subst)
  | IfE e1 e2 e3 => IfE (subst_expr e1 subst) (subst_expr e2 subst) (subst_expr e3 subst)
  | StuckE => StuckE
  end.


  (* Assuming that local variables of each procedure are disjoint *)
Fixpoint subst_stmt (s : stmt) (subst : list (var * expr)) : stmt :=
  match s with
  | Seq s1 s2 => Seq (subst_stmt s1 subst) (subst_stmt s2 subst)
  (* | Return e => Return (subst_expr e subst) *)
  | IfS e s1 s2 => IfS (subst_expr e subst) (subst_stmt s1 subst) (subst_stmt s2 subst)
  | Assign v e => Assign v (subst_expr e subst)
  (* | Free e => Free (subst_expr e subst) *)
  | SkipS => SkipS
  | StuckS => StuckS
  (* | ExprS e => ExprS (subst_expr e subst) *)
  | Call v proc args => Call v proc (map (λ e, subst_expr e subst) args)
  | FldWr v f e2 => FldWr v f (subst_expr e2 subst)
  | FldRd v e f => FldRd v e f
  | CAS vr e1 f e2 e3 => CAS vr (subst_expr e1 subst) f (subst_expr e2 subst) (subst_expr e3 subst)
  | Alloc v fs => Alloc v fs
  | Spawn proc args => Spawn proc (map (λ e, subst_expr e subst) args)
  end.
End state.

Definition fresh_loc (h : heap) : loc :=
  Loc (Z.of_nat (size h)).

(* Operational Semantics *)
Section semantics.

Inductive runtime_stmt :=
| RTSeq (s1 s2 : runtime_stmt)
| RTIfS (e : expr) (s1 s2 : runtime_stmt) (stk_id : stack_id)
| RTAssign (v : var) (e : expr) (stk_id : stack_id)
(* | RTFree (e : expr) (stk_id : stack_id) *)
| RTSkipS (stk_id : stack_id)
| RTStuckS
| RTVal (v : val)
| RTCall (v : var) (proc : proc_name) (args : list expr) (stk_id : stack_id)
| RTActiveCall (v : var) (s : runtime_stmt) (callee_stk_id : stack_id) (caller_stk_id : stack_id) 
| RTFldWr (v : var) (fld : fld_name) (e : expr) (stk_id : stack_id)
| RTFldRd (v : var) (e : expr) (fld : fld_name) (stk_id : stack_id)
| RTCAS (v : var) (e1 : expr) (fld : fld_name) (e2 : expr) (e3 : expr) (stk_id : stack_id)
| RTAlloc (v : var) (fs : list (fld_name * val)) (stk_id : stack_id)
| RTSpawn (proc : proc_name) (args : list expr) (stk_id : stack_id)
.

Definition of_val v := RTVal v.
Definition to_val (e : runtime_stmt) := match e with
| RTVal v => Some v
| _ => None
end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Inductive ectx_item :=
| SeqCtx (s : runtime_stmt)
| ActiveCallCtx (v : var) (c_id : stack_id) (cr_id : stack_id).

Definition fill_item (Ki : ectx_item) (s : runtime_stmt) : runtime_stmt :=
  match Ki with
  | SeqCtx s1 => RTSeq s s1
  | ActiveCallCtx v c_id cr_id => RTActiveCall v s c_id cr_id
  end.

Fixpoint to_rtstmt (stk_id : stack_id) (s : stmt) :=
match s with
| Seq s1 s2 => RTSeq (to_rtstmt stk_id s1) (to_rtstmt stk_id s2)
(* | Return (e : expr) *)
| IfS e s1 s2 => RTIfS e (to_rtstmt stk_id s1) (to_rtstmt stk_id s2) stk_id
| Assign v e => RTAssign v e stk_id
(* | Free (e : expr) *)
| SkipS => RTSkipS stk_id
| StuckS => RTStuckS (* stuck statement *)
(* | ExprS (e : expr) *)
| Call v proc args => RTCall v proc args stk_id 
| FldWr v fld e => RTFldWr v fld e stk_id
| FldRd v e fld => RTFldRd v e fld stk_id
| CAS v e1 fld e2 e3 => RTCAS v e1 fld e2 e3 stk_id
| Alloc v fs => RTAlloc v fs stk_id
| Spawn proc args => RTSpawn proc args stk_id
end
.

Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NotBoolOp, LitBool b => Some (LitBool (negb b))
  | NegOp, LitInt i => Some (LitInt (-i))
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | AddOp, LitInt i1, LitInt i2 => Some (LitInt (i1 + i2))
  | SubOp, LitInt i1, LitInt i2 => Some (LitInt (i1 - i2))
  | MulOp, LitInt i1, LitInt i2 => Some (LitInt (i1 * i2))
  | DivOp, LitInt i1, LitInt i2 => 
      if (i2 =? 0)%Z then None else Some (LitInt (i1 / i2))
  | ModOp, LitInt i1, LitInt i2 =>
      if (i2 =? 0)%Z then None else Some (LitInt (i1 mod i2))
  | EqOp, v1, v2 => Some (LitBool (bool_decide (v1 = v2)))
  | NeOp, v1, v2 => Some (LitBool (bool_decide (v1 ≠ v2)))
  | LtOp, LitInt i1, LitInt i2 => Some (LitBool (Z.ltb i1 i2))
  | GtOp, LitInt i1, LitInt i2 => Some (LitBool (Z.ltb i2 i1))
  | LeOp, LitInt i1, LitInt i2 => Some (LitBool (Z.leb i1 i2))
  | GeOp, LitInt i1, LitInt i2 => Some (LitBool (Z.leb i2 i1))
  | AndOp, LitBool b1, LitBool b2 => Some (LitBool (b1 && b2))
  | OrOp, LitBool b1, LitBool b2 => Some (LitBool (b1 || b2))
  | _, _, _ => None
  end.

(* Expression evaluation *)
Inductive expr_step : expr → stack_frame → expr → Prop :=
| ExprRefl e stk_frame :
  expr_step e stk_frame e
| VarStep stk_frame x v :
    stk_frame.(locals) !! x = Some v ->
    expr_step (Var x) stk_frame ((Val v))
| UnOpStep stk_frame op e v v' :
    expr_step e stk_frame (Val v) ->
    un_op_eval op v = Some v' ->
    expr_step (UnOp op e) stk_frame ((Val v'))
| BinOpStep stk_frame op e1 e2 v1 v2 v :
    expr_step e1 stk_frame (Val v1) ->
    expr_step e2 stk_frame (Val v2) ->
    bin_op_eval op v1 v2 = Some v ->
    expr_step (BinOp op e1 e2) stk_frame ((Val v))
| IfETrueStep stk_frame v e1 e2 :
    v = (LitBool true) ->
    expr_step (IfE (Val v) e1 e2) stk_frame (e1)
| IfEFalseStep stk_frame v e1 e2 :
    v = (LitBool false) ->
    expr_step (IfE (Val v) e1 e2) stk_frame (e2).

Inductive runtime_step : runtime_stmt → state → list Empty_set → runtime_stmt → state → list runtime_stmt → Prop :=
| RTIfSStep σ stk_id stk_frm e s1 s2 b :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitBool b)) ->
  runtime_step (RTIfS e s1 s2 stk_id) σ [] (if b then s1 else s2) σ []

| RTAssignStep σ stk_id stk_frm var e v :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val v) ->
  let σ' := update_lvar σ var  stk_id v in
  runtime_step (RTAssign var e stk_id) σ [] (RTVal LitUnit) σ' []

| RTSkipStep σ stk_id :
  runtime_step (RTSkipS stk_id) σ [] (RTVal LitUnit) σ []

| RTCallStep σ stk_id stk_frm v proc args arg_vals procedure :
  σ.(stack) !! stk_id = Some stk_frm ->
  σ.(procs) !! proc = Some procedure ->
  length procedure.(proc_args) = length args ->
  Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
  let (new_stk_id, σ') := fresh_stk_id σ in
  let new_stk_frame := StackFrame 
      (list_to_map (zip (map fst procedure.(proc_args)) arg_vals))
    in
  let σ'' := update_stack σ' new_stk_id new_stk_frame in
  let new_stmt := to_rtstmt new_stk_id procedure.(proc_stmt) in
  runtime_step (RTCall v proc args stk_id) σ [] 
  (RTActiveCall v new_stmt new_stk_id stk_id) σ'' []

| FldWrStep σ stk_id stk_frm v fld e l val:
  σ.(stack) !! stk_id = Some stk_frm ->
  stk_frm.(locals) !! v = Some (LitLoc l) ->
  expr_step e stk_frm (Val val) ->
  let σ' := update_heap σ l fld val in
  runtime_step (RTFldWr v fld e stk_id) σ [] (RTVal LitUnit) σ' []

| FldRdStep σ stk_id stk_frm v e fld l v2 :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitLoc l)) ->
  lookup_heap σ l fld = Some v2 ->
  let σ' := update_lvar σ v stk_id v2 in
  runtime_step (RTFldRd v e fld stk_id) σ [] (RTVal LitUnit) σ' []

| CASSuccStep σ stk_id stk_frm v e1 fld e2 e3 l v2 v3 :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e1 stk_frm (Val (LitLoc l)) ->
  expr_step e2 stk_frm (Val v2) ->
  expr_step e3 stk_frm (Val v3) ->
  lookup_heap σ l fld = Some v2 ->
  let σ' := update_heap σ l fld v3 in
  let σ'' := update_lvar σ' v stk_id (LitBool true) in
  runtime_step (RTCAS v e1 fld e2 e3 stk_id) σ [] (RTVal LitUnit) σ'' []

| CASFailStep σ stk_id stk_frm v e1 fld e2 e3 l v0 v2 :
  σ.(stack) !! stk_id = Some stk_frm ->expr_step e1 stk_frm (Val (LitLoc l)) ->
  expr_step e2 stk_frm (Val v2) ->
  lookup_heap σ l fld = Some v0 ->
  not (v0 = v2) ->
  let σ' := update_lvar σ v stk_id (LitBool false) in
  runtime_step (RTCAS v e1 fld e2 e3 stk_id) σ [] (RTVal LitUnit) σ' []

| AllocStep σ stk_id v fs :
  let l := fresh_loc σ.(global_heap) in
  let σ' := (foldr (fun f_v acc => update_heap acc l (fst f_v) (snd f_v)) σ fs) in
  let σ'' := update_lvar σ' v stk_id (LitLoc l) in
  runtime_step (RTAlloc v fs stk_id) σ [] (RTVal LitUnit) σ'' []

| SpawnStep σ stk_id stk_frm proc args arg_vals procedure :
  σ.(stack) !! stk_id = Some stk_frm ->
  σ.(procs) !! proc = Some procedure ->
  length procedure.(proc_args) = length args ->
  Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
  let (new_stk_id, σ') := fresh_stk_id σ in
  let new_stk_frame := StackFrame 
      (list_to_map (zip (map fst procedure.(proc_args)) arg_vals))
  in
  let new_stmt := to_rtstmt new_stk_id procedure.(proc_stmt) in
  let σ'' := update_stack σ' new_stk_id new_stk_frame in
  runtime_step (RTSpawn proc args stk_id) σ [] (RTVal LitUnit) σ'' [new_stmt]

| ActiveCallStep σ callee_stk_id caller_stk_id var value callee_stack ret_val:
  σ.(stack) !! callee_stk_id = Some callee_stack ->
  callee_stack.(locals) !! "#ret_val" = Some ret_val ->
  let σ' := update_lvar σ var caller_stk_id ret_val in
  runtime_step (RTActiveCall var (RTVal value) callee_stk_id caller_stk_id) σ []
  (RTVal LitUnit) σ' []

| SeqStep σ v s2:
  runtime_step (RTSeq (RTVal v) s2) σ [] s2 σ []

  .

End semantics.

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_base_stuck e1 σ1 κ e2 σ2 efs : runtime_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma base_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  runtime_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki1, Ki2; naive_solver eauto with f_equal. Qed.

Lemma simp_lang_mixin : EctxiLanguageMixin of_val to_val fill_item runtime_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_base_stuck,
    fill_item_val, fill_item_no_val_inj, base_ctx_step_val.
Qed.

Canonical Structure simp_ectxi_lang := EctxiLanguage simp_lang_mixin.
Canonical Structure simp_ectx_lang := EctxLanguageOfEctxi simp_ectxi_lang.
Canonical Structure simp_lang := LanguageOfEctx simp_ectx_lang.

(* Check (@step simp_lang).

Eval compute in cfg simp_lang. *)

Canonical Structure valO := leibnizO val.
Canonical Structure stack_frameO := leibnizO stack_frame.

Lemma expr_step_val_unique e stk_frm v v0:
  expr_step e stk_frm (Val v) ->
  expr_step e stk_frm (Val v0) ->
  v = v0.
Proof. 
  Admitted.


Lemma Forall2_expr_step_val_unique :
  ∀ args stk_frm vals1 vals2,
  Forall2 (λ e v, expr_step e stk_frm (Val v)) args vals1 →
  Forall2 (λ e v, expr_step e stk_frm (Val v)) args vals2 →
  vals1 = vals2.
Proof.
  induction args; intros stk_frm vals1 vals2 H1 H2.
  - inversion H1; inversion H2; reflexivity.
  - inversion H1; inversion H2; subst.
    f_equal.
    + eapply expr_step_val_unique; eauto.
    + eapply IHargs; eauto.
Qed.

