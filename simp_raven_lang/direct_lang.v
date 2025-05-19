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
| TpInt | TpLoc | TpBool.

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
| Return (e : expr)
| IfS (e : expr) (s1 s2 : stmt) (s : stmt)
| Assign (v : var) (e : expr) (s : stmt)
(* | Free (e : expr) (s : stmt) *)
| SkipS (s : stmt)
| StuckS (* stuck statement *)
(* | ExprS (e : expr) (s : stmt) *)
| Call (v : var) (proc : proc_name) (args : list expr) (s : stmt)
| FldWr (e1 : expr) (fld : fld_name) (e2 : expr) (s : stmt) 
| FldRd (v : var) (e : expr) (fld : fld_name) (s : stmt)
| CAS (v : var)(e1 : expr) (fld : fld_name) (e2 : expr) (e3 : expr) (s : stmt)
| Alloc (v : var) (fs: list (fld_name * val)) (s : stmt)
| Spawn (proc : proc_name) (args : list expr) (s : stmt)
| Term
.

Fixpoint stmt_append (s1 s2 : stmt) : stmt :=
  match s1 with
  | Return e => Return e
  | IfS e s1 s2 s => IfS e s1 s2 (stmt_append s s2)
  | Assign v e s => Assign v e (stmt_append s s2)
  (* | Free e s => Free e (stmt_append s s2) *)
  | SkipS s => (stmt_append s s2)
  | StuckS => StuckS
  (* | ExprS e s => ExprS e (stmt_append s s2) *)
  | Call v proc args s => Call v proc args (stmt_append s s2)
  | FldWr e1 f e2 s => FldWr e1 f e2 (stmt_append s s2)
  | FldRd e1 e2 f s => FldRd e1 e2 f (stmt_append s s2)
  | CAS vr e1 f e2 e3 s => CAS vr e1 f e2 e3 (stmt_append s s2)
  | Alloc e fs s => Alloc e fs (stmt_append s s2)
  | Spawn proc args s => Spawn proc args (stmt_append s s2)
  | Term => s2
  end.

Section state.

(* Heap maps locations to field-value pairs *)
Definition heap := gmap loc (gmap fld_name val).

Definition stack_id := Z.

(* Stack frame contains local variables and current statement *)
Record stack_frame := StackFrame {
  locals : gmap var val;
  curr_stmt : stmt;
  ret_var : var;
  ret_stack : stack_id;
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
  let fields := default ∅ (h !! l) in
  let new_fields := <[f := v]> fields in
  State (<[l := new_fields]> h) σ.(procs) σ.(stack) σ.(max_stack_id).

(* Definition stack := list stack_frame. *)

Definition lookup_heap (σ : state) (l : loc) (f : fld_name) : option val :=
  σ.(global_heap) !! l ≫= (λ fields, fields !! f).



  
Definition update_frame_lvar (frame : stack_frame) (x : var) (v : val) : stack_frame :=
  StackFrame (<[x := v]> frame.(locals)) frame.(curr_stmt) frame.(ret_var) frame.(ret_stack).

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

(* Definition pop_frame (s : stack) : option (stack * stack_frame) :=
  match s with
  | nil => None
  | frame :: rest => Some (rest, frame)
  end. *)

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
  | Return e => Return (subst_expr e subst)
  | IfS e s1 s2 s => IfS (subst_expr e subst) (subst_stmt s1 subst) (subst_stmt s2 subst) (subst_stmt s subst)
  | Assign v e s => Assign v (subst_expr e subst) (subst_stmt s subst)
  (* | Free e s => Free (subst_expr e subst) (subst_stmt s subst) *)
  | SkipS s => SkipS (subst_stmt s subst)
  | StuckS => StuckS
  (* | ExprS e s => ExprS (subst_expr e subst) (subst_stmt s subst) *)
  | Call v proc args s => Call v proc (map (λ e, subst_expr e subst) args) (subst_stmt s subst)
  | FldWr e1 f e2 s => FldWr (subst_expr e1 subst) f (subst_expr e2 subst) (subst_stmt s subst)
  | FldRd v e f s => FldRd v e f (subst_stmt s subst)
  | CAS vr e1 f e2 e3 s => CAS vr (subst_expr e1 subst) f (subst_expr e2 subst) (subst_expr e3 subst) (subst_stmt s subst)
  | Alloc v fs s => Alloc v fs (subst_stmt s subst)
  | Spawn proc args s => Spawn proc (map (λ e, subst_expr e subst) args) (subst_stmt s subst)
  | Term => Term
  end.
End state.

Definition fresh_loc (h : heap) : loc :=
  Loc (Z.of_nat (size h)).

(* Operational Semantics *)
Section semantics.

Inductive runtime_expr :=
| ValS (v: val)
| Stmt (s : stmt) (stk_id : stack_id).

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
Inductive expr_step : expr → state → stack_id → expr → Prop :=
| VarStep σ stk_id x v frame :
    (σ.(stack)) !! stk_id = Some frame ->
    frame.(locals) !! x = Some v ->
    expr_step (Var x) σ stk_id ((Val v))
| UnOpStep σ stk_id op e v v' :
    expr_step e σ stk_id (Val v) ->
    un_op_eval op v = Some v' ->
    expr_step (UnOp op e) σ stk_id ((Val v'))
| BinOpStep σ stk_id op e1 e2 v1 v2 v :
    expr_step e1 σ stk_id (Val v1) ->
    expr_step e2 σ stk_id (Val v2) ->
    bin_op_eval op v1 v2 = Some v ->
    expr_step (BinOp op e1 e2) σ stk_id ((Val v))
| IfETrueStep σ stk_id v e1 e2 :
    v = (LitBool true) ->
    expr_step (IfE (Val v) e1 e2) σ stk_id (e1)
| IfEFalseStep σ stk_id v e1 e2 :
    v = (LitBool false) ->
    expr_step (IfE (Val v) e1 e2) σ stk_id (e2).

End semantics.

Inductive prim_step : runtime_expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop := 
| ReturnS σ stk_id e v s callee_stk_frm caller_stk_frm :
  expr_step e σ stk_id (Val v) ->
  σ.(stack) !! stk_id = Some callee_stk_frm ->
  σ.(stack) !! callee_stk_frm.(ret_stack) = Some caller_stk_frm ->
  s = callee_stk_frm.(curr_stmt) ->
  let σ' := update_lvar σ caller_stk_frm.(ret_var) callee_stk_frm.(ret_stack) v in
  
  prim_step (Stmt (Return e) stk_id) σ [] (Stmt s callee_stk_frm.(ret_stack)) σ' []

| ReturnTerminal σ stk_id e v callee_stk_frm :
  expr_step e σ stk_id (Val v) ->
  σ.(stack) !! stk_id = Some callee_stk_frm ->
  σ.(stack) !! callee_stk_frm.(ret_stack) = None ->
  prim_step (Stmt (Return e) stk_id) σ [] (ValS v) σ []

| IfStep σ stk_id e s1 s2 s b :
  expr_step e σ stk_id (Val (LitBool b)) ->
  let s' := stmt_append (if b then s1 else s2) s in
  prim_step (Stmt (IfS e s1 s2 s) stk_id) σ [] (Stmt s' stk_id) σ []

| AssignStep σ stk_id var e s v :
  expr_step e σ stk_id (Val v) ->
  let σ' := update_lvar σ var  stk_id v in

  prim_step (Stmt (Assign var e s) stk_id) σ [] (Stmt s stk_id) σ' []

| SkipStep σ stk_id s:
  prim_step (Stmt (SkipS s) stk_id) σ [] (Stmt s stk_id) σ []

| CallStep σ stk_id v proc args arg_vals s procedure:
  σ.(procs) !! proc = Some procedure ->
  length procedure.(proc_args) = length args ->
  Forall2 (fun expr val => expr_step expr σ stk_id (Val val)) args arg_vals ->
  let (new_stk_id, σ') := fresh_stk_id σ in
  let new_stk_frame := StackFrame 
      (list_to_map (zip (map fst procedure.(proc_args)) arg_vals))
      s
      v
      stk_id
    in
  let σ'' := update_stack σ' new_stk_id new_stk_frame in
  prim_step (Stmt (Call v proc args s) stk_id) σ [] (Stmt procedure.(proc_stmt) new_stk_id) σ'' []

| FldWrStep σ stk_id e1 fld e2 s l v:
  expr_step e1 σ stk_id (Val (LitLoc l)) ->
  expr_step e2 σ stk_id (Val v) ->
  let σ' := update_heap σ l fld v in
  prim_step (Stmt (FldWr e1 fld e2 s) stk_id) σ [] (Stmt s stk_id) σ' []


| FldRdStep σ stk_id v e fld s l v2 :
  expr_step e σ stk_id (Val (LitLoc l)) ->
  lookup_heap σ l fld = Some v2 ->
  let σ' := update_lvar σ v stk_id v2 in
  prim_step (Stmt (FldRd v e fld s) stk_id) σ [] (Stmt s stk_id) σ' []

| CASSuccStep σ stk_id v e1 fld e2 e3 s l v2 v3 :
  expr_step e1 σ stk_id (Val (LitLoc l)) ->
  expr_step e2 σ stk_id (Val v2) ->
  expr_step e3 σ stk_id (Val v3) ->
  lookup_heap σ l fld = Some v2 ->
  let σ' := update_heap σ l fld v3 in
  let σ'' := update_lvar σ' v stk_id (LitBool true) in
  prim_step (Stmt (CAS v e1 fld e2 e3 s) stk_id) σ [] (Stmt s stk_id) σ'' []

| CASFailStep σ stk_id v e1 fld e2 e3 s l v0 v2 v3 :
  expr_step e1 σ stk_id (Val (LitLoc l)) ->
  expr_step e2 σ stk_id (Val v2) ->
  expr_step e3 σ stk_id (Val v3) ->
  lookup_heap σ l fld = Some v0 ->
  not (v0 = v2) ->
  let σ' := update_lvar σ v stk_id (LitBool false) in
  prim_step (Stmt (CAS v e1 fld e2 e3 s) stk_id) σ [] (Stmt s stk_id) σ' []

| AllocStep σ stk_id v fs s :
  let l := fresh_loc σ.(global_heap) in
  let σ' := (fold_left (fun acc (f_v : fld_name * val) => update_heap acc l (fst f_v) (snd f_v)) fs σ) in
  let σ'' := update_lvar σ v stk_id (LitLoc l) in
  prim_step (Stmt (Alloc v fs s) stk_id) σ [] (Stmt s stk_id) σ'' []

| SpawnStep σ stk_id v proc args arg_vals s procedure :
  σ.(procs) !! proc = Some procedure ->
  length procedure.(proc_args) = length args ->
  Forall2 (fun expr val => expr_step expr σ stk_id (Val val)) args arg_vals ->
  let (new_stk_id, σ') := fresh_stk_id σ in
  let new_stk_frame := StackFrame 
      (list_to_map (zip (map fst procedure.(proc_args)) arg_vals))
      s
      v
      stk_id
    in
  let σ'' := update_stack σ' new_stk_id new_stk_frame in
  prim_step (Stmt (Spawn proc args s) stk_id) σ [] (Stmt s stk_id) σ'' [(Stmt procedure.(proc_stmt) new_stk_id)]
  .

Definition of_val v := ValS v.
Definition to_val s := match s with 
  | ValS v => Some v
  | _ => None
end.

Lemma of_to_val (s : runtime_expr) v : to_val s = Some v → s = (ValS v).
Proof. case: s => // -[]//. naive_solver. 
all: intros; naive_solver. 
Qed.

Lemma to_of_val (s : runtime_expr) v : to_val s = Some v -> (ValS v) = s.
Proof. case: s => // -[]//; naive_solver.
Qed.

Lemma val_stuck s σ κ s' σ' efs :
  prim_step s σ κ s' σ' efs → to_val s = None.
Proof.
  destruct 1; naive_solver.
Qed.

Definition simp_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split; eauto using of_to_val, to_of_val, val_stuck.
Qed.

Canonical Structure simp_lang : language := Language simp_lang_mixin.

Canonical Structure valO := leibnizO val.
Canonical Structure stack_frameO := leibnizO stack_frame.