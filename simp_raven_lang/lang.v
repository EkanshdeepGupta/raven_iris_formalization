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
(* | Alloc (e : expr) (fs: list string) *)
(* | Tuple (es : list expr)
| TupleLookUp (e : expr) (ind : Z) *)
(* | SkipE (e : expr) *)
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
| Free (e : expr) (s : stmt)
| SkipS
| StuckS (* stuck statement *)
| ExprS (e : expr) (s : stmt)
| Call (v : option var) (proc : proc_name) (args : list expr) (s : stmt)
| FldWr (e1 : expr) (fld : fld_name) (e2 : expr) (s : stmt) 
| FldRd (v : var) (e : expr) (fld : fld_name) (s : stmt)
| CAS (v : var)(e1 : expr) (fld : fld_name) (e2 : expr) (e3 : expr) (s : stmt)
| Alloc (e : expr) (fs: list (fld_name * val)) (s : stmt)
| Spawn (proc : proc_name) (args : list expr) (s : stmt)
.

Fixpoint stmt_append (s1 s2 : stmt) : stmt :=
  match s1 with
  | Return e => Return e
  | IfS e s1 s2 s => IfS e s1 s2 (stmt_append s s2)
  | Assign v e s => Assign v e (stmt_append s s2)
  | Free e s => Free e (stmt_append s s2)
  | SkipS => s2
  | StuckS => StuckS
  | ExprS e s => ExprS e (stmt_append s s2)
  | Call v proc args s => Call v proc args (stmt_append s s2)
  | FldWr e1 f e2 s => FldWr e1 f e2 (stmt_append s s2)
  | FldRd e1 e2 f s => FldRd e1 e2 f (stmt_append s s2)
  | CAS vr e1 f e2 e3 s => CAS vr e1 f e2 e3 (stmt_append s s2)
  | Alloc e fs s => Alloc e fs (stmt_append s s2)
  | Spawn proc args s => Spawn proc args (stmt_append s s2)
  end.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.
(* State Model *)
Section state.

(* Heap maps locations to field-value pairs *)
Definition heap := gmap loc (gmap fld_name val).

(* Stack frame contains local variables and current statement *)
Record stack_frame := StackFrame {
  locals : gmap var val;
  curr_stmt : stmt;
  ret_var : option var;
}.

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
}.

(* Empty state *)
Definition empty_state : state := State ∅ ∅.

(* Helper functions for state manipulation *)
Definition update_heap (σ : state) (l : loc) (f : fld_name) (v : val) : state :=
  let h := σ.(global_heap) in
  let fields := default ∅ (h !! l) in
  let new_fields := <[f := v]> fields in
  State (<[l := new_fields]> h) σ.(procs).

Definition stack := list stack_frame.

Definition lookup_heap (σ : state) (l : loc) (f : fld_name) : option val :=
  σ.(global_heap) !! l ≫= (λ fields, fields !! f).



  
Definition update_frame_lvar (frame : stack_frame) (x : var) (v : val) : stack_frame :=
  StackFrame (<[x := v]> frame.(locals)) frame.(curr_stmt) frame.(ret_var).

Definition update_lvar (s : stack) (x : var) (v : val) : stack :=
  match s with
  | [] => []
  | frame :: rest => update_frame_lvar frame x v :: rest
  end.

Definition lookup_lvar (s : stack) (x : var) : option val :=
  match s with
  | [] => None
  | frame :: _ => frame.(locals) !! x
  end.

Definition pop_frame (s : stack) : option (stack * stack_frame) :=
  match s with
  | nil => None
  | frame :: rest => Some (rest, frame)
  end.

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
  | Free e s => Free (subst_expr e subst) (subst_stmt s subst)
  | SkipS => SkipS
  | StuckS => StuckS
  | ExprS e s => ExprS (subst_expr e subst) (subst_stmt s subst)
  | Call v proc args s => Call v proc (map (λ e, subst_expr e subst) args) (subst_stmt s subst)
  | FldWr e1 f e2 s => FldWr (subst_expr e1 subst) f (subst_expr e2 subst) (subst_stmt s subst)
  | FldRd v e f s => FldRd v e f (subst_stmt s subst)
  | CAS vr e1 f e2 e3 s => CAS vr (subst_expr e1 subst) f (subst_expr e2 subst) (subst_expr e3 subst) (subst_stmt s subst)
  | Alloc e fs s => Alloc (subst_expr e subst) fs (subst_stmt s subst)
  | Spawn proc args s => Spawn proc (map (λ e, subst_expr e subst) args) (subst_stmt s subst)
  end.
End state.

Definition fresh_loc (h : heap) : loc :=
  Loc (Z.of_nat (size h)).

(* Operational Semantics *)
Section semantics.

Inductive runtime_expr :=
| Expr (e : rtexpr) (stack : stack)
| Stmt (s : rtstmt) (stack : stack)
with rtexpr :=
| RTVar (x : var)
| RTVal (v : val)
| RTUnOp (op : un_op) (e : rtexpr)
| RTBinOp (op : bin_op) (e1 e2 : rtexpr)
| RTIfE (e1 e2 e3 : rtexpr)
| RTStuckE
with rtstmt :=
| RTReturn (e : rtexpr)
| RTIfS (e : rtexpr) (s1 : rtstmt) (s2 : rtstmt) (s : rtstmt)
| RTAssign (v : var) (e : rtexpr) (s : rtstmt)
| RTFree (e : rtexpr) (s : rtstmt)
| RTStuckS
| RTExprS (e : rtexpr) (s : rtstmt)
| RTCall (v : option var) (proc : proc_name) (args : list rtexpr) (s : rtstmt)
| RTFldWr (e1 : rtexpr) (fld : fld_name) (e2 : rtexpr) (s : rtstmt)
| RTFldRd (v : var) (e : rtexpr) (fld : fld_name) (s : rtstmt)
| RTCAS (vr : var) (e1 : rtexpr) (fld : fld_name) (e2 : rtexpr) (e3 : rtexpr) (s : rtstmt)
| RTAlloc (e : rtexpr) (fs: list (fld_name * val)) (s : rtstmt)
| RTSpawn (proc : proc_name) (args : list rtexpr) (s : rtstmt).

Fixpoint to_rtexpr (e : expr) : rtexpr :=
  match e with
  | Var x => RTVar x
  | Val v => RTVal v
  | UnOp op e => RTUnOp op (to_rtexpr e)
  | BinOp op e1 e2 => RTBinOp op (to_rtexpr e1) (to_rtexpr e2)
  | IfE e1 e2 e3 => RTIfE (to_rtexpr e1) (to_rtexpr e2) (to_rtexpr e3)
  | StuckE => RTStuckE
  end.

Definition coerce_rtexpr := to_rtexpr.
Coercion coerce_rtexpr : expr >-> rtexpr.

Fixpoint to_rtstmt (s : stmt) : rtstmt :=
  match s with
  | Return e => RTReturn (to_rtexpr e)
  | IfS e s1 s2 s => RTIfS (to_rtexpr e) (to_rtstmt s1) (to_rtstmt s2) (to_rtstmt s)
  | Assign v e s => RTAssign v (to_rtexpr e) (to_rtstmt s)
  | Free e s => RTFree (to_rtexpr e) (to_rtstmt s)
  | SkipS => RTStuckS
  | StuckS => RTStuckS
  | ExprS e s => RTExprS (to_rtexpr e) (to_rtstmt s)
  | Call v proc args s => RTCall v proc (map to_rtexpr args) (to_rtstmt s)
  | FldWr e1 f e2 s => RTFldWr (to_rtexpr e1) f (to_rtexpr e2) (to_rtstmt s)
  | FldRd v e f s => RTFldRd v (to_rtexpr e) f (to_rtstmt s)
  | CAS vr e1 f e2 e3 s => RTCAS vr (to_rtexpr e1) f (to_rtexpr e2) (to_rtexpr e3) (to_rtstmt s)
  | Alloc e fs s => RTAlloc (to_rtexpr e) fs (to_rtstmt s)
  | Spawn proc args s => RTSpawn proc (map to_rtexpr args) (to_rtstmt s)
  end.

Definition coerce_rtstmt := to_rtstmt.
Coercion coerce_rtstmt : stmt >-> rtstmt.

Definition expr_to_runtime_expr (e : expr) (stk : stack): runtime_expr :=
  Expr (to_rtexpr e) stk.

Definition stmt_to_runtime_stmt (s : stmt) (stk : stack): runtime_expr :=
  Stmt (to_rtstmt s) stk.

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
Inductive expr_step : expr → state → stack → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| VarStep σ stk x v frame :
    stk !! 0 = Some frame ->
    frame.(locals) !! x = Some v ->
    expr_step (Var x) σ stk [] (expr_to_runtime_expr (Val v) stk) σ []
| ValStep σ stk v :
    expr_step (Val v) σ stk [] (expr_to_runtime_expr (Val v) stk) σ []
| UnOpStep σ stk op v v' :
    un_op_eval op v = Some v' ->
    expr_step (UnOp op (Val v)) σ stk [] (expr_to_runtime_expr (Val v') stk) σ []
| BinOpStep σ stk op v1 v2 v :
    bin_op_eval op v1 v2 = Some v ->
    expr_step (BinOp op (Val v1) (Val v2)) σ stk [] (expr_to_runtime_expr (Val v) stk) σ []
| IfETrueStep σ stk v e1 e2 :
    v = (LitBool true) ->
    expr_step (IfE (Val v) e1 e2) σ stk [] (expr_to_runtime_expr e1 stk) σ []
| IfEFalseStep σ stk v e1 e2 :
    v = (LitBool false) ->
    expr_step (IfE (Val v) e1 e2) σ stk [] (expr_to_runtime_expr e2 stk) σ []
| StuckStep σ stk:
    expr_step StuckE σ stk [] (stmt_to_runtime_stmt StuckS stk) σ [].

(* Statement execution *)
Inductive stmt_step : stmt → state → stack -> list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| ReturnStep σ stk e v s :
    expr_step e σ stk [] (expr_to_runtime_expr (Val v) stk) σ [] ->
    match stk with
    | [] | _ :: [] => s = SkipS
    | frame :: rest_hd :: rest_tl => s = rest_hd.(curr_stmt)
    end ->
    let stk' := match stk with
    | []  | _ :: [] => []
    | frame :: rest_hd :: rest_tl => 
      match frame.(ret_var) with
      | Some ret_var => update_frame_lvar rest_hd ret_var v :: rest_tl
      | None => rest_hd :: rest_tl
      end
    end in
    stmt_step (Return e) σ stk [] (stmt_to_runtime_stmt s stk') σ []
| IfTrueStep σ stk e s1 s2 s :
    expr_step e σ stk [] (expr_to_runtime_expr (Val (LitBool true)) stk) σ [] ->
    stmt_step (IfS e s1 s2 s) σ stk [] (stmt_to_runtime_stmt s1 stk) σ []
| IfFalseStep σ stk e s1 s2 s :
    expr_step e σ stk [] (expr_to_runtime_expr (Val (LitBool false)) stk) σ [] ->
    stmt_step (IfS e s1 s2 s) σ stk [] (stmt_to_runtime_stmt s2 stk) σ []
| AssignStep σ stk var e2 s v :
    expr_step e2 σ stk [] (expr_to_runtime_expr (Val v) stk) σ [] ->
    stmt_step (Assign var e2 s) σ stk [] (stmt_to_runtime_stmt s (update_lvar stk var v)) σ []
| FreeStep σ stk e s l :
    expr_step e σ stk [] (expr_to_runtime_expr (Val (LitLoc l)) stk) σ [] ->
    stmt_step (Free e s) σ stk [] (stmt_to_runtime_stmt s stk)
             {| global_heap := delete l σ.(global_heap);
                procs := σ.(procs);
              |} 
             []
| SkipStep σ stk :
    stmt_step SkipS σ stk [] (stmt_to_runtime_stmt SkipS stk) σ []
| ExprStep σ stk e s v :
    expr_step e σ stk [] (expr_to_runtime_expr (Val v) stk) σ [] ->
    stmt_step (ExprS e s) σ stk [] (stmt_to_runtime_stmt SkipS stk) σ []
| CallStep σ stk opt_ret proc args s procedure :
    σ.(procs) !! proc = Some procedure ->
    length procedure.(proc_args) = length args ->
    
    let subst_body := subst_stmt procedure.(proc_stmt) (zip (map fst procedure.(proc_args)) args) in
    let stk' := match stk with
    | [] => []
    | frame :: rest => {| locals := frame.(locals);
                          curr_stmt := s;
                          ret_var := frame.(ret_var) |} :: rest
    end in

    stmt_step (Call opt_ret proc args s) σ stk []
              (stmt_to_runtime_stmt subst_body (StackFrame ∅ SkipS opt_ret :: stk')) σ []
| SpawnStep σ stk proc args s procedure :
    σ.(procs) !! proc = Some procedure ->
    let subst_body := subst_stmt procedure.(proc_stmt) (zip (map fst procedure.(proc_args)) args) in
    let new_stk := [StackFrame ∅ SkipS None] in
    stmt_step (Spawn proc args  s) σ stk [] (stmt_to_runtime_stmt SkipS stk) σ [stmt_to_runtime_stmt subst_body new_stk]
| FldWrStep σ stk e1 f e2 s l v :
    expr_step e1 σ stk [] (expr_to_runtime_expr (Val (LitLoc l)) stk) σ [] ->
    expr_step e2 σ stk [] (expr_to_runtime_expr (Val v) stk) σ [] ->
    stmt_step (FldWr e1 f e2 s) σ stk [] (stmt_to_runtime_stmt s stk) (update_heap σ l f v) []
| FldRdStep σ stk e1 e2 f s l v vr :
    e1 = (Var vr) ->
    expr_step e2 σ stk [] (expr_to_runtime_expr (Val (LitLoc l)) stk) σ [] ->
    lookup_heap σ l f = Some v ->
    stmt_step (FldRd vr e2 f s) σ stk [] (stmt_to_runtime_stmt s (update_lvar stk vr v)) σ []
| AllocStep σ stk e fs s vr :
    e = (Var vr) ->
    let l := fresh_loc σ.(global_heap) in
    stmt_step (Alloc e fs s) σ stk [] (stmt_to_runtime_stmt s (update_lvar stk vr (LitLoc l))) 
    (fold_left (fun acc (f_v : fld_name * val) => update_heap acc l (fst f_v) (snd f_v)) fs σ)
    []
| CASSucc σ stk vr e1 f e2 e3 s v2 v3 l:
    expr_step e1 σ stk [] (expr_to_runtime_expr (Val (LitLoc l)) stk) σ [] ->
    e2 = (Val v2) ->
    e3 = (Val v3) ->
    lookup_heap σ l f = Some v2 ->
    stmt_step (CAS vr e1 f e2 e3 s) σ stk [] (stmt_to_runtime_stmt s (update_lvar stk vr (LitBool true))) (update_heap σ l f v3) []
| CASFail σ stk vr e1 f e2 e3 s v1 v2 v3 l:
    expr_step e1 σ stk [] (expr_to_runtime_expr (Val (LitLoc l)) stk) σ [] ->
    e2 = (Val v2) ->
    e3 = (Val v3) ->
    lookup_heap σ l f = Some v1 ->
    bool_decide (v1 = v2) = false ->
    stmt_step (CAS vr e1 f e2 e3 s) σ stk [] (stmt_to_runtime_stmt s (update_lvar stk vr (LitBool false))) σ [].

Inductive runtime_step : runtime_expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| RTExprStep σ e stk v :
    expr_step e σ stk [] (expr_to_runtime_expr (Val v) stk) σ [] ->
    runtime_step (Expr e stk) σ [] (Expr (Val v) stk) σ []
| RTStmtStep σ s stk stk':
    stmt_step s σ stk [] (Stmt s stk') σ [] ->
    runtime_step (Stmt s stk) σ [] (Stmt s stk') σ []
.

End semantics.

Inductive expr_ectx :=
| UnOpCtx (op : un_op)
| BinOpLCtx (op : bin_op) (e2 : rtexpr)
| BinOpRCtx (op : bin_op) (v1 : val)
| IfECtx (e2 : rtexpr) (e3 : rtexpr)
.

Definition expr_fill_item (Ki : expr_ectx) (e : rtexpr) : rtexpr :=
  match Ki with
  | UnOpCtx op => RTUnOp op e
  | BinOpLCtx op e2 => RTBinOp op e e2
  | BinOpRCtx op v1 => RTBinOp op (RTVal v1) e
  | IfECtx e2 e3 => RTIfE e e2 e3
  end.

Inductive stmt_ectx :=
| ReturnCtx
| IfSCtx (s1 s2 s : stmt)
| AssignCtx (v : var) (s : stmt)
| FreeCtx (s : stmt)
| ExprSCtx (s : stmt)
| FldWrLCtx (f : fld_name) (v : val) (s : stmt)
| FldWrRCtx (e : rtexpr) (f : fld_name) (s : stmt)
| FldRdCtx (v : var) (e : rtexpr) (f : fld_name) (s : stmt)
| CASLCtx (v : var) (e1 : rtexpr) (fld : fld_name) (e2 : rtexpr) (s : stmt)
| CASMCtx (v : var) (e1 : rtexpr) (fld : fld_name) (v3 : val) (s : stmt)
| CASRCtx (v : var) (fld : fld_name) (v2 : val) (v3 : val) (s : stmt)
| AllocCtx (fs : list (fld_name * val)) (s : stmt)
| SpawnCtx (proc : proc_name) (args : list rtexpr) (s : stmt)
.

Definition stmt_fill_item (Ki : stmt_ectx) (e : rtexpr) : rtstmt :=
  match Ki with
  | ReturnCtx => RTReturn e
  | IfSCtx s1 s2 s => RTIfS e s1 s2 s
  | AssignCtx v s => RTAssign v e s
  | FreeCtx s => RTFree e s
  | ExprSCtx s => RTExprS e s
  | FldWrLCtx f v s => RTFldWr (Val v) f e s
  | FldWrRCtx e1 f s => RTFldWr e1 f e s
  | FldRdCtx v e1 f s => RTFldRd v e1 f s
  | CASLCtx v e1 f e2 s => RTCAS v e1 f e2 e s
  | CASMCtx v e1 f v3 s => RTCAS v e1 f (Val v3) e s
  | CASRCtx v f v2 v3 s => RTCAS v (Val v2) f (Val v3) e s
  | AllocCtx fs s => RTAlloc e fs s
  | SpawnCtx proc args s => RTSpawn proc args s
  end.


Inductive runtime_ectx :=
| ExprCtx (e : expr_ectx)
| StmtCtx (s : stmt_ectx)
.

Definition runtime_ectx_fill_item (Ki : runtime_ectx) (e : runtime_expr) : runtime_expr :=
  match Ki, e with
  | ExprCtx E, Expr e stk => Expr (expr_fill_item E e) stk
  | StmtCtx s, Expr e stk => Stmt (stmt_fill_item s e) stk
  | _, _ => e
  end.

Global Instance fill_item_inj Ki : Inj (=) (=) (runtime_ectx_fill_item Ki).
Proof. destruct Ki as [E|E]; destruct E; intros x y ?; simplify_eq/=; auto with f_equal; destruct x; destruct y; simplify_eq/=; auto with f_equal.
-

Qed.




