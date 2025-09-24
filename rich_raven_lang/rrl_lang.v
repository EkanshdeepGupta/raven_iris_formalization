From stdpp Require Export binders strings.
From stdpp Require Import countable.
Require Import Eqdep_dec.
From stdpp Require Import gmap list sets coPset.
From stdpp Require Import namespaces.

From iris Require Import options.
From iris.algebra Require Import ofe cmra agree.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import tactics.

From raven_iris.simp_raven_lang Require Export lang lifting ghost_state.
From raven_iris.simp_raven_lang Require Import ghost_state.

From Coq.Program Require Import Wf.

Require Import Coq.Program.Equality.

Class inGs {I : Type} (Σ : gFunctors) (Gs : I → cmra) := {
  inGs_inG : ∀ i, inG Σ (Gs i)
}.

Context {I : Type}.
Context (Gs : I → cmra).
Context `{!inGs Σ Gs}. 

Context `{!simpLangG Σ}.

Definition lvar := string.

Definition proc_name := string.
Global Parameter proc_set : gset proc_name.

Definition pred_name := string.
Global Parameter pred_set : gset pred_name.

Definition inv_name := string.
Global Parameter inv_set : gset inv_name.

Class ResourceAlgebra (A: Type) := {
  comp : A -> A -> A;
  frame : A -> A -> A;
  valid : A -> Prop;
  fpuValid : A -> A -> Prop;
  fpuAxiom : forall x y, fpuValid x y -> valid x /\ valid y /\ forall c, (valid (comp x c) -> valid (comp y c));
  (* RA Axioms *)
  (* ra_ucmra : ucmra; *)
  (* ra_ucmra_map : A -> ra_ucmra; *)
}.

Global Declare Instance RAEq : forall A: Type, EqDecision (ResourceAlgebra A).
Global Declare Instance RACountable : forall A: Type, Countable (ResourceAlgebra A).

Record RA_Pack := {
  RA_carrier :> Type;
  RA_carrier_eqdec :> EqDecision RA_carrier;
  RA_inst :> ResourceAlgebra RA_carrier;
}.

Global Axiom ra_eq_dec :  EqDecision RA_Pack .

Parameter fld_set : gset lang.fld_name.

Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

Parameter ghost_map : loc -> fld_name -> gname.

Inductive val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc).

(* TODO: Figure out how to incorporate RA values *)
Inductive LitRAElem (r : RA_Pack) (x : RA_carrier r): Type. 

Scheme Equality for val.

Inductive LExpr :=
| LVar (x : lvar)
| LVal (v : val)
| LUnOp (op : un_op) (e : LExpr)
| LBinOp (op : bin_op) (e1 e2 : LExpr)
(* | LIfE  *)
| LIfE (e1 e2 e3 : LExpr)
| LStuck
.

Definition symb_map : Type := lvar -> val.

Fixpoint interp_lexpr (le : LExpr) (mp : symb_map) : option val :=
  match le with
  | LVar x => Some (mp x)
  
  | LVal v => Some v

  | LUnOp op e =>
    match op with
    | NotBoolOp =>
      match interp_lexpr e mp with
      | Some (LitBool b) => Some (LitBool (negb b))
      | _ => None
      end
    | NegOp =>
      match interp_lexpr e mp with
      | Some (LitInt i) => Some (LitInt (-1 * i))
      | _ => None
      end
    end
  
  | LBinOp op e1 e2 =>
    match op with
    | AddOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 + i2))
      | _, _ => None
      end

    | SubOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 - i2))
      | _, _ => None
      end

    | MulOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 * i2))
      | _, _ => None  
      end

    | DivOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 / i2))
      | _, _ => None
      end

    | ModOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 mod i2))
      | _, _ => None
      end

    | EqOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (if val_beq v1 v2 then true else false))
      | _, _ => None
      end

    | NeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (if val_beq v1 v2 then false else true))
      | _, _ => None
      end

    | LtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.ltb i1 i2 then true else false))
      | _, _ => None
      end

    | GtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.gtb i1 i2 then true else false))
      | _, _ => None
      end
    
    | LeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.leb i1 i2 then true else false))
      | _, _ => None
      end
      
    | GeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.geb i1 i2 then true else false))
      | _, _ => None
      end

    | AndOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 && b2))
      | _, _ => None
      end

    | OrOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 || b2))
      | _, _ => None
      end
    end

  | LIfE e1 e2 e3 =>
    match interp_lexpr e1 mp with
    | Some (LitBool true) => interp_lexpr e2 mp
    | Some (LitBool false) => interp_lexpr e3 mp
    | _ => None
    end 

  | LStuck => None
  end.


(* TODO: Fix this with a proper error state; at present returning True when le is malformed which is not sound. *)
Definition LExpr_holds (le : LExpr) (mp : symb_map) : Prop :=
  match interp_lexpr le mp with
  | Some v => v = LitBool true
  | None => True
  end.

Definition trnsl_val (v: lang.val) : val :=
match v with
| lang.LitBool b => LitBool b
| lang.LitInt i => LitInt i
| lang.LitUnit => LitUnit
| lang.LitLoc l => LitLoc l
end.

Lemma trnsl_val_inj : forall v1 v2, trnsl_val v1 = trnsl_val v2 -> v1 = v2.
Proof.
  destruct v1, v2; simpl; try discriminate; intros H; inversion H; subst; auto.
Qed.

Fixpoint lexpr_subst (expr : LExpr) (subst_map : gmap var LExpr) :=
match expr with
| LVar x => match subst_map !! x with
    | None => LVar x
    | Some e => e
    end
| LVal v => LVal v
| LUnOp op e => LUnOp op (lexpr_subst e subst_map)
| LBinOp op e1 e2 => LBinOp op (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map)
| LIfE e1 e2 e3 => LIfE (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map) (lexpr_subst e3 subst_map)
| LStuck => LStuck
end.

Global Instance ra_carrier_eqdec_instance (r : RA_Pack) : EqDecision (RA_carrier r) :=
  RA_carrier_eqdec r.

Global Instance val_eq : EqDecision val.
Proof.
  refine (fun x y =>
    match x, y with
    | LitBool b1, LitBool b2 => cast_if (decide (b1 = b2))
    | LitInt i1, LitInt i2 => cast_if (decide (i1 = i2))
    | LitUnit, LitUnit => left eq_refl
    | LitLoc l1, LitLoc l2 => cast_if (decide (l1 = l2))
    (* | LitRAElem r1 a1, LitRAElem r2 a2 =>
        match ra_eq_dec r1 r2 with
        | left Heq =>
            (* r1 = r2, so carriers are same, can cast and decide equality on carrier elements *)
            cast_if (decide (eq_rect r1 (fun r => RA_carrier r) a1 r2 Heq = a2))

        | right _ => right _
        end *)
    | _, _ => right _
    end). 
  all: try by f_equal.
  all: try intros Heq; inversion Heq; auto.
Qed.

(* TODO: To be proved *)
Global Declare Instance LExpr_Eq : EqDecision LExpr.
Global Declare Instance LExpr_Countable : Countable LExpr.

Global Declare Instance val_countable : Countable val.

Definition pvar_typs : Type := var -> typ.
Definition lvar_typs : Type := lvar -> typ.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : lang.expr) *)
| IfS (e : lang.expr) (s1 s2 : stmt)
| Assign (v : lang.var) (e : lang.expr)
(* | Free (e : lang.expr) *)
| SkipS
| StuckS (* stuck statement *)
(* | ExprS (e : lang.expr) *)
| Call (v : lang.var) (proc : proc_name) (args : list lang.expr)
| FldWr (v : lang.var) (fld : fld_name) (e2 : lang.expr)
| FldRd (v : lang.var) (e : lang.expr) (fld : fld_name)
| CAS (v : lang.var) (e1 : lang.expr) (fld : fld_name) (e2 : lang.expr) (e3 : lang.expr)
| Alloc (v : lang.var) (fs: list (lang.fld_name * lang.val))
| Spawn (proc : proc_name) (args : list lang.expr)
| UnfoldPred (pred : pred_name) (args : list lang.expr)
| FoldPred (pred : pred_name) (args : list lang.expr)
| InvAccessBlock (inv: inv_name) (args : list lang.expr) (body : stmt)
(* | UnfoldInv (inv: inv_name) (args : list lang.expr)
| FoldInv (inv: inv_name) (args : list lang.expr) *)
| Fpu (e : lang.expr) (fld : fld_name) (RAPack : RA_Pack) (old_val : RA_carrier RAPack) (new_val : RA_carrier RAPack)
.

Inductive assertion :=
| LProc (proc_name : proc_name) (proc_entry : ProcRecord)
| LStack (σ : gmap lang.var lvar)
| LExprA (p: LExpr)
| LPure (p : Prop)
| LOwn (e: LExpr) (fld: fld_name) (chunk: val)
| LGhostOwn (e: LExpr) (fld: fld_name) (RAPack: RA_Pack) (chunk: RA_carrier RAPack)
| LForall (v : var) (body : assertion)
| LExists (v : var) (body : assertion)
| LImpl (cond : LExpr) (body : assertion)
| LInv (inv_name : inv_name) (args : list LExpr)
| LPred (pred_name : pred_name) (args : list LExpr)
| LAnd (assert1 : assertion) (assert2 : assertion)

with ProcRecord := | Proc 
  (proc_args: list (var * typ))
  (proc_local_vars: list (var * typ))
  (proc_precond : assertion)
  (proc_postcond : assertion)
  (body : stmt).

Definition proc_args_of (p : ProcRecord) :=
  match p with Proc args _ _ _ _ => args end.

Definition proc_locals_of (p : ProcRecord) :=
  match p with Proc _ locs _ _ _ => locs end.

Definition proc_precond_of (p : ProcRecord) :=
  match p with Proc _ _ pre _ _ => pre end.

Definition proc_postcond_of (p : ProcRecord) :=
  match p with Proc _ _ _ post _ => post end.

Definition proc_body_of (p : ProcRecord) :=
  match p with Proc _ _ _ _ body => body end.

Fixpoint subst (ra: assertion) (mp: gmap var LExpr) : assertion := match ra with
| LProc p p_e => LProc p p_e
| LStack σ => LStack σ
| LExprA e => LExprA (lexpr_subst e mp)
| LPure p => LPure p
| LOwn e fld chunk => LOwn (lexpr_subst e mp) fld chunk
| LGhostOwn e fld RAPack chunk => LGhostOwn e fld RAPack chunk
| LForall vars body => LForall vars (subst body mp)
| LExists vars body => LExists vars (subst body mp)
| LImpl cond body => LImpl (lexpr_subst cond mp) (subst body mp)
| LInv inv_name args => 
    LInv inv_name (map (fun expr => lexpr_subst expr mp) args)
| LPred pred_name args =>
    LPred pred_name (map (fun expr => lexpr_subst expr mp) args)
| LAnd a1 a2 => LAnd (subst a1 mp) (subst a2 mp)
end.

  Definition StackFree : assertion -> bool.
  Admitted.

Global Parameter proc_map : gmap proc_name ProcRecord.
Axiom proc_map_set : dom proc_map = proc_set.
Axiom proc_args_unique : map_Forall (λ proc proc_entry, NoDup (proc_args_of proc_entry).*1 ) proc_map.

Axiom proc_spec_stack_free : 
  map_Forall (λ proc proc_entry, StackFree (proc_precond_of proc_entry) /\ StackFree (proc_postcond_of proc_entry) ) proc_map.

Record InvRecord := Inv {
  inv_args: list var;
  inv_body: assertion;
}.

Global Parameter inv_map : gmap inv_name InvRecord.
Axiom inv_map_set : dom inv_map = inv_set.

Record PredRecord := Pred {
  pred_args: list var;
  pred_body: assertion;
}.

Global Parameter pred_map : gmap pred_name PredRecord.
Axiom pred_map_set : dom pred_map = pred_set.

Inductive expr_well_defined : lang.expr -> Prop :=
| Constr e :
  expr_well_defined e.

Inductive stmt_well_defined : pvar_typs -> stmt -> Prop := 
| SeqTp ρ s1 s2 :
  stmt_well_defined ρ s1 ->
  stmt_well_defined ρ s2 ->
  stmt_well_defined ρ (Seq s1 s2)
(* | ReturnTp e : 
    expr_well_defined e ->
    stmt_well_defined (Return e) *)
| IfSTp ρ e s1 s2 : 
    expr_well_defined e -> 
    stmt_well_defined ρ s1 ->
    stmt_well_defined ρ s2 -> 
    stmt_well_defined ρ (IfS e s1 s2)
| AssignTp ρ v e: 
    expr_well_defined e ->
    stmt_well_defined ρ (Assign v e)
(* | FreeTp e: 
    expr_well_defined e ->
    stmt_well_defined (Free e) *)
| SkipSTp ρ : stmt_well_defined ρ (SkipS)
| StuckSTp ρ : stmt_well_defined ρ (StuckS)
(* | ExprSTp e: 
    expr_well_defined e -> 
    stmt_well_defined (ExprS e) *)
| CallTp ρ v proc proc_entry args: 
    proc ∈ proc_set -> 
    proc_map !! proc = Some proc_entry ->
    length args = length (proc_args_of proc_entry) ->
    (Forall (fun arg => expr_well_defined arg) args) ->
    stmt_well_defined ρ (Call v proc args)
| FldWrTp ρ v fld e2: 
    (fld ∈ fld_set) -> 
    expr_well_defined e2 -> 
    stmt_well_defined ρ (FldWr v fld e2)
| FldRdTp ρ v e fld: 
    fld ∈ fld_set ->
    expr_well_defined e ->
    stmt_well_defined ρ (FldRd v e fld)
| CASTp ρ v e1 fld e2 e3: 
    fld ∈ fld_set ->
    expr_well_defined e1 ->
    expr_well_defined e2 ->
    expr_well_defined e3 ->
    stmt_well_defined ρ (CAS v e1 fld e2 e3)
| AllocTp ρ v fs: 
    Forall (fun fld_v => (fst fld_v) ∈ fld_set) fs ->
    stmt_well_defined ρ (Alloc v fs)
| SpawnTp ρ proc args: 
    proc ∈ proc_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined ρ (Spawn proc args)
| UnfoldPredTp ρ pred args : 
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined ρ (UnfoldPred pred args)
| FoldPredTp ρ pred args : 
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined ρ (FoldPred pred args)
| InvAccessBlockTp ρ inv args stmt:
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined ρ stmt ->
    stmt_well_defined ρ (InvAccessBlock inv args stmt)

(* | UnfoldInvTp inv args : 
    inv ∈ inv_set -> 
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (UnfoldInv inv args)
| FoldInvTp inv args : 
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (FoldInv inv args) *)
| FpuTp ρ e fld RAPack old_val new_val : 
    fld ∈ fld_set ->
    expr_well_defined e ->
    stmt_well_defined ρ (Fpu e fld RAPack  old_val new_val)
.

Section AtomicAnnotations.
  Parameter inv_namespace_map : inv_name -> namespace.

  Axiom inv_namespace_disjoint : forall inv1 inv2 : inv_name, inv1 ∈ inv_set -> inv2 ∈ inv_set -> (inv_namespace_map inv1) ## (inv_namespace_map inv2).

  Inductive AtomicStep : Type :=
  | Closed
  | Opened (S : list (inv_name * list LExpr))
  | Stepped (S : list (inv_name * list LExpr))
  .

  Definition AtomicAnnotation : Type := (gset inv_name * AtomicStep).

  Definition maskAnnot : Type := gset inv_name.

End AtomicAnnotations.

Section Translation.

    Definition trnsl_lval (v: val) : lang.val :=
    match v with
    | LitBool b => (lang.LitBool b) 
    | LitInt i => (lang.LitInt i)
    | LitUnit => (lang.LitUnit)
    | LitLoc l => (lang.LitLoc (lang.Loc l.(loc_car)))
    (* | LitRAElem _ _ => None *)
    end.

    Lemma trnsl_lval_injective v1 v2 : trnsl_lval v1 = trnsl_lval v2 -> v1 = v2.
    Proof.
      Admitted.

    Lemma trnsl_lval_trnsl_val_inverse y: trnsl_lval (trnsl_val y) = y.
    Proof.
      Admitted.

    Global Parameter trnsl_pred : pred_name -> list LExpr -> symb_map -> iProp Σ.
    Global Parameter trnsl_inv : inv_name -> list LExpr -> symb_map -> iProp Σ.


    Definition stack: Type := gmap lang.var lvar.

    Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk).


  Fixpoint trnsl_expr_lExpr (stk: stack) (e: lang.expr) :=
  match e with
  | Var x => match stk !! x with
             | Some v => Some (LVar v)
             | None => None
             end
  | Val v => Some (LVal (trnsl_val v))
  | UnOp op e => 
      match trnsl_expr_lExpr stk e with
      | Some le => Some (LUnOp op le)
      | None => None
      end
  | BinOp op e1 e2 => 
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2) with
    | Some le1, Some le2 => Some (LBinOp op le1 le2)
    | _, _ => None
    end

  | IfE e1 e2 e3 =>
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2), (trnsl_expr_lExpr stk e3) with
    | Some le1, Some le2, Some le3 => Some (LIfE le1 le2 le3)
    | _, _, _ => None
    end

  | StuckE => Some LStuck
  end.

  Inductive trnsl_stmt_ret :=
  | None'
  | Error
  | Some' (s: lang.stmt).
  
  Fixpoint trnsl_atomic_block (body : stmt) (step_taken : bool) : trnsl_stmt_ret * bool := 
  match body, step_taken with
  | Seq s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken with
    | (None', step_taken') => trnsl_atomic_block s2 step_taken'
    | (Some' s1, step_taken') => 
      match trnsl_atomic_block s2 step_taken' with
      | (None', step_taken'') => (Some' s1, step_taken'')
      | (Some' s2, step_taken'') => (Some' (lang.Seq s1 s2), step_taken'')
      | (Error, _) => (Error, step_taken')
      end
    | (Error, _) => (Error, step_taken)
    end

  | IfS e s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken, trnsl_atomic_block s2 step_taken with
    | (None', step_taken'), (None', step_taken'') => (Some' (lang.SkipS), step_taken' || step_taken'')
    | (None', step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e lang.SkipS s2), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (None', step_taken'') => (Some' (lang.IfS e s1 lang.SkipS), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e s1 s2), step_taken' || step_taken'')
    | (Error, _), _ | _, (Error, _) => (Error, step_taken)
    end

  | Assign v e, false => (Some' (lang.Assign v e), true)
  | Assign v e, true => (Error, true)

  | SkipS, false => (Some' lang.SkipS, false)
  | SkipS, true => (Some' lang.SkipS, true)

  | StuckS, _ => (Some' lang.StuckS, step_taken)
  | Call v proc args, _ => (Error, true)

  | FldWr v fld e2, false => (Some' (lang.FldWr v fld e2), true)
  | FldWr v fld e2, true => (Error, true)

  | FldRd v e fld, false => (Some' (lang.FldRd v e fld), true)
  | FldRd v e fld, true => (Error, true)

  | CAS v e1 fld e2 e3, false => (Some' (lang.CAS v e1 fld e2 e3), true)
  | CAS v e1 fld e2 e3, true => (Error, true)

  | Alloc v fs, false => (Some' (lang.Alloc v fs), true)
  | Alloc v fs, true => (Error, true)

  | Spawn proc args, false => (Some' (lang.Spawn proc args), true)
  | Spawn proc args, true => (Error, true)
  | InvAccessBlock inv args body, _ => trnsl_atomic_block body step_taken
  | _, _ => (None', step_taken)
  end.

  Fixpoint trnsl_stmt (s : stmt) : trnsl_stmt_ret := match s with
  | Seq s1 s2 => 
    match trnsl_stmt s1, trnsl_stmt s2 with
    | None', None' => None'
    | Some' s1, None' => Some' s1
    | None', Some' s2 => Some' s2
    | Some' s1', Some' s2' => Some' (stmt_append s1' s2' )
    | Error, _
    | _, Error => Error
    end

  | IfS e s1 s2 => 
      match (trnsl_stmt s1), (trnsl_stmt s2) with
      | None', None' => None'
      | Some' s1, None' => Some' (lang.IfS e s1 lang.SkipS)
      | None', Some' s2 => Some' (lang.IfS e lang.SkipS s2 )
      | Some' s1, Some' s2 => Some' (lang.IfS e s1 s2) 
      | Error, _ | _, Error => Error
      end

  | Assign v e => Some' (lang.Assign v e)
  | SkipS => Some' (lang.SkipS)
  | StuckS => Some' lang.StuckS
  | Call v proc args => Some' (lang.Call v proc args)
  | FldWr v fld e2 => Some' (lang.FldWr v fld e2)
  
  | FldRd v e1 fld => Some' (lang.FldRd v e1 fld)
  | CAS v e1 fld e2 e3 => Some' (lang.CAS v e1 fld e2 e3)
  | Alloc v fs => Some' (lang.Alloc v fs)
  | Spawn proc args => None'
  
  | UnfoldPred pred args => None'
  | FoldPred pred args => None'
  | InvAccessBlock inv args body => (trnsl_atomic_block body false).1

  (* | UnfoldInv inv args => None'
  | FoldInv inv args => None' *)
  | Fpu e fld RAPack old_val new_val => None'
  end.

  Definition transport {A B : Type} (H : A = B) (x : A) : B :=
    eq_rect A id x _ H.

  Lemma transport_sym : forall (A B : Type) (H : A = B) (x : B),
     (transport H (transport (eq_sym H) x)) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma transport_cancel : forall (A B : Type) (H : A = B) (x : A),
    transport (eq_sym H) (transport H x) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma eq_rect_transport_comp : forall (R: RA_Pack) (U : Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)) (c : U),
  eq_rect (RA_carrier R) (λ T : Type, T → T → T) (RA_inst R).(comp) U Heq_car (transport Heq_car x) c = 
  transport Heq_car ((RA_inst R).(comp) x (transport (eq_sym Heq_car) c)).
Proof.
  intros. unfold transport. destruct Heq_car. simpl. reflexivity.
Qed.


  Lemma eq_rect_transport_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x) ->
    (RA_inst R).(valid) x.
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_valid_inv : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    (RA_inst R).(valid) x ->
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x).
    
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_inv_comp_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (y : (RA_carrier R)) (c: U),
    (RA_inst R).(valid) ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c)) ->
    eq_rect (RA_carrier R) (λ T : Type, T → Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c))).
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Definition Γ_type := forall R : RA_Pack,
  { i : I & { U : ucmra |
      CmraDiscrete U /\
      { Heq_car : RA_carrier R = ucmra_car U | 
          ucmra_cmraR U = Gs i /\ 
          ucmra_op U = eq_rect (RA_carrier R) (fun T => T -> T -> T) ((RA_inst R).(comp)) (ucmra_car U) Heq_car /\
          ucmra_valid U = eq_rect (RA_carrier R) (fun T => T -> Prop) ((RA_inst R).(valid)) (ucmra_car U) Heq_car
      }
  } } .

  Lemma RAPack_fpuValid (Γ: Γ_type) :
    forall R : RA_Pack,
      forall x y : RA_carrier R,
        (* let '(existT i (existT U (exist _ Hdis Heq_car (conj Hind (conj Hcomp Hvalid))))) := Γ R in *)
        let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Hcmra (conj Hop Hvalid)))))) := Γ R in
        (RA_inst R).(fpuValid) x y -> (transport Heq_car x) ~~> (transport Heq_car y).
  Proof.
    intros R x y.
    destruct (Γ R) as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]].
    intros Hfpu.
    
    intros n c Hvalid.
    destruct c as [c|].

    - simpl in *. 

    (* make the dot-notation explicit so we can rewrite the op *)
    change (transport Heq_car x ⋅ c) with (ucmra_op U (transport Heq_car x) c) in Hvalid.
    rewrite Hcomp in Hvalid.
    (* bring the context back to the R-side by destructing the equality *)
    apply cmra_discrete_valid_iff.
    apply cmra_discrete_valid_iff in Hvalid.
    change (✓ (transport Heq_car y ⋅ c)) with (ucmra_valid U (transport Heq_car y ⋅ c)).
    rewrite Hval.
    unfold transport.

    set (cR := transport (eq_sym Heq_car) c).
    assert ((RA_inst R).(valid) ((RA_inst R).(comp) y cR)). {
      apply (fpuAxiom x y); [done | ].

      rewrite eq_rect_transport_comp in Hvalid.
      unfold cR.
      change (✓ transport Heq_car (comp x (transport (eq_sym Heq_car) c))) with ((ucmra_valid U) (transport Heq_car ((RA_inst R).(comp) x (transport (eq_sym Heq_car) c)))) in Hvalid.
      
      rewrite Hval in Hvalid.
      apply (eq_rect_transport_valid R (ucmra_car U) Heq_car). done.
    }

    subst cR.

    change (eq_rect (RA_carrier R) (λ T : Type, T → Prop) (RA_inst R).(valid) U Heq_car ((ucmra_op U) (eq_rect (RA_carrier R) id y U Heq_car) c)).

    rewrite Hcomp.
    rewrite eq_rect_transport_comp.

    apply eq_rect_transport_inv_comp_valid.
    done.

    - simpl in *. apply cmra_discrete_valid_iff. apply cmra_discrete_valid_iff in Hvalid.

    apply (fpuAxiom x y) in Hfpu.
    destruct Hfpu as [_ [HvVal _]].
    change (@cmra.valid (cmra_car (ucmra_cmraR U)) (cmra_valid (ucmra_cmraR U))) with (ucmra_valid U).
    rewrite Hval.
    apply eq_rect_transport_valid_inv. done.
  Qed.

(* cast a chunk from RA_carrier to the correct cmra_car and carry the inG instance *)
(* Definition cast_chunk `{!inGs Σ Gs} 
           (Γ : Γ_type) (R : RA_Pack) (chunk : RA_carrier R)
  : { i : I & cmra_car (Gs i) * inG Σ (Gs i) } :=
  match Γ R with
  | existT i (exist U (conj Heq_car Heq_cmra)) =>
      let chunkU    := transport (eq_sym Heq_car) chunk in
      let chunkCmra := transport (eq_sym (cmra_ucmra_car_eq U)) chunkU in
      let chunkGs   := transport (f_equal cmra_car Heq_cmra) chunkCmra in
      existT _ i (chunkGs, inGs_inG i)
  end. *)

  Fixpoint trnsl_assertion (Γ: Γ_type) (a : assertion) (stk_id: stack_id) (mp : symb_map): option (iProp Σ) := match a with
    | LProc p p_e => 
      match p_e with
        Proc args locals pre post body => 
          match trnsl_stmt body with
          | None' =>
            Some (proc_tbl_chunk p (
              lang.Proc p args locals lang.SkipS
            ))
          | Some' stmt =>
            Some (proc_tbl_chunk p (
              lang.Proc p args locals stmt
            ))
          | Error => None
          end
      end
    | LStack σ => Some (stack_frame_own stk_id (symb_stk_to_stk_frm σ mp))
    | LExprA l_expr => 
      Some (⌜LExpr_holds l_expr mp⌝%I)
      (* Some (⌜(e = (lang.Val (lang.LitBool true)))⌝) *)
    
    (* ⌜(trnsl_expressions l_expr) = Some (lang.Val (lang.LitBool true))⌝ *)
    | LPure p => Some (⌜ p ⌝%I)
    | LOwn l_expr fld chunk => 
      match trnsl_lval chunk with
      | chunk =>
      Some (∃ l: lang.loc, (
        ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ 
        (l#fld ↦{ 1 } chunk)
        )%I)%I
        (* (heap_maps_to l fld 1 chunk) *)
        end
    (* TODO: Embed RAs properly and redefine this correctly *)

    | LGhostOwn l_expr fld RAPack chunk => 
      let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) := Γ RAPack in
      (* let '(existT i (exist _ U (conj Heq_cmra Heq_car))) := Γ RAPack in *)
      let chunkU := transport (Heq_car) chunk in
      let chunkGs := transport (f_equal cmra_car Heq_cmra) chunkU in 
      let HinG := inGs_inG i in

      Some (∃ l : lang.loc, (⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ (own (ghost_map l fld) chunkGs (inG0 := HinG)))%I)%I
    | LForall v body => 
      match trnsl_assertion Γ body stk_id mp with
      | None => None
      | Some body_expr => Some (∀ v':lang.val, body_expr)%I
      end
      (* ∀ v':lang.val, (trnsl_assertion (body)) *)
      (* ∀ vs, (trnsl_assertion body) *)
      (* True *)
    | LExists v body => 
      Some (∃ v': val,
        match trnsl_assertion Γ body stk_id (λ x, if String.eqb x v then v' else mp x) with
        | None => True
        | Some body_expr => body_expr
        end
    )%I
    
    | LImpl cnd body => 
      match (trnsl_assertion Γ body stk_id mp) with
      | None => None
      | Some body_expr => 
      Some (⌜LExpr_holds cnd mp⌝ -∗ body_expr)%I
      end
      (* True *)
    | LInv inv' args => 
      match inv_map !! inv' with
      | Some inv_record => 
        let subst_map := list_to_map (zip inv_record.(inv_args) args) in
        let subst_body := subst inv_record.(inv_body) subst_map in

        Some (inv (inv_namespace_map inv') (trnsl_inv inv' args mp))

        (* False *)
      | None => None
      end
      (* False *)
    | LPred pred args => Some (trnsl_pred pred args mp)
    | LAnd a1 a2 => 
      match (trnsl_assertion Γ a1 stk_id mp), (trnsl_assertion Γ a2 stk_id mp) with
      | None, _ => None
      | _, None => None
      | Some a1, Some a2 => Some (a1 ∗ a2)%I
      end
    end
    .


  Axiom trnsl_pred_validity : forall (Γ: Γ_type) (pred : pred_name) (args : list LExpr) (stk_id: stack_id) (mp : symb_map), 
    match pred_map !! pred with
    | Some pred_rec => 
      let subst_map := list_to_map (zip pred_rec.(pred_args) args) in

      trnsl_assertion Γ (subst pred_rec.(pred_body) subst_map) stk_id mp = Some (trnsl_pred pred args mp)
    | None => true
    end
  .

  Axiom trnsl_inv_validity : forall (Γ: Γ_type) (inv : inv_name) (args : list LExpr) (stk_id: stack_id) (mp : symb_map), 
    match inv_map !! inv with
    | Some inv_rec => 
      let subst_map := list_to_map (zip inv_rec.(inv_args) args) in

      trnsl_assertion Γ (subst inv_rec.(inv_body) subst_map) stk_id mp = Some (trnsl_inv inv args mp)
    | None => true
    end
  .

  Definition entails P Q := forall Γ stk_id mp, ∃ P' Q', trnsl_assertion Γ P stk_id mp = Some P' /\ trnsl_assertion Γ Q stk_id mp = Some Q' /\ (P' ⊢  Q')%I.

End Translation.


Section TypeInf.
    Definition stk_type_compat (ρ : pvar_typs) (σ : lvar_typs) (stk : stack) := forall v lv, (stk !! v = Some lv) -> ρ v = σ lv.


  Definition typeOf (v: lang.val) : typ := 
  match v with
  | lang.LitBool _ => TpBool
  | lang.LitInt _ => TpInt
  | lang.LitUnit => TpUnit
  | lang.LitLoc _ => TpLoc
  end.


  Fixpoint inf_expr (ρ: pvar_typs) (e: lang.expr) : option typ :=
  match e with
  | Var x => Some (ρ x)
  | Val v => Some (typeOf v)
  | UnOp NotBoolOp e =>
    match inf_expr ρ e with
    | Some TpBool => Some TpBool
    | _ => None
    end
  | UnOp NegOp e =>
    match inf_expr ρ e with
    | Some TpInt => Some TpInt
    | _ => None
    end

  | BinOp (AddOp | SubOp | MulOp | DivOp | ModOp | LtOp | GtOp | LeOp | GeOp) e1 e2 =>
    match inf_expr ρ e1, inf_expr ρ e2 with
    | Some TpInt, Some TpInt => Some TpInt
    | _, _ => None
    end

  | BinOp (AndOp | OrOp) e1 e2 =>
    match inf_expr ρ e1, inf_expr ρ e2 with
    | Some TpBool, Some TpBool => Some TpBool
    | _, _ => None
    end

  | BinOp (EqOp | NeOp) e1 e2 =>
    match inf_expr ρ e1, inf_expr ρ e2 with
    | Some tp1, Some tp2 => if typ_beq tp1 tp2 then Some TpBool else None
    | _, _ => None
    end

  | IfE e1 e2 e3 =>
    match inf_expr ρ e1, inf_expr ρ e2, inf_expr ρ e3 with
    | Some TpBool, Some tp2, Some tp3 => if typ_beq tp2 tp3 then Some tp2 else None
    | _, _, _ => None
    end

  | _ => None
  end.


  Fixpoint inf_lexpr (σ: lvar_typs) (le: LExpr) : option typ := 
  match le with
  | LVar x => Some (σ x)
  | LVal v => Some (typeOf (trnsl_lval v))
  | LUnOp NotBoolOp e =>
    match inf_lexpr σ e with
    | Some TpBool => Some TpBool
    | _ => None
    end
  | LUnOp NegOp e =>
    match inf_lexpr σ e with
    | Some TpInt => Some TpInt
    | _ => None
    end

  | LBinOp (AddOp | SubOp | MulOp | DivOp | ModOp | LtOp | GtOp | LeOp | GeOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpInt, Some TpInt => Some TpInt
    | _, _ => None
    end

  | LBinOp (AndOp | OrOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpBool, Some TpBool => Some TpBool
    | _, _ => None
    end

  | LBinOp (EqOp | NeOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some tp1, Some tp2 => if typ_beq tp1 tp2 then Some TpBool else None
    | _, _ => None
    end

  | LIfE e1 e2 e3 =>
    match inf_lexpr σ e1, inf_lexpr σ e2, inf_lexpr σ e3 with
    | Some TpBool, Some tp2, Some tp3 => if typ_beq tp2 tp3 then Some tp2 else None
    | _, _, _ => None
    end

  | _ => None
  end.


  Definition env_typ_well_defined (σ : lvar_typs) (mp : symb_map) :=
      forall lv, 
      match (σ lv), (mp lv) with
      | TpBool, LitBool b => True
      | TpInt, LitInt i => True
      | TpLoc, LitLoc l => True
      | _, _ => False
      end.


  Lemma lexpr_expr_typ_compat ρ σ stk e le tp :
    stk_type_compat ρ σ stk ->
    trnsl_expr_lExpr stk e = Some le ->
    inf_expr ρ e = Some tp ->
    inf_lexpr σ le = Some tp.
  Proof. 
    Admitted.

  Lemma interp_lexpr_typ_compat σ le tp val mp :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    (interp_lexpr le mp) = Some val ->
    typeOf (trnsl_lval val) = tp.
  Proof.
    Admitted.

  Lemma lexpr_typcheck_well_defined σ mp le tp :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    ∃ val, interp_lexpr le mp = Some val.
  Proof.
    Admitted.


End TypeInf.


Section RavenLogic.

  Definition fresh_lvar (stk: stack) v := forall v', not (stk !! v' = Some v). 

  Fixpoint field_list_to_assertion lexpr fld_vals  := match fld_vals with
  | [] => LPure true
  | (fld,val) :: fld_vals => LAnd (LOwn lexpr fld (trnsl_val val)) (field_list_to_assertion lexpr fld_vals)
  end.

  Inductive RavenHoareTriple : 
  pvar_typs -> lvar_typs ->
  assertion -> 
      stmt -> maskAnnot ->
  assertion ->  Prop :=

  | VarAssignmentRule ρ σ stk mask v lv e lexpr :
    trnsl_expr_lExpr stk e = Some lexpr ->
    fresh_lvar stk lv ->
    stk_type_compat ρ σ stk -> 
    RavenHoareTriple ρ σ
      (LStack stk) 
        (Assign v e) mask 
      (LExists lv 
        (LAnd 
          (LStack (<[v := lv]> stk))
          (LExprA (LBinOp EqOp (LVar lv) lexpr))
        )
      )
    
  
  | HeapReadRule ρ σ stk mask x e val fld lexpr_e lvar_x  :
    trnsl_expr_lExpr stk e = Some lexpr_e ->
    fresh_lvar stk lvar_x ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn lexpr_e fld val))  
        (FldRd x e fld) mask
      (LExists lvar_x (LAnd 
        (LStack (<[x := lvar_x]> stk)) 
        (LAnd 
          (LOwn lexpr_e fld val) 
          (LExprA (LBinOp EqOp (LVar lvar_x) (LVal val)))
        )
      ))

  | HeapWriteRule ρ σ stk mask v fld e old_val new_val lv :
    stk !! v = Some lv ->
    trnsl_expr_lExpr stk e = Some (LVal new_val) ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn (LVar lv) fld old_val))
        (FldWr v fld e) mask
      (LAnd (LStack stk) (LOwn (LVar lv) fld new_val))
  
    
  | HeapAllocRule ρ σ stk mask x fld_vals lvar_x :
    fresh_lvar stk lvar_x ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
       (LStack stk) 
        (Alloc x fld_vals) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (field_list_to_assertion (LVar lvar_x) fld_vals)))

  | ProcCallRuleRet ρ σ stk mask x proc_name args lexprs lvar_x proc_record :
    fresh_lvar stk lvar_x ->
    proc_map !! proc_name = Some proc_record ->
    length args = length (proc_args_of proc_record) ->
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip (proc_args_of proc_record).*1 lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LProc proc_name proc_record) (subst (proc_precond_of proc_record) subst_map)))
        (Call x proc_name args) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (subst (proc_postcond_of proc_record) (<[ "#ret_var" := LVar lvar_x]> subst_map)))) 

  | SequenceRule ρ σ mask a1 c1 a2 c2 a3 :
    RavenHoareTriple ρ σ
      a1 
        c1 mask
      a2
    ->
    RavenHoareTriple ρ σ
      a2
        c2 mask
      a3
    ->
    RavenHoareTriple ρ σ
      a1 
        (Seq c1 c2) mask
      a3

  | CondRule ρ σ stk1 stk2 mask e s1 s2 p q lexpr :
    trnsl_expr_lExpr stk1 e = Some lexpr ->
    inf_expr ρ e = Some TpBool ->
    stk_type_compat ρ σ stk1 ->
    stk_type_compat ρ σ stk2 ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (lexpr))) )
        s1 mask
      (LAnd (LStack stk2) q)
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (LUnOp NotBoolOp lexpr))))
        s2 mask
      (LAnd (LStack stk2) q)
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) p) 
        (IfS e s1 s2) mask
      (LAnd (LStack stk2) q)

  | InvAccessBlockRule ρ σ stk mask inv args stmt inv_record p q lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    inv ∈ mask ->
    inv_map !! inv = Some inv_record ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) p)) 
        stmt (mask ∖ {[inv]})
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) q))  ->
    
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) p)) 
        (InvAccessBlock inv args stmt ) mask
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) q))

  (* | InvUnfoldRule stk  mask1 inv args inv_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
      | Closed, Opened s => s = [ (inv, lexprs) ]
      | Opened s1, Opened s2 => s2 = (inv, lexprs) :: s1
      | Stepped s1, Stepped s2 => s2 = (inv, lexprs) :: s1
      | _, _ => False
    end
    ->
    inv ∈ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (LInv inv lexprs) (mask1, i1)
        (UnfoldInv inv args) 
      stk (subst inv_record.(inv_body) subst_map) (mask1 ∖ {[inv]}, i2) *)

  (* | InvFoldRule stk  mask1 inv args inv_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
    | Opened s, Closed => s = [ (inv, lexprs) ]
    | Stepped s, Closed => s = [ (inv, lexprs) ]
    | Opened s1, Opened s2 => s1 = (inv, lexprs) :: s2 /\ ¬(s2 = [])
    | Stepped s1, Stepped s2 => s1 = (inv, lexprs) :: s2 /\ ¬(s2 = [])
    | _, _ => False
    end
    ->
    inv ∉ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (subst inv_record.(inv_body) subst_map) (mask1, i1)
        (UnfoldInv inv args) 
      stk (LInv inv lexprs) (mask1 ∪ {[inv]}, i2) *)

  | PredUnfoldRule ρ σ stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LPred pred lexprs)) 
        (UnfoldPred pred args) mask
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map))

  | PredFoldRule ρ σ stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    stk_type_compat ρ σ stk ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map)) 
        (FoldPred pred args) mask
      (LAnd (LStack stk) (LPred pred lexprs))

  | FPURule ρ σ stk mask e l_expr fld RAPack old_val new_val :
    trnsl_expr_lExpr stk e = Some l_expr ->
    (RAPack.(RA_inst) ).(fpuValid) old_val new_val ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack old_val))
        (Fpu e fld RAPack old_val new_val) mask
        (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack new_val))

  | FrameRule ρ σ mask s p q r :
    RavenHoareTriple ρ σ
      p
        s mask
      q
    ->
    RavenHoareTriple ρ σ
      (LAnd p r)
        s mask
      (LAnd q r)
  
  | WeakeningRule ρ σ mask p p' q q' c :
    RavenHoareTriple ρ σ
      p 
        c mask
      q
    ->
    entails p' p ->
    entails q q' ->

    RavenHoareTriple ρ σ
      p'
        c mask
      q'

  | SkipRule ρ σ stk mask p :
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) p) 
        SkipS mask
      (LAnd (LStack stk) p)

  | CASSuccRule ρ σ stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val new_val :
    fresh_lvar stk lvar_v ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val) ->
    trnsl_expr_lExpr stk e3 = Some (LVal new_val) ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LOwn lexpr1 fld old_val))
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld new_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool true)))))) )

  | CASFailRule ρ σ stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val old_val2 :
    fresh_lvar stk lvar_v ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val2) ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LUnOp NotBoolOp (LBinOp EqOp (LVal old_val) (LVal old_val2))))))
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool false)))))))
  .

End RavenLogic.

Section LExpr_embed.
  (* TODO: Figure out the right way to do this deep embedding *)
  Definition EqOp_refl : forall a b mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b a) mp.
  Proof.
    intros.
    unfold LExpr_holds.
    destruct (interp_lexpr (LBinOp EqOp b a) mp) eqn: H0; try done.
  Admitted.
   (* rewrite H0 in H. rewrite H1 in H. rewrite H. reflexivity. *)
  (* Qed. *)

  Definition EqOp_trans : forall a b c mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b c) mp -> LExpr_holds (LBinOp EqOp a c) mp.
  Proof.
    Admitted.

  Definition EqOp_subst : forall var le e mp, LExpr_holds (LBinOp EqOp (LVar var) le) mp -> LExpr_holds e mp -> LExpr_holds (lexpr_subst e (<[ var := le]> ∅)) mp.
  Proof.
    Admitted.

  Definition EqpOp_LVal : forall v1 v2 mp, LExpr_holds (LBinOp EqOp (LVal v1) (LVal v2)) mp -> v1 = v2.
  Proof.
    Admitted.

End LExpr_embed.


Section AssertionsProperties.

  Lemma trnsl_assertion_w_lexpr_subst Γ assertion lexprs args arg_vals stk_id mp p1 p2:
    Forall2 
  (λ (expr : LExpr) (val0 : lang.val),
    interp_lexpr expr mp = Some (trnsl_val val0)
  ) lexprs arg_vals ->

  (trnsl_assertion Γ (subst assertion (list_to_map
    (zip args 
      lexprs
    )
  )) stk_id mp) = Some p1 ->

  (trnsl_assertion Γ (subst assertion (list_to_map
    (zip args 
      (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)
    )
  )) stk_id mp ) = Some p2
  
  -> (p1 -∗ p2).
  Proof. 
    Admitted.

  Lemma trnsl_assertion_w_lexpr_subst_r Γ assertion lexprs args arg_vals lvar_x ret_val stk stk_id mp p1 p2:
    fresh_lvar stk lvar_x ->
    Forall2 
  (λ (expr : LExpr) (val0 : lang.val),
    interp_lexpr expr mp = Some (trnsl_val val0)
  ) lexprs arg_vals ->

  (trnsl_assertion Γ (subst assertion (<["#ret_var":=LVar lvar_x]>(list_to_map
    (zip args 
      lexprs
    )
  ))) stk_id (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else
  mp x0)) = Some p1 ->

  (trnsl_assertion Γ (subst assertion (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map
    (zip args 
      (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)
    )
  ))) stk_id mp ) = Some p2
  
  -> (p2 -∗ p1).
  Proof. 
    Admitted.

  Lemma stack_free_assertion_trnsl Γ assertion stk_id stk_id' mp : 
    StackFree assertion -> 
    trnsl_assertion Γ assertion stk_id mp = trnsl_assertion Γ assertion stk_id' mp.
  Proof.
    Admitted.


  Lemma stack_free_assertion_subst assertion subst_map :
    StackFree assertion -> StackFree (subst assertion subst_map).
  Proof.
    Admitted.
  

End AssertionsProperties.

Lemma transport_cmra_update {A B} (p : A = B) (x y : (cmra_car A)) :
  x ~~> y → transport (f_equal cmra_car p) x ~~> transport (f_equal cmra_car p) y.
Proof.
  intros Hxy. subst. done.
Qed.

