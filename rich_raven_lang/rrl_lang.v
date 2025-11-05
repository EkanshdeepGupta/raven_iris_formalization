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
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.
Require Import Coq.Init.Datatypes.

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
Record InvRecord := Inv {
  inv_args: list var;
  inv_body: assertion;
}.

Global Parameter inv_map : gmap inv_name InvRecord.
(* Axiom inv_map_set : dom inv_map = inv_set. *)

Record PredRecord := Pred {
  pred_args: list var;
  pred_body: assertion;
}.

Global Parameter pred_map : gmap pred_name PredRecord.
(* Axiom pred_map_set : dom pred_map = pred_set. *)

Inductive StackFree : assertion → Prop :=
| SF_Proc proc_name proc_entry :
    StackFree (LProc proc_name proc_entry)
| SF_Expr p :
    StackFree (LExprA p)
| SF_Pure p :
    StackFree (LPure p)
| SF_Own e fld chunk :
    StackFree (LOwn e fld chunk)
| SF_GhostOwn e fld RAPAck chunk :
    StackFree (LGhostOwn e fld RAPAck chunk)
| SF_Forall v body :
    StackFree body →
    StackFree (LForall v body)
| SF_Exists v body :
    StackFree body →
    StackFree (LExists v body)
| SF_Impl cond body :
    StackFree body →
    StackFree (LImpl cond body)
| SF_And a1 a2 :
    StackFree a1 →
    StackFree a2 →
    StackFree (LAnd a1 a2)
| SF_Inv inv_name args inv_record :
    inv_map !! inv_name = Some inv_record →
    StackFree (subst (inv_record.(inv_body)) (list_to_map (zip inv_record.(inv_args) args))) →
    StackFree (LInv inv_name args)
| SF_Pred pred_name args pred_record :
    pred_map !! pred_name = Some pred_record →
    StackFree (subst (pred_record.(pred_body)) (list_to_map (zip pred_record.(pred_args) args))) →
    StackFree (LPred pred_name args).


(* Fixpoint StackFreeStr (F : assertion -d> bool) (a: assertion) : bool :=
match a with
| LProc proc_name proc_entry => true
| LStack σ => false
| LExprA p => true
| LPure p => true
| LOwn e fld chunk => true
| LGhostOwn e fld RAPAck chunk => true
| LForall v body => StackFreeStr F body
| LExists v body => StackFreeStr F body
| LImpl cond body => StackFreeStr F body
| LInv inv' args => 
    (* true *)
    match inv_map !! inv' with
    | Some inv_record => 
      let subst_map := list_to_map (zip inv_record.(inv_args) args) in
      F (subst inv_record.(inv_body) subst_map)
    | None => true
    end

| LPred pred args => 
    (* true *)
    match pred_map !! pred with 
    | Some pred_record =>
      let subst_map := list_to_map (zip pred_record.(pred_args) args) in

      F (subst pred_record.(pred_body) subst_map)
    | None => true
    end
| LAnd a1 a2 => (StackFreeStr F a1) && (StackFreeStr F a2)
end.

Definition StackFreePre (F : assertion -d> bool) :
     assertion -d> bool := λ a , StackFreeStr F a.

Global Instance StackFreePre_contractive : Contractive StackFreePre.
Proof. rewrite /StackFreePre.  intros n F1 F2 Hd a. 
  revert a.
  induction a; simpl; try auto.
  - destruct (inv_map !! inv_name0); try reflexivity.
    auto. f_equal.

  solve_contractive. repeat (f_contractive || f_equiv). solve_contractive.


Definition StackFree := fixpoint StackFreePre. *)

Global Parameter proc_map : gmap proc_name ProcRecord.
(* Axiom proc_map_set : dom proc_map = proc_set. *)
Axiom proc_args_unique : map_Forall (λ proc proc_entry, NoDup (proc_args_of proc_entry).*1 ) proc_map.

Axiom proc_spec_stack_free : 
  map_Forall (λ proc proc_entry, StackFree (proc_precond_of proc_entry) /\ StackFree (proc_postcond_of proc_entry) ) proc_map.


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

Lemma alloc_stmt_well_defined ρ x fld val fld_vals : 
  stmt_well_defined ρ (Alloc x ((fld, val) :: fld_vals)) -> stmt_well_defined ρ (Alloc x fld_vals).
Proof.
  intros H.
  inversion H.
  apply (AllocTp ρ x fld_vals).
  inversion H2. exact H7.
Qed.

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
      destruct v1 eqn:Hv1, v2 eqn:Hv2; try discriminate.
      - simpl; intros; inversion H. done.
      - simpl; intros; inversion H. done.
      - simpl; intros; inversion H. done.
      - simpl; intros. inversion H. destruct l, l0. simpl in H1; subst loc_car0. done.
    Qed. 

    Lemma trnsl_lval_trnsl_val_inverse y: trnsl_lval (trnsl_val y) = y.
    Proof.
      destruct y eqn:Hy; try simpl; try done.
      destruct l. simpl. done.
    Qed.

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
      | None', None' => Some' lang.SkipS
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
  | Spawn proc args => Some' (lang.Spawn proc args)
  
  | UnfoldPred pred args => None'
  | FoldPred pred args => None'
  | InvAccessBlock inv args body => (trnsl_atomic_block body false).1

  (* | UnfoldInv inv args => None'
  | FoldInv inv args => None' *)
  | Fpu e fld RAPack old_val new_val => None'
  end.

  Ltac proj_fst H := (apply f_equal with (f := fst) in H).

  (* Monotonicity for Some' *)
  Lemma trnsl_atomic_step_monotone (s : stmt)  :
    (forall stmt1 stmt2 stp1 stp2, 
        trnsl_atomic_block s true = (stmt1, stp1) ->
        trnsl_atomic_block s false = (stmt2, stp2) ->
        not (stmt1 = Error) ->
        stmt1 = stmt2 /\ (stp2 -> stp1)).
  Proof.
    induction s.
    all: intros.

    1: { (* Seq *)
      simpl in H, H0.

      destruct (trnsl_atomic_block s1 true) eqn:E1;
      destruct (trnsl_atomic_block s1 false) eqn:E2.
      specialize (IHs1 t t0 b b0 eq_refl eq_refl).

      destruct t eqn:Ht, t0 eqn:Ht0.
        all:
          try (specialize (IHs1 ltac:(intros Htemp'; discriminate)) as [IHs1stmt IHs1stp]; try done).
        all:
          try (inversion H; subst; contradiction).

      - destruct b, b0.
        ** rewrite H  in H0. inversion H0; subst. done.
        ** specialize (IHs2 stmt1 stmt2 stp1 stp2 H H0 H1) as IHs2Sp. done.
        ** exfalso. apply IHs1stp. done.
        ** rewrite H in H0. inversion H0; subst. done.

      - destruct b, b0; inversion IHs1stmt; subst.
        ** rewrite H in H0. inversion H0. done.
        ** destruct (trnsl_atomic_block s2 true) eqn:Htrnsl_s2;
          destruct (trnsl_atomic_block s2 false) eqn:Htrnsl_s2'.

          specialize (IHs2 t t0 b b0 eq_refl eq_refl).
          
          destruct t eqn:Ht, t0 eqn:Ht0. 
          all: 
            inversion H; inversion H0; subst; 
            try (specialize (IHs2 ltac:(intros Htemp; discriminate)) as [IHs2Stmt IHs2stp]; split; try done); 
            try done.
          
          inversion IHs2Stmt; subst. done.

        ** exfalso. apply IHs1stp; done.
        ** destruct (trnsl_atomic_block s2 false) eqn:Htrnsl_s2.
          destruct (trnsl_atomic_block s2 true) eqn:Htrnsl_s2'.

          specialize (IHs2 t0 t b0 b eq_refl eq_refl).

          destruct t0 eqn:Ht0, t eqn:Ht. 
          all: 
            inversion H; inversion H0; subst; 
            try (specialize (IHs2 ltac:(intros [Htemp Htemp']; discriminate)) as [IHs2Stmt IHs2stp]; split; try done); 
            try done.
    }

    1: { (* IfS *)
      simpl in H, H0.

        destruct (trnsl_atomic_block s1 true) eqn: E1.
        destruct (trnsl_atomic_block s1 false) eqn:E2.

        specialize (IHs1 t t0 b b0 eq_refl eq_refl).

        destruct t eqn:Ht, t0 eqn:Ht0.
        all:
          try (specialize (IHs1 ltac:(intros Htemp'; discriminate)) as [IHs1stmt IHs1stp]; try done).
        
        all:
          (destruct (trnsl_atomic_block s2 true) eqn:F1;
          destruct (trnsl_atomic_block s2 false) eqn:F2;
          specialize (IHs2 t1 t2 b1 b2 eq_refl eq_refl);  
          destruct t1 eqn:Ht1, t2 eqn:Ht2;
          try (specialize (IHs2 ltac:(intros Htemp; discriminate)) as [IHs2stmt IHs2stp]; try done)
          ).

        all:
            (inversion H; inversion H0; subst; split; try done).
        + destruct b0, b; intuition.
        + inversion IHs2stmt; subst; done.
        + destruct b0, b2; intuition.
        + inversion IHs1stmt; subst; done.
        + destruct b0, b2; auto.
        + inversion IHs1stmt; inversion IHs2stmt; subst; done.
        + destruct b0, b2; auto.
    }

    all: simpl in *; inversion H; inversion H0; subst; try done.
    
    apply IHs; done.
  Qed.

  Definition P_some (c : stmt) :=
    forall stmt' step_taken,
      (trnsl_atomic_block c step_taken).1 = Some' stmt' ->
      trnsl_stmt c = Some' stmt'.

  Definition P_none (c : stmt) :=
    forall step_taken,
      (trnsl_atomic_block c step_taken).1 = None' ->
      trnsl_stmt c = None'.

  Lemma trnsl_stmt_trnsl_atomic_block_some_none_mutual :
    forall c, (P_some c /\ P_none c).
  Proof.
    apply (stmt_ind (fun c => P_some c /\ P_none c)).
    all: intros; simpl in *.

    Ltac solve_split_case :=
      split;
      [ (* P_some *)
        intros stmt' step_taken H;
        simpl in H;
        destruct step_taken; try discriminate H; rewrite <- H; try done
      | (* P_none *)
        intros step_taken H;
        simpl in H;
        destruct step_taken; try discriminate H; try done
      ].

    (* All atomic steps *)
    all: try (solve_split_case).
        
    1: { (* Seq*)
      destruct H as [IHsome1 IHnone1].
      destruct H0 as [IHsome2 IHnone2].
      split.
      + (* --- P_some --- *)
        intros stmt' step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        simpl in H.
        ++ (* case (None', step1) *)
          unfold P_none in IHnone1. 
          proj_fst H1.
          specialize (IHnone1 step_taken H1) as Hs1.
          simpl. 
          rewrite Hs1.
          unfold P_some in IHsome2. apply IHsome2 in H. rewrite H. done.

        ++ discriminate H.
        
        ++ (* case (Some' s1', step1) *)
          unfold P_some in IHsome1.
          proj_fst H1.
          specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. 
          destruct (trnsl_atomic_block s2 step1) as [[| | ] step2] eqn:H2.
          ** proj_fst H2. 
            specialize (IHnone2 step1 H2) as Hs2. rewrite Hs2. done.

          ** discriminate H.

          **  proj_fst H2. specialize (IHsome2 s0 step1 H2) as Hs2. rewrite Hs2.
          simpl in H. rewrite H. done.

      + (* --- P_none --- *)
        intros step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        simpl in H.
        ++ (* case (None', step1) *)
          unfold P_none in IHnone1.
          proj_fst H1.
          specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2.
          apply IHnone2 in H. rewrite H. done.

        ++ (* case (Error, step1) *)
          discriminate H.

        ++ (* case (Some' s1', step1) *)
          unfold P_some in IHsome1.
          proj_fst H1.
          specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          destruct (trnsl_atomic_block s2 step1) as [[| | ] step2] eqn:H2;
          simpl in H.
          ** (* (None', step2) *)
              unfold P_none in IHnone2.
              proj_fst H2.
              specialize (IHnone2 step1 H2) as Hs2.
              rewrite Hs2. done.
          ** discriminate H.
          ** discriminate H.
    }
      
    1: { (* IfS *)
      destruct H as [IHsome1 IHnone1].
      destruct H0 as [IHsome2 IHnone2].
      split.

      + (* --- P_some --- *)
        intros stmt' step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        destruct (trnsl_atomic_block s2 step_taken) as [[| | ] step2] eqn:H2;
        simpl in H.

        ++ (* case: s1 = None', s2 = None' *)
          unfold P_none in IHnone1. proj_fst H1. specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2. proj_fst H2. specialize (IHnone2 step_taken H2) as Hs2.
          rewrite Hs2. simpl.
          rewrite H. reflexivity.

        ++ (* case: s1 = None', s2 = Error *) 
          discriminate H.
        
        ++ (* case: s1 = None', s2 = Some' s2' *)
          unfold P_none in IHnone1. proj_fst H1. specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. proj_fst H2. specialize (IHsome2 s step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

        ++ (* case: s1 = Error, s2 = None' *)
          discriminate H.

        ++ (* case: s1 = Error, s2 = Error *)
          discriminate H.
        
        ++ (* case: s1 = Error, s2 = Some' s *)
          discriminate H.

        ++ (* case: s1 = Some' s1', s2 = None' *)
          unfold P_some in IHsome1. proj_fst H1. specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2. proj_fst H2. specialize (IHnone2 step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

        ++ (* case: s1 = Some' s1', s2 = Error *)
          discriminate H.

        ++ (* case: s1 = Some' s, s2 = Some' s0 *)
          unfold P_some in IHsome1. proj_fst H1. specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. proj_fst H2. specialize (IHsome2 s0 step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

      + (* --- P_none --- *)
        intros step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        destruct (trnsl_atomic_block s2 step_taken) as [[| | ] step2] eqn:H2;
        simpl in H; try discriminate H.
    }

    1: { (* InvAccessBlock *)
      split.
      + (* P_some *)
        intros stmt' step_taken H1.
        simpl.
        simpl in H1.
        destruct step_taken; try discriminate H.
        * rewrite <- H1. simpl.
          destruct (trnsl_atomic_block body true) eqn:Hb1.
          destruct (trnsl_atomic_block body false) eqn:Hb2.
          simpl in H1.

          pose proof (trnsl_atomic_step_monotone body t t0 b b0 Hb1 Hb2) as HMono.
          specialize (HMono ltac:(intros Htemp; rewrite H1 in Htemp; discriminate)) as [Hbody _]. simpl. done.
        * rewrite <- H1. simpl. done.

      + (* P_none *) 
        intros step_taken H1.
        simpl in H1.
        simpl.
        destruct H as [HIndSome HIndNone].
        unfold P_none in HIndNone.
        destruct step_taken; rewrite <- H1; simpl; try done.
        * 
          destruct (trnsl_atomic_block body true) eqn:Hb1.
          destruct (trnsl_atomic_block body false) eqn:Hb2.
          simpl in H1.

          pose proof (trnsl_atomic_step_monotone body t t0 b b0 Hb1 Hb2) as HMono.
          specialize (HMono ltac:(intros Htemp; rewrite H1 in Htemp; discriminate)) as [Hbody _]. simpl. done.
    }
  Qed.

  Lemma trnsl_stmt_trnsl_atomic_block_some c stmt :
    (trnsl_atomic_block c false).1 = Some' stmt -> trnsl_stmt c = Some' stmt.
  Proof.
    pose proof (trnsl_stmt_trnsl_atomic_block_some_none_mutual c) as [Hsome _].
    unfold P_some in Hsome.
    specialize (Hsome stmt false). done.
  Qed.

  Lemma trnsl_stmt_trnsl_atomic_block_none c :
    (trnsl_atomic_block c false).1 = None' -> trnsl_stmt c = None'.
  Proof.
    pose proof (trnsl_stmt_trnsl_atomic_block_some_none_mutual c) as [_ Hnone].
    unfold P_none in Hnone.
    specialize (Hnone false). done.
  Qed.

  Lemma trnsl_atomic_block_atomicity stmt s stk_id:
    (trnsl_atomic_block stmt false).1 = Some' s -> Atomic WeaklyAtomic (to_rtstmt stk_id s).
  Proof.
    unfold Atomic. simpl.
    
  Admitted.
 

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


  Global Parameter Γ : Γ_type.

  Fixpoint trnsl_assertion_str (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) 
    (a: assertion) (stk_id: stack_id) (mp: symb_map) : 
     (iPropO Σ) :=      
      match a with
    | LProc p p_e => 
      match p_e with
        Proc args locals pre post body => 
          match trnsl_stmt body with
          | None' =>
            (proc_tbl_chunk p (
              lang.Proc p args locals lang.SkipS
            ))
          | Some' stmt =>
            (proc_tbl_chunk p (
              lang.Proc p args locals stmt
            ))
          | Error => 
            (False)%I
          end
      end
    | LStack σ => (stack_frame_own stk_id (symb_stk_to_stk_frm σ mp))
    | LExprA l_expr => 
      (⌜LExpr_holds l_expr mp⌝%I)
    
    | LPure p => (⌜ p ⌝%I)
    | LOwn l_expr fld chunk => 
      (∃ l: lang.loc, (
        ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ 
        (l#fld ↦{ 1 } (trnsl_lval chunk))
        )%I)%I

    | LGhostOwn l_expr fld RAPack chunk => 
      let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) := Γ RAPack in
      let chunkU := transport (Heq_car) chunk in
      let chunkGs := transport (f_equal cmra_car Heq_cmra) chunkU in 
      let HinG := inGs_inG i in

      (∃ l : lang.loc, (⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ (own (ghost_map l fld) chunkGs (inG0 := HinG)))%I)%I
    | LForall v body => 
       (∀ v':lang.val, (trnsl_assertion_str F body stk_id mp))%I

    | LExists v body => 
      (∃ v': val,
           (trnsl_assertion_str F body stk_id (λ x, if String.eqb x v then v' else mp x))
    )%I
    
    | LImpl cnd body => 
      (⌜LExpr_holds cnd mp⌝ -∗  (trnsl_assertion_str F body stk_id mp))%I

    | LInv inv' args => 
        match inv_map !! inv' with
        | Some inv_record => 
          let subst_map := list_to_map (zip inv_record.(inv_args) args) in

          (inv (inv_namespace_map inv') (F (subst inv_record.(inv_body) subst_map) stk_id mp))
        | None => True%I
        end

    | LPred pred args => 
        match pred_map !! pred with 
        | Some pred_record =>
          let subst_map := list_to_map (zip pred_record.(pred_args) args) in

          (▷ (F (subst pred_record.(pred_body) subst_map) stk_id mp))%I
        | None => True%I
        end

    | LAnd a1 a2 => 
      ( ((trnsl_assertion_str F a1 stk_id mp) ∗ (trnsl_assertion_str F a2 stk_id mp)))%I
    end.

  Definition trnsl_assertion_pre (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) :
     assertion -d> stack_id -d> symb_map -d> (iPropO Σ) := λ a stk_id mp, trnsl_assertion_str F a stk_id mp.

(* --- main contractiveness instance --- *)
Global Instance trnsl_assertion_pre_contractive : Contractive trnsl_assertion_pre.
Proof.
  intros n F G HFG a stk_id mp.
  unfold trnsl_assertion_pre.
  revert mp.
  induction a; simpl; try solve [reflexivity | repeat f_equiv; auto].
  -  (* LForall case *)
    intros mp. do 1 f_equiv. intros v'. apply IHa.
  - (* LExists case *)
    intros mp. do 1 f_equiv. intros v'. apply IHa.
  - (* LImpl case *)
    intros mp. f_equiv. apply IHa.
  - (* LInv case *)
    intros mp. 
    destruct (inv_map !! inv_name0); try reflexivity.
    apply inv_contractive.
    constructor.
    intros m Hlt.
    apply (dist_later_lt _ _ _ HFG _ Hlt).
  -  (* LPred case *)
    intros mp. 
    destruct (pred_map !! pred_name0); try reflexivity.
    (* Don't do f_equiv yet, work with the later directly *)
    apply later_contractive.
    constructor.
    intros m Hlt.
    apply (dist_later_lt _ _ _ HFG _ Hlt).
  - intros mp. f_equiv. { apply IHa1. } {apply IHa2. }
Qed.

Definition trnsl_assertion' := fixpoint trnsl_assertion_pre. 

Lemma trnsl_assertion_unfold a stk mp :
  trnsl_assertion' a stk mp ≡ trnsl_assertion_pre trnsl_assertion' a stk mp.
Proof. apply (fixpoint_unfold trnsl_assertion_pre a stk mp). Qed.

Lemma trnsl_inv_validity' inv' args stk mp :
  match inv_map !! inv' with
  | Some inv_rec =>
      let subst_map := list_to_map (zip inv_rec.(inv_args) args) in
      inv (inv_namespace_map inv')
          (trnsl_assertion' (subst inv_rec.(inv_body) subst_map) stk mp)
      ⊣⊢ trnsl_assertion' (LInv inv' args) stk mp
  | None => true
  end.
  Proof.
    destruct (inv_map !! inv') eqn:HInv; try done.
    simpl.
    setoid_rewrite trnsl_assertion_unfold.
  simpl. rewrite HInv. setoid_rewrite <- trnsl_assertion_unfold. done.
Qed.


Lemma trnsl_pred_validity' pred args stk_id mp :
  match pred_map !! pred with
  | Some pred_rec => 
    let subst_map := list_to_map (zip pred_rec.(pred_args) args) in

    (▷ (trnsl_assertion' (subst pred_rec.(pred_body) subst_map) stk_id mp))%I ≡ trnsl_assertion' (LPred pred args) stk_id mp
  | None => true
  end
.
Proof.
  destruct (pred_map !! pred) eqn:HPred; try done.
  simpl.
  setoid_rewrite trnsl_assertion_unfold.
  simpl. rewrite HPred. setoid_rewrite <- trnsl_assertion_unfold. done.
Qed.  

Definition trnsl_assertion := trnsl_assertion'.


  Definition entails P Q := forall stk_id mp, ∃ P' Q', trnsl_assertion P stk_id mp = P' /\ trnsl_assertion Q stk_id mp = Q' /\ (P' ⊢  Q')%I.

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
  assertion -> nat ->
      stmt -> maskAnnot ->
  assertion -> nat ->  Prop :=

  | VarAssignmentRule ρ σ ι stk mask v lv e lexpr :
    trnsl_expr_lExpr stk e = Some lexpr ->
    fresh_lvar stk lv ->
    stk_type_compat ρ σ stk -> 
    RavenHoareTriple ρ σ 
      (LStack stk) ι
        (Assign v e) mask 
      (LExists lv 
        (LAnd 
          (LStack (<[v := lv]> stk))
          (LExprA (LBinOp EqOp (LVar lv) lexpr))
        )
      ) (ι+1)
  
  | HeapReadRule ρ σ ι stk mask x e val fld lexpr_e lvar_x  :
    trnsl_expr_lExpr stk e = Some lexpr_e ->
    fresh_lvar stk lvar_x ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn lexpr_e fld val)) ι
        (FldRd x e fld) mask
      (LExists lvar_x (LAnd 
        (LStack (<[x := lvar_x]> stk)) 
        (LAnd 
          (LOwn lexpr_e fld val) 
          (LExprA (LBinOp EqOp (LVar lvar_x) (LVal val)))
        )
      )) (ι+1)

  | HeapWriteRule ρ σ ι stk mask v fld e old_val new_val lv :
    stk !! v = Some lv ->
    trnsl_expr_lExpr stk e = Some (LVal new_val) ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn (LVar lv) fld old_val)) ι
        (FldWr v fld e) mask
      (LAnd (LStack stk) (LOwn (LVar lv) fld new_val)) (ι+1)
  
    
  | HeapAllocRule ρ σ ι stk mask x fld_vals lvar_x :
    fresh_lvar stk lvar_x ->
    NoDup fld_vals.*1 ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
       (LStack stk) ι
        (Alloc x fld_vals) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (field_list_to_assertion (LVar lvar_x) fld_vals))) (ι+1)

  | ProcCallRuleRet ρ σ ι stk mask x proc_name args lexprs lvar_x proc_record :
    fresh_lvar stk lvar_x ->
    proc_map !! proc_name = Some proc_record ->
    length args = length (proc_args_of proc_record) ->
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip (proc_args_of proc_record).*1 lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LProc proc_name proc_record) (subst (proc_precond_of proc_record) subst_map))) ι
        (Call x proc_name args) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (subst (proc_postcond_of proc_record) (<[ "#ret_var" := LVar lvar_x]> subst_map)))) (ι+1)

  | SequenceRule ρ σ mask ι1 ι2 ι3 a1 c1 a2 c2 a3 :
    RavenHoareTriple ρ σ
      a1 ι1
        c1 mask
      a2 ι2
    ->
    RavenHoareTriple ρ σ
      a2 ι2
        c2 mask
      a3 ι3
    ->
    RavenHoareTriple ρ σ
      a1 ι1
        (Seq c1 c2) mask
      a3 ι3

  | CondRule ρ σ ι1 ι2 ι3 stk1 stk2 mask e s1 s2 p q lexpr :
    trnsl_expr_lExpr stk1 e = Some lexpr ->
    inf_expr ρ e = Some TpBool ->
    stk_type_compat ρ σ stk1 ->
    stk_type_compat ρ σ stk2 ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (lexpr))) ) ι1
        s1 mask
      (LAnd (LStack stk2) q) ι2
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (LUnOp NotBoolOp lexpr)))) ι1
        s2 mask
      (LAnd (LStack stk2) q) ι3
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) p) ι1
        (IfS e s1 s2) mask
      (LAnd (LStack stk2) q) (Nat.min ι2 ι3)

  | InvAccessBlockRule ρ σ ι1 ι2 stk mask inv args stmt inv_record p q lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    inv ∈ mask ->
    inv_map !! inv = Some inv_record ->
    stk_type_compat ρ σ stk ->
    ι1 > 0 ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) p)) (ι1-1)
        stmt (mask ∖ {[inv]})
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) q)) ι2 ->
    
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) p)) ι1
        (InvAccessBlock inv args stmt ) mask
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) q)) ι2

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

  | PredUnfoldRule ρ σ ι stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LPred pred lexprs)) (ι+1)
        (UnfoldPred pred args) mask
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map)) ι

  | PredFoldRule ρ σ ι stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    stk_type_compat ρ σ stk ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map)) ι
        (FoldPred pred args) mask
      (LAnd (LStack stk) (LPred pred lexprs)) ι

  | FPURule ρ σ ι stk mask e l_expr fld RAPack old_val new_val :
    trnsl_expr_lExpr stk e = Some l_expr ->
    (RAPack.(RA_inst) ).(fpuValid) old_val new_val ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack old_val)) ι
        (Fpu e fld RAPack old_val new_val) mask
        (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack new_val)) ι

  | FrameRule ρ σ mask ι1 ι2 s p q r :
    RavenHoareTriple ρ σ
      p ι1
        s mask
      q ι2
    ->
    RavenHoareTriple ρ σ
      (LAnd p r) ι1
        s mask
      (LAnd q r) ι2
  
  | WeakeningRule ρ σ mask ι1 ι2 p p' q q' c :
    RavenHoareTriple ρ σ
      p ι1
        c mask
      q ι2
    ->
    entails p' p ->
    entails q q' ->

    RavenHoareTriple ρ σ
      p' ι1
        c mask
      q' ι2

  | SkipRule ρ σ ι stk mask p :
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) p) ι
        SkipS mask
      (LAnd (LStack stk) p) (1+ι)

  | CASSuccRule ρ σ ι stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val new_val :
    fresh_lvar stk lvar_v ->
    inf_expr ρ e1 = Some (TpLoc) ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val) ->
    trnsl_expr_lExpr stk e3 = Some (LVal new_val) ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LOwn lexpr1 fld old_val)) ι
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld new_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool true)))))) ) (ι+1)

  | CASFailRule ρ σ ι stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val old_val2 :
    fresh_lvar stk lvar_v ->
    inf_expr ρ e1 = Some (TpLoc) ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val2) ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LUnOp NotBoolOp (LBinOp EqOp (LVal old_val) (LVal old_val2)))))) ι
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool false))))))) (ι+1)
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

  Lemma trnsl_assertion_w_lexpr_subst assertion lexprs args arg_vals stk_id mp p1 p2:
    Forall2 
  (λ (expr : LExpr) (val0 : lang.val),
    interp_lexpr expr mp = Some (trnsl_val val0)
  ) lexprs arg_vals ->

  (trnsl_assertion (subst assertion (list_to_map
    (zip args 
      lexprs
    )
  )) stk_id mp) = p1 ->

  (trnsl_assertion (subst assertion (list_to_map
    (zip args 
      (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)
    )
  )) stk_id mp ) = p2
  
  -> (p1 -∗ p2).
  Proof. 
    Admitted.

  Lemma trnsl_assertion_w_lexpr_subst_r assertion lexprs args arg_vals lvar_x ret_val stk stk_id mp p1 p2:
    fresh_lvar stk lvar_x ->
    Forall2 
  (λ (expr : LExpr) (val0 : lang.val),
    interp_lexpr expr mp = Some (trnsl_val val0)
  ) lexprs arg_vals ->

  (trnsl_assertion (subst assertion (<["#ret_var":=LVar lvar_x]>(list_to_map
    (zip args 
      lexprs
    )
  ))) stk_id (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else
  mp x0)) = p1 ->

  (trnsl_assertion (subst assertion (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map
    (zip args 
      (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)
    )
  ))) stk_id mp ) = p2
  
  -> (p2 -∗ p1).
  Proof. 
    Admitted.



  Definition stack_free_prop (F : assertion -d> stack_id -d> symb_map -d> iPropO Σ) :=
  ∀ a stk stk' mp,
    StackFree a →
    trnsl_assertion_str F a stk mp = trnsl_assertion_str F a stk' mp.

  Lemma stack_free_prop_closed :
  ∀ F, stack_free_prop F → stack_free_prop (trnsl_assertion_pre F).
  Proof.
    intros F IH a.
    (* unfold trnsl_assertion_pre. *)
    (* simpl. *)
    induction a; intros stk stk' mp Hsf; simpl in *; try reflexivity; try done.
      (* try (destruct (StackFree a1 && StackFree a2) eqn:Hsf2; simpl in *; ...). *)
    - inversion Hsf.
    - (* LForall*) apply f_equal.   (* LInv *)
      inversion Hsf.
      rewrite (IHa stk stk' mp H0). done.
    - (* LExists *) apply f_equal. extensionality v'.
    inversion Hsf.
      rewrite (IHa stk stk' (λ x : lvar, if (x =? v)%string then v' else mp x) H0). done.
      
    - inversion Hsf. (* LImpl *) rewrite (IHa stk stk' mp H0). done.
    - (* LInv *) 
      destruct (inv_map !! inv_name0) as [inv_record|] eqn:Hinv; simpl; [|reflexivity].
      unfold trnsl_assertion_pre.

      rewrite (IH (subst inv_record.(inv_body) _ ) stk stk' mp); auto.
      inversion Hsf. rewrite Hinv in H1. inversion H1. subst inv_record0. exact H2.

    - (* LPred *)
      rewrite /trnsl_assertion_str.
      destruct (pred_map !! pred_name0) as [pred_record|] eqn:Hpred; simpl; [|reflexivity].
      unfold trnsl_assertion_pre.
      rewrite (IH (subst pred_record.(pred_body) _) stk stk' mp); auto.
      inversion Hsf. rewrite Hpred in H1. inversion H1. subst pred_record0. exact H2.

    - (* LAnd *)    
      inversion Hsf; subst a0 a3.
      rewrite (IHa1 stk stk' mp H1) (IHa2 stk stk' mp H2). reflexivity.
  Qed.

(* instantiate with the fixed point *)
(* Lemma stack_free_assertion_trnsl a stk stk' mp :
  StackFree a ->
  trnsl_assertion a stk mp = trnsl_assertion a stk' mp.
Proof.
Admitted. *)
  (* intros HSF.
  unfold trnsl_assertion.
   (* trnsl_assertion'. *)
  rewrite trnsl_assertion_unfold.
  (* Induction on the StackFree derivation *)
  induction HSF.

  - rewrite fixpoint_unfold. (* Case for each constructor of StackFree *)
    
    (* Try to simplify the fixpoint directly without unfolding *)
    (* The idea is that for stack-free assertions, the computation
       doesn't depend on the stack parameter *)
    
    (* You may need to use functional extensionality or 
       properties specific to how trnsl_assertion_str is defined *)
Admitted. *)


  Lemma stack_free_assertion_trnsl assertion stk_id stk_id' mp : 
    StackFree assertion -> 
    trnsl_assertion assertion stk_id mp = trnsl_assertion assertion stk_id' mp.
  Proof.
  Admitted.
    (* revert assertion.
    induction assertion0.
    - intros. unfold trnsl_assertion. unfold trnsl_assertion'.
    (* rewrite /trnsl_assertion_pre. *)
    rewrite (leibniz_equiv (fixpoint trnsl_assertion_pre (LProc proc_name0 proc_entry) stk_id mp) (fixpoint trnsl_assertion_pre (LProc proc_name0 proc_entry) stk_id' mp)).
    rewrite (fixpoint_unfold (trnsl_assertion_str : _ -> _ -> _ -> iPropO Σ)).

    rewrite (fixpoint_unfold trnsl_assertion_pre).

    rewrite fixpoint_unfold.
 rewrite trnsl_assertion_unfold.
    simpl. done.
  Admitted. *)


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

