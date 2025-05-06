From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From stdpp Require Import countable.
Require Import Eqdep_dec.

From stdpp Require Export strings.
From stdpp Require Import gmap list sets.
From iris.algebra Require Import cmra.
From iris.heap_lang Require Import lang.
From iris.heap_lang Require Import locations.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
(* From iris.prelude Require Import options. *)
(* From iris.algebra Require Import reservation_map agree frac. *)
(* From iris.algebra Require Export dfrac. *)
(* From iris.bi.lib Require Import fractional. *)
(* From iris.proofmode Require Import proofmode. *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Context `{!heapGS Σ}.

Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp 
| EqOp | NeOp | LtOp
| GtOp | LeOp | GeOp
| AndOp | OrOp.

Inductive un_op : Set :=
| NotBoolOp | NegOp.

Definition var := string.

Definition proc_name := string.
Global Parameter proc_set : gset proc_name.

Definition pred_name := string.
Global Parameter pred_set : gset pred_name.

Definition inv_name := string.
Global Parameter inv_set : gset inv_name.

(* How to connect Resource Algebras to ucmras, without triggering universe inconsistencies *)
Class ResourceAlgebra (A: Type) := {
  comp : A -> A -> A;
  frame : A -> A -> A;
  fpuValid : A -> A -> bool;
  (* RA Axioms *)
  (* ra_ucmra : ucmra; *)
  (* ra_ucmra_map : A -> ra_ucmra; *)
}.

Global Declare Instance RAEq : forall A: Type, EqDecision (ResourceAlgebra A).
Global Declare Instance RACountable : forall A: Type, Countable (ResourceAlgebra A).

Record RA_Pack := {
  RA_carrier : Type;
  RA_carrier_eqdec :> EqDecision RA_carrier;
  RA_inst :> ResourceAlgebra RA_carrier;
}.

Global Axiom ra_eq_dec :  EqDecision RA_Pack .
(* Global Axiom ra_countable_dec :  Countable RA_Pack . *)

Parameter ResourceAlgebras : list RA_Pack.


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

Inductive typ :=
| TpInt | TpLoc | TpBool.

Definition fld_name := string.
Parameter fld_set : gset fld_name.

Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

Inductive val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc)
| LitRAElem : forall (r : RA_Pack), RA_carrier r -> val.

Inductive RavenExpr :=
| Var (x : var)
| Val (v : val)
| UnOp (op : un_op) (e : RavenExpr)
| BinOp (op : bin_op) (e1 e2 : RavenExpr)
.

Inductive LExpr :=
| LVar (x : var)
| LVal (v : val)
| LUnOp (op : un_op) (e : LExpr)
| LBinOp (op : bin_op) (e1 e2 : LExpr)
(* | LIfE (e1 e2 e3 : LExpr) *)
.

Fixpoint rexpr_lexpr_subst (expr : RavenExpr) (subst_map : gmap var LExpr) :=
match expr with
| Var x => match subst_map !! x with
    | None => LVar x
    | Some e => e
    end
| Val v => LVal v
| UnOp op e => LUnOp op (rexpr_lexpr_subst e subst_map)
| BinOp op e1 e2 => LBinOp op (rexpr_lexpr_subst e1 subst_map) (rexpr_lexpr_subst e2 subst_map)
(* | IfE e1 e2 e3 => LIfE (rexpr_lexpr_subst e1 subst_map) (rexpr_lexpr_subst e2 subst_map) (rexpr_lexpr_subst e3 subst_map) *)
end.

Global Instance ra_carrier_eqdec_instance (r : RA_Pack) : EqDecision (RA_carrier r) :=
  RA_carrier_eqdec r.

Global Instance val_eq : EqDecision val.
Proof.
  (* intros x y.
  destruct x; destruct y. *)
  (* solve_decision. *)
  refine (fun x y =>
    match x, y with
    | LitBool b1, LitBool b2 => cast_if (decide (b1 = b2))
    | LitInt i1, LitInt i2 => cast_if (decide (i1 = i2))
    | LitUnit, LitUnit => left eq_refl
    | LitLoc l1, LitLoc l2 => cast_if (decide (l1 = l2))
    | LitRAElem r1 a1, LitRAElem r2 a2 =>
        match ra_eq_dec r1 r2 with
        | left Heq =>
            (* r1 = r2, so carriers are same, can cast and decide equality on carrier elements *)
            cast_if (decide (eq_rect r1 (fun r => RA_carrier r) a1 r2 Heq = a2))

        | right _ => right _
        end
    | _, _ => right _
    end). 
  all: try by f_equal.
  all: try intros Heq; inversion Heq; auto.
  - subst. simpl. by f_equal.
  - subst. simpl in n. intros Heq.
  inversion Heq as [H1].
  assert (a1 = a2) by (apply (inj_pair2_eq_dec _ ra_eq_dec), H1).
  done.
Qed.

(* TODO: To be proved *)
Global Declare Instance LExpr_Eq : EqDecision LExpr.
Global Declare Instance LExpr_Countable : Countable LExpr.

Global Declare Instance val_countable : Countable val.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : RavenExpr) *)
| IfS (e : RavenExpr) (s1 s2 : stmt)
| Assign (v : var) (e : RavenExpr)
(* | Free (e : RavenExpr) *)
| SkipS
| StuckS (* stuck statement *)
| ExprS (e : RavenExpr)
| Call (v : option var) (proc : proc_name) (args : list RavenExpr)
| FldWr (e1 : RavenExpr) (fld : fld_name) (e2 : RavenExpr)
| FldRd (v : var) (e : RavenExpr) (fld : fld_name)
| CAS (v : var) (e1 : RavenExpr) (fld : fld_name) (e2 : RavenExpr) (e3 : RavenExpr)
| Alloc (e : RavenExpr) (fs: list (fld_name * val))
| Spawn (proc : proc_name) (args : list RavenExpr)
| UnfoldPred (pred : pred_name) (args : list RavenExpr)
| FoldPred (pred : pred_name) (args : list RavenExpr)
| UnfoldInv (inv: inv_name) (args : list RavenExpr)
| FoldInv (inv: inv_name) (args : list RavenExpr)
| Fpu (e : RavenExpr) (fld : fld_name) (old_val : val) (new_val : val)
.

Inductive assertion (expr: Type) :=
| EExpr (p: expr)
| EPure (p : Prop)
| EOwn (e: expr) (fld: fld_name) (chunk: val)
| EForall (v : var) (body : assertion expr)
| EExists (v : var) (body : assertion expr)
| EImpl (cond : expr) (body : assertion expr)
| EInv (inv_name : inv_name) (args : list expr)
| EPred (pred_name : pred_name) (args : list expr)
| EAnd (assert1 : (assertion expr)) (assert2 : (assertion expr))
.

Definition r_assertion := assertion RavenExpr.
Definition l_assertion := assertion LExpr.
Definition LExprA := EExpr LExpr.
Definition LPure := EPure LExpr.
Definition LOwn := EOwn LExpr.
Definition LForall := EForall LExpr.
Definition LExists := EExists LExpr.
Definition LImpl := EImpl LExpr.
Definition LInv := EInv LExpr.
Definition LPred := EPred LExpr.
Definition LAnd := EAnd LExpr.

Fixpoint subst (ra: r_assertion) (mp: gmap var LExpr) : l_assertion := match ra with
| EExpr _ e => LExprA (rexpr_lexpr_subst e mp)
| EPure _ p => LPure p
| EOwn _ e fld chunk => LOwn (rexpr_lexpr_subst e mp) fld chunk
| EForall _ vars body => LForall vars (subst body mp)
| EExists _ vars body => LExists vars (subst body mp)
| EImpl _ cond body => LImpl (rexpr_lexpr_subst cond mp) (subst body mp)
| EInv _ inv_name args => 
    LInv inv_name (map (fun expr => rexpr_lexpr_subst expr mp) args)
| EPred _ pred_name args =>
    LPred pred_name (map (fun expr => rexpr_lexpr_subst expr mp) args)
| EAnd _ a1 a2 => LAnd (subst a1 mp) (subst a2 mp)
end.

Definition trnsl_r_assertion_l_assertion (ra: r_assertion) : l_assertion := 
  subst ra ∅.

Record ProcRecord := Proc {
  proc_args: list var;
  proc_precond : r_assertion;
  proc_postcond : r_assertion;
  ret_var : var;
  body : stmt;
}.

Global Parameter proc_map : gmap proc_name ProcRecord.
Axiom proc_map_set : dom proc_map = proc_set.

Record InvRecord := Inv {
  inv_args: list var;
  inv_body: r_assertion;
}.

Global Parameter inv_map : gmap inv_name InvRecord.
Axiom inv_map_set : dom inv_map = inv_set.

Record PredRecord := Pred {
  pred_args: list var;
  pred_body: r_assertion;
}.

Global Parameter pred_map : gmap pred_name PredRecord.
Axiom pred_map_set : dom pred_map = pred_set.

Inductive expr_well_defined : RavenExpr -> Prop :=
| Constr e :
  expr_well_defined e.

Inductive stmt_well_defined : stmt -> Prop := 
| SeqTp s1 s2 :
  stmt_well_defined s1 ->
  stmt_well_defined s2 ->
  stmt_well_defined (Seq s1 s2)
(* | ReturnTp e : 
    expr_well_defined e ->
    stmt_well_defined (Return e) *)
| IfSTp e s1 s2 : 
    expr_well_defined e -> 
    stmt_well_defined s1 ->
    stmt_well_defined s2 -> 
    stmt_well_defined (IfS e s1 s2)
| AssignTp v e: 
    expr_well_defined e ->
    stmt_well_defined (Assign v e)
(* | FreeTp e: 
    expr_well_defined e ->
    stmt_well_defined (Free e) *)
| SkipSTp : stmt_well_defined (SkipS)
| StuckSTp : stmt_well_defined (StuckS)
| ExprSTp e: 
    expr_well_defined e -> 
    stmt_well_defined (ExprS e)
| CallTp v proc args: 
    proc ∈ proc_set -> 
    (Forall (fun arg => expr_well_defined arg) args) ->
    stmt_well_defined (Call v proc args)
| FldWrTp e1 fld e2: 
    (fld ∈ fld_set) ->
    expr_well_defined e1 -> 
    expr_well_defined e2 -> 
    stmt_well_defined (FldWr e1 fld e2)
| FldRdTp v e fld: 
    fld ∈ fld_set ->
    expr_well_defined e ->
    stmt_well_defined (FldRd v e fld)
| CASTp v e1 fld e2 e3: 
    fld ∈ fld_set ->
    expr_well_defined e1 ->
    expr_well_defined e2 ->
    expr_well_defined e3 ->
    stmt_well_defined (CAS v e1 fld e2 e3)
| AllocTp e fs: 
    expr_well_defined e ->
    Forall (fun fld_v => (fst fld_v) ∈ fld_set) fs ->
    stmt_well_defined (Alloc e fs)
| SpawnTp proc args: 
    proc ∈ proc_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (Spawn proc args)
| UnfoldPredTp pred args : 
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (UnfoldPred pred args)
| FoldPredTp pred args : 
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (FoldPred pred args)
| UnfoldInvTp inv args : 
    inv ∈ inv_set -> 
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (UnfoldInv inv args)
| FoldInvTp inv args : 
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (FoldInv inv args)
| FpuTp e fld old_val new_val : 
    fld ∈ fld_set ->
    expr_well_defined e ->
    stmt_well_defined (Fpu e fld old_val new_val)
.

Section AtomicAnnotations.
  Parameter inv_namespace_map : inv_name -> namespace.

  Axiom inv_namespace_disjoint : forall inv1 inv2 : inv_name, inv1 ∈ inv_set -> inv2 ∈ inv_set -> (inv_namespace_map inv1) ## (inv_namespace_map inv2).

  Inductive AtomicStep : Type :=
  | Closed
  | Opened (S : gset (inv_name * list LExpr))
  | Stepped (S : gset (inv_name * list LExpr))
  .

  Definition AtomicAnnotation : Type := (gset inv_name * AtomicStep).

  Definition oneAtomicStep i1 i2 := match i1, i2 with
  | Closed, Closed => true
  | (Opened s1), (Stepped s2) => bool_decide (s1 = s2)
  | _, _ => false
  end.
End AtomicAnnotations.

Section Translation.
  (* Have to include all the resource algebras  *)

    Definition trnsl_val (v: val) : heap_lang.val :=
    match v with
    | LitBool b => LitV (heap_lang.LitBool b)
    | LitInt i => LitV (heap_lang.LitInt i)
    | LitUnit => LitV (heap_lang.LitUnit)
    | LitLoc l => LitV (heap_lang.LitLoc (heap_lang.locations.Loc l.(loc_car)))
    | LitRAElem RA val => LitV (heap_lang.LitBool true)
    end.

    Definition trnsl_expressions (e: LExpr) : heap_lang.expr := match e with
    | LVar x => (heap_lang.Var x)
    | LVal v =>
        heap_lang.Val (trnsl_val v)
    | LUnOp op e => heap_lang.Val (LitV (heap_lang.LitBool true))
    | LBinOp op e1 e2 => heap_lang.Val (LitV (heap_lang.LitBool true))
    end.

    Fixpoint trnsl_assertions (a : l_assertion) : iProp Σ := match a with
    | EExpr _ l_expr => ⌜(trnsl_expressions l_expr) = #true⌝
    | EPure _ p => ⌜ p ⌝
    | EOwn _ l_expr fld (LitRAElem RA ra_elem) => 
      (* True *)
      ∃ l: locations.loc, ⌜(trnsl_expressions l_expr) = heap_lang.Val (LitV (heap_lang.LitLoc l))⌝ ∗ l ↦ #0
    | EForall _ v body => 
      ∀ v':heap_lang.val, (trnsl_assertions (body))
      (* ∀ vs, (trnsl_assertions body) *)
      (* True *)
    | EExists _ v body => ∃ v': heap_lang.val, (trnsl_assertions body)
    | EImpl _ cnd body => 
      ⌜((trnsl_expressions cnd) = #true)⌝ -∗ (trnsl_assertions body)
      (* True *)
    | EInv _ inv args => 
      match inv_map !! inv with
      | Some inv_record => 
        let subst_map := list_to_map (zip inv_record.(inv_args) args) in
        let subst_body := subst inv_record.(inv_body) subst_map in

        (* (invariants.inv (inv_namespace_map inv) (trnsl_assertions subst_body)) *)

        False
      | None => False
      end
      (* False *)
    | EPred _ pred args => True
    | EAnd _ a1 a2 => (trnsl_assertions a1) ∗ (trnsl_assertions a2)
    |_ => True
    end.

  Definition entails P Q := trnsl_assertions P ⊢ trnsl_assertions Q.

  Definition stack: Type := gmap var LExpr.

  Fixpoint trnsl_ravenExpr_lExpr (stk: stack) (e: RavenExpr) :=
  match e with
  | Var x => match stk !! x with
             | Some v => Some v
             | None => None
             end
  | Val v => Some (LVal v)
  | UnOp op e => 
      match trnsl_ravenExpr_lExpr stk e with
      | Some le => Some (LUnOp op le)
      | None => None
      end
  | BinOp op e1 e2 => 
    match (trnsl_ravenExpr_lExpr stk e1), (trnsl_ravenExpr_lExpr stk e2) with
    | Some le1, Some le2 => Some (LBinOp op le1 le2)
    | _, _ => None
    end
  (* | IfE e1 e2 e3 => 
    match (trnsl_ravenExpr_lExpr stk e1), (trnsl_ravenExpr_lExpr stk e2), (trnsl_ravenExpr_lExpr stk e3) with
    | Some le1, Some le2, Some le3 => Some (LIfE le1 le2 le3)
    | _, _, _ => None
    end *)
  end.

  Fixpoint trnsl_stmt (s : stmt) stk : option heap_lang.expr := match s with
  | Seq s1 s2 => 
    match trnsl_stmt s1 stk, trnsl_stmt s2 stk with
    | None, None => None
    | Some s1, None => Some s1
    | None, Some s2 => Some s2
    | Some s1', Some s2' => Some (Lam BAnon s2' s1' )
    end
  | IfS e s1 s2 => match (trnsl_ravenExpr_lExpr stk e) with
    | Some lexpr => 
      match (trnsl_stmt s1 stk), (trnsl_stmt s2 stk) with
      | None, None => None
      | Some s1, None => Some (heap_lang.If (trnsl_expressions lexpr) s1 Skip)
      | None, Some s2 => Some (heap_lang.If (trnsl_expressions lexpr) Skip s2)
      | Some s1, Some s2 => Some (heap_lang.If (trnsl_expressions lexpr) s1 s2) 
      end
    | None => None
    end
  | Assign v e => None
  | SkipS => Some (Skip)
  | StuckS => None
  | ExprS e => 
    match (trnsl_ravenExpr_lExpr stk e) with
    | Some lexpr => Some (trnsl_expressions lexpr)
    | None => None
    end
  | Call v proc args => None
  | FldWr e1 fld e2 => None
  | FldRd v e1 fld => None
  | CAS v e1 fld e2 e3 => None
  | Alloc e fs => None
  | Spawn proc args => None
  
  | UnfoldPred pred args => None
  | FoldPred pred args => None
  | UnfoldInv inv args => None
  | FoldInv inv args => None
  | Fpu e fld old_val new_val => None
  (* | _ => (None) *)
  end.

End Translation.


Section RavenLogic.

  (* Inductive RavenHoareTriple :=
  | HoareTriple (p: assertion) (a1: AtomicAnnotation) (s: stmt) (q: assertion) (a2: AtomicAnnotation). *)



  Inductive RavenHoareTriple : 
  stack -> l_assertion -> AtomicAnnotation -> 
      stmt -> 
  stack -> l_assertion -> AtomicAnnotation -> Prop :=
  | mkHoareTriple : forall stk p a1 s stk' q a2, RavenHoareTriple stk p a1 s stk' q a2.



  Definition fresh_lvar (stk: stack) v := forall v', not (stk !! v' = Some (LVar v)). 

  Definition VarAssignmentRule stk i1 i2 mask v v2 e lexpr :=
    oneAtomicStep i1 i2 ->
    trnsl_ravenExpr_lExpr stk e = Some lexpr ->
    fresh_lvar stk v2 ->
    RavenHoareTriple 
      stk (EPure _ True) (mask, i1) 
        (Assign v e) 
      (<[v := LVar v2]> stk) (LExprA (LBinOp EqOp (LVar v2) lexpr)) (mask, i2).

  Definition HeapReadRule stk i1 i2 mask x e val fld lexpr_e lvar_x  :=
    oneAtomicStep i1 i2 ->
    trnsl_ravenExpr_lExpr stk e = Some lexpr_e ->
    fresh_lvar stk lvar_x ->
    RavenHoareTriple 
      stk (LOwn lexpr_e fld val) (mask, i1) 
        (FldRd x e fld)
      (<[x := LVar lvar_x]> stk) (LAnd (LOwn lexpr_e fld val) (LExprA (LBinOp EqOp (LVar lvar_x) (LVal val)))) (mask, i2).


  (* Need e2 to resolve to an LVal. Should own predicates also take LExpr for values? *)
  Definition HeapWriteRule stk i1 i2 mask e1 fld e2 old_val new_val lexpr1 :=
    oneAtomicStep i1 i2 ->
    trnsl_ravenExpr_lExpr stk e1 = Some lexpr1 ->
    trnsl_ravenExpr_lExpr stk e2 = Some (LVal new_val) ->
    RavenHoareTriple
      stk (LOwn lexpr1 fld old_val) (mask, i1)
        (FldWr e1 fld e2)
      stk (LOwn lexpr1 fld new_val) (mask, i2).
  
  Fixpoint field_list_to_assertion lexpr fld_vals  := match fld_vals with
  | [] => LPure true
  | (fld,val) :: fld_vals => LAnd (LOwn lexpr fld val) (field_list_to_assertion lexpr fld_vals)
  end.

  Definition HeapAllocRule stk i1 i2 mask x fld_vals lvar_x :=
    oneAtomicStep i1 i2 ->
    fresh_lvar stk lvar_x ->
    RavenHoareTriple
      stk (LPure true) (mask, i1)
        (Alloc (Var x) fld_vals)
      (<[x := LVar lvar_x]> stk) (field_list_to_assertion (LVar lvar_x) fld_vals) (mask, i2).
  
  Definition ProcCallRuleRet stk i mask x proc_name args lexprs lvar_x proc_record :=
    i = Closed ->
    fresh_lvar stk lvar_x ->
    proc_map !! proc_name = Some proc_record ->
    length args = length proc_record.(proc_args) ->
    (map (fun arg => trnsl_ravenExpr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    let subst_map := list_to_map (zip proc_record.(proc_args) lexprs) in
    RavenHoareTriple
      stk (subst proc_record.(proc_precond) subst_map) (mask, i)
        (Call (Some x) proc_name args)
      (<[x := LVar lvar_x]> stk) (subst proc_record.(proc_postcond) (<[ proc_record.(ret_var) := LVar lvar_x]> subst_map)) (mask, i).

  Definition SequenceRule stk1 i1 mask1 a1 c1 stk2 i2 mask2 a2 c2 stk3 i3 mask3 a3 :=
    RavenHoareTriple
      stk1 a1 (mask1, i1)
        c1
      stk2 a2 (mask2, i2)
    ->
    RavenHoareTriple
      stk2 a2 (mask2, i2)
        c2
      stk3 a3 (mask3, i3)
    ->
    RavenHoareTriple
      stk1 a1 (mask1, i1)
        (Seq c1 c2)
      stk3 a3 (mask3, i3).

  Definition CondRule stk1 stk2 i1 i2 mask1 mask2 e s1 s2 p q lexpr :=
   trnsl_ravenExpr_lExpr stk1 e = Some lexpr ->
    RavenHoareTriple
      stk1 (LAnd p (LExprA (lexpr))) (mask1, i1)
        s1
      stk2 q (mask2, i2)
    ->
    RavenHoareTriple
      stk1 (LAnd p (LExprA (LUnOp NotBoolOp lexpr))) (mask1, i1)
        s2
      stk2 q (mask2, i2)
    ->
    RavenHoareTriple
      stk1 p (mask1, i1)
        (IfS e s1 s2)
      stk2 q (mask2, i2).

  Definition FrameRule stk1 stk2 i1 i2 mask1 mask2 s p q r :=
    RavenHoareTriple
      stk1 p (mask1, i1)
        s
      stk2 q (mask2, i2)
    ->
    RavenHoareTriple
      stk1 (LAnd p r) (mask1, i1)
        s
      stk2 (LAnd q r) (mask2, i2).

  Definition InvUnfoldRule stk i1 i2 mask1 inv args inv_record lexprs :=
    (map (fun arg => trnsl_ravenExpr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
    | Closed, Opened s => s = {[ (inv, lexprs) ]}
    | Opened s1, Opened s2 => s2 = s1 ∪ {[ (inv, lexprs) ]}
    | Stepped s1, Stepped s2 => s2 = s1 ∪ {[ (inv, lexprs) ]}
    | _, _ => False
    end
    ->
    inv ∈ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (LInv inv lexprs) (mask1, i1)
        (UnfoldInv inv args) 
      stk (subst inv_record.(inv_body) subst_map) (mask1 ∖ {[inv]}, i2)
  .
  
  Definition InvFoldRule stk i1 i2 mask1 inv args inv_record lexprs :=
    (map (fun arg => trnsl_ravenExpr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
    | Opened s, Closed => s = {[ (inv, lexprs) ]}
    | Stepped s, Closed => s = {[ (inv, lexprs) ]}
    | Opened s1, Opened s2 => s2 = s1 ∖ {[ (inv, lexprs) ]} /\ ¬(s2 = ∅)
    | Stepped s1, Stepped s2 => s2 = s1 ∖ {[ (inv, lexprs) ]} /\ ¬(s2 = ∅)
    | _, _ => False
    end
    ->
    inv ∉ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (subst inv_record.(inv_body) subst_map) (mask1, i1)
        (UnfoldInv inv args) 
      stk (LInv inv lexprs) (mask1 ∪ {[inv]}, i2)
  .

  Definition PredUnfoldRule stk i mask pred args pred_record lexprs :=
    (map (fun arg => trnsl_ravenExpr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple
      stk (LPred pred lexprs) (mask, i)
        (UnfoldPred pred args) 
      stk (subst pred_record.(pred_body) subst_map) (mask, i)
  .

  Definition PredFoldRule stk i mask pred args pred_record lexprs :=
    (map (fun arg => trnsl_ravenExpr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple
      stk (subst pred_record.(pred_body) subst_map) (mask, i)
        (FoldPred pred args) 
      stk (LPred pred lexprs) (mask, i)
  .

  Definition FPURule stk i mask e l_expr fld RAPack old_val new_val :=
    trnsl_ravenExpr_lExpr stk e = Some l_expr ->
    (RAPack.(RA_inst) ).(fpuValid) old_val new_val = true ->
    RavenHoareTriple
      stk (LOwn l_expr fld (LitRAElem RAPack old_val)) (mask, i)
        (Fpu e fld (LitRAElem RAPack old_val) (LitRAElem RAPack new_val))
        stk (LOwn l_expr fld (LitRAElem RAPack new_val)) (mask, i)
  .


  Definition WeakeningRule stk1 stk2 i1 i2 mask1 mask2 p p' q q' c :=
  RavenHoareTriple 
    stk1 p (mask1, i1)
      c
    stk2 q (mask2, i2)
  ->
  entails p' p ->
  entails q q' ->

  RavenHoareTriple 
    stk1 p' (mask1, i1)
      c
    stk2 q' (mask2, i2)
  .

  Definition SkipRule stk i1 i2 mask p :=
  oneAtomicStep i1 i2 ->
  RavenHoareTriple
    stk p (mask, i1)
      SkipS
    stk p (mask, i2).

  Definition CASSuccRule stk i1 i2 mask v e1 fld e2 e3 lvar_v lexpr1 old_val new_val :=
  oneAtomicStep i1 i2 ->
  fresh_lvar stk lvar_v ->
  trnsl_ravenExpr_lExpr stk e1 = Some lexpr1 ->
  trnsl_ravenExpr_lExpr stk e2 = Some (LVal old_val) ->
  trnsl_ravenExpr_lExpr stk e3 = Some (LVal new_val) 
  ->
    RavenHoareTriple
      stk (LOwn lexpr1 fld old_val) (mask, i1)
        (CAS v e1 fld e2 e3)
      (<[v := LVar lvar_v]> stk) (LAnd (LOwn lexpr1 fld new_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool true))))) (mask, i2).

  Definition CASFailRule stk i1 i2 mask v e1 fld e2 e3 lvar_v lexpr1 old_val old_val2 :=
  oneAtomicStep i1 i2 ->
  fresh_lvar stk lvar_v ->
  trnsl_ravenExpr_lExpr stk e1 = Some lexpr1 ->
  trnsl_ravenExpr_lExpr stk e2 = Some (LVal old_val2)
  ->
    RavenHoareTriple
      stk (LAnd (LOwn lexpr1 fld old_val) (LExprA (LUnOp NotBoolOp (LBinOp EqOp (LVal old_val) (LVal old_val2))))) (mask, i1) 
        (CAS v e1 fld e2 e3)
      (<[v := LVar lvar_v]> stk) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool false))))) (mask, i2).

End RavenLogic.
