From stdpp Require Import coPset.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export tactics.
From simp_raven_lang Require Export lang.

From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".
Import uPred.

(* Inductive heap_addr :=
| heap_addr_constr:  loc -> fld_name -> heap_addr.

Global Instance heap_addr_eq : EqDecision heap_addr.
Proof. solve_decision. Qed.

Global Declare Instance heap_addr_countable : Countable heap_addr. *)


Inductive stackvar_addr :=
| mk_stkvar_addr (stk_id : stack_id) (v : var).

Global Instance stackvar_addr_eq : EqDecision stackvar_addr.
Proof. solve_decision. Qed.

Global Declare Instance stackvar_addr_countable : Countable stackvar_addr.


Definition heap_cellR : cmra :=
  prodR fracR (agreeR valO).

Definition heapUR : ucmra :=
  gmapUR heap_addr heap_cellR.

Definition stackUR :=
  gmapUR stack_id (exclR stack_frame).

Class heapG Σ := HeapG {
  heap_heap_inG :: inG Σ (authR heapUR);
  heap_heap_name : gname;
  heap_stack_inG :: inG Σ (authR stackUR);
  heap_stack_name : gname;
  heap_proctbl_inG :: ghost_mapG Σ proc_name proc;
  heap_proctbl_name : gname;
}.

Section definitions.
  Context `{!heapG Σ}.

  Definition to_heap_cellR (v: val) : heap_cellR := (1%Qp, to_agree v).

  (* Not sure why this is needed. *)
  Global Instance insert : Insert heap_addr (Qp * val) (gmap heap_addr heap_cellR).
  Proof. unfold Insert; intros; done. Qed.
  
  Global Instance heap_add_fmap : FMap (gmap heap_addr).
  Proof. apply gmap_fmap. Qed.



  Definition to_heapUR (h : heap) : heapUR :=
  fmap (λ v, (to_heap_cellR v)) h.
  (* fold_left (fun acc (p : loc * gmap fld_name val) =>
    let (l, fs) := p in
    fold_left (fun (acc' : (gmap heap_addr heap_cellR)) (q : fld_name * val) =>
      let (f, v) := q in
      <[ (heap_addr_constr l f) := (to_heap_cellR v)]> acc' )

    (map_to_list fs) acc)
  (map_to_list h) ∅. *)

  Definition heap_interp (h : heap) : iProp Σ :=
  own heap_heap_name (● (to_heapUR h)).

  Definition proc_tbl_interp (proc_tbl : gmap proc_name proc) : iProp Σ :=
    ghost_map_auth heap_proctbl_name 1 proc_tbl. 

  Definition to_stackR (s : gmap stack_id stack_frame) : stackUR :=
    fmap (λ frm, Excl frm) s.
    (* fold_left (fun acc (elem : stack_id * stack_frame) =>
      let (sid, sf) := elem in
      fold_left (fun acc' (elem2 : var * val) => 
        let (x, v) := elem2 in
        (<[ (mk_stkvar_addr sid x) := (Excl v)]> acc')
      ) (map_to_list sf.(locals)) acc
    ) (map_to_list s) (∅ : (gmapR stackvar_addr (exclR valO))). *)

  Definition stack_interp (stack : gmap stack_id stack_frame) : iProp Σ :=
    own heap_stack_name (● (to_stackR stack)).

  Definition state_interp (σ : state) : iProp Σ :=
  heap_interp σ.(global_heap) ∗ proc_tbl_interp σ.(procs) ∗ stack_interp σ.(stack).

  Global Instance singletonM_heapUR : SingletonM heap_addr (Qp * val) heapUR := λ H H0, <[H := H0]> ∅.

  Definition heap_maps_to (l : loc) (fld : fld_name) (q : Qp) (v : val) :=
    own heap_heap_name (◯ {[(heap_addr_constr l fld) := (q, to_agree v)]}).

  Definition stack_frame_own (stk_id : stack_id) (stk_frm : stack_frame)  := 
    own heap_stack_name (◯ (to_stackR ({[stk_id := stk_frm]} ))).

  Lemma heap_update σ l f x v0: 
    (● ((λ v1 : lang.val, to_heap_cellR v1) <$> global_heap σ)
    ⋅ ◯ {[heap_addr_constr l f := (1%Qp, to_agree x)]}) ~~> 
    
    (● ((λ v1 : lang.val, to_heap_cellR v1) <$> <[heap_addr_constr l f:=v0]> (global_heap σ))
    ⋅ ◯ {[heap_addr_constr l f := (1%Qp, to_agree v0)]}).
  Proof.
  Admitted.
  
  Lemma stack_interp_agreement σ stk_id stk_frm : (stack_interp (stack σ)) -∗ stack_frame_own stk_id stk_frm -∗ ⌜stack σ !! stk_id = Some stk_frm⌝.
  Proof. 
    iIntros "Hstack Hstk".
    unfold stack_interp.
    unfold stack_frame_own.
    iCombine "Hstack" "Hstk" as "HstackV".
    iPoseProof (own_valid with "HstackV") as "%Hi".
    apply auth_both_valid_discrete in Hi.
    destruct Hi as [Hi1 Hi2].
    (* iPureIntro. *)
     (* gmap.lookup_included in Hi1. *)
    (* Check gmap.lookup_included. *)
    rewrite -> (gmap.lookup_included (to_stackR {[stk_id := stk_frm]}) (to_stackR (stack σ))) in Hi1.
    specialize (Hi1 stk_id).
    iPureIntro.

    (* Locate map_lookup. *)
    (* unfold to_stackR in Hi1. *)
    rewrite !lookup_fmap in Hi1. cbn in Hi1. rewrite lookup_insert in Hi1. cbn in Hi1.
    destruct (stack σ !! stk_id); try done.
    -  cbn in Hi1. rewrite Excl_included in Hi1. 
    apply leibniz_equiv in Hi1. by subst s.

    - cbn in Hi1. exfalso. rewrite option_included in Hi1.
    destruct Hi1; try done.
    destruct H as [a [b [H1 [H2 H3]]]]. try done.
  Qed.
End definitions.

Notation " l # f  ↦{ q } v" := (heap_maps_to l f q v)
(at level 20) : bi_scope.

Notation "'stack_own[' stk_id , frm ']' " := (stack_frame_own stk_id frm)
(at level 20) : bi_scope.