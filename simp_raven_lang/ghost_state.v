From stdpp Require Import coPset gmap.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export tactics.
From raven_iris.simp_raven_lang Require Export lang.

From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".
Import uPred.

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
  (* Global Instance insert : Insert heap_addr (Qp * val) (gmap heap_addr heap_cellR).
  Proof. unfold Insert; intros; done. Qed. *)
  
  Global Instance heap_add_fmap : FMap (gmap heap_addr).
  Proof. apply gmap_fmap. Qed.

  Global Declare Instance heap_addr_finmap : FinMap heap_addr (gmap heap_addr).


  Definition to_heapUR (h : heap) : heapUR :=
  fmap (λ v, (to_heap_cellR v)) h.

  Definition heap_interp (h : heap) : iProp Σ :=
  own heap_heap_name (● (to_heapUR h)).

  Definition proc_tbl_interp (proc_tbl : gmap proc_name proc) : iProp Σ :=
    ghost_map_auth heap_proctbl_name 1 proc_tbl. 

  Definition to_stackR (s : gmap stack_id stack_frame) : stackUR :=
    fmap (λ frm, Excl frm) s.

  Definition stack_interp (stack : gmap stack_id stack_frame) : iProp Σ :=
    own heap_stack_name (● (to_stackR stack)).

  Definition state_interp (σ : state) : iProp Σ :=
  heap_interp σ.(global_heap) ∗ proc_tbl_interp σ.(procs) ∗ stack_interp σ.(stack).


  Definition heap_maps_to (l : loc) (fld : fld_name) (q : Qp) (v : val) :=
    own heap_heap_name (◯ {[(heap_addr_constr l fld) := (q, to_agree v)]}).

  Definition stack_frame_own (stk_id : stack_id) (stk_frm : stack_frame)  := 
    own heap_stack_name (◯ (to_stackR ({[stk_id := stk_frm]} ))).

  Definition proc_tbl_chunk (p : proc_name) (proc : proc) : iProp Σ :=
    p ↪[heap_proctbl_name] proc.

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

  Lemma heap_interp_agreement σ l f q v:
  (heap_interp (global_heap σ)) -∗ (heap_maps_to l f q v) -∗ ⌜lookup_heap σ l f = Some v⌝.
  Proof.
    iIntros "Hheap Hhp".
    unfold heap_interp.
    unfold heap_maps_to.
    iCombine "Hheap" "Hhp" as "HhpV".
    iPoseProof (own_valid with "HhpV") as "%Hi".
    apply auth_both_valid_discrete in Hi.
    destruct Hi as [Hi1 Hi2].

    (* Search gmap.lookup_included. *)
    rewrite (gmap.lookup_included ({[heap_addr_constr l f := (q, to_agree v)]})) in Hi1.
    specialize (Hi1 (heap_addr_constr l f)).
    iPureIntro.
    unfold to_heapUR in Hi1.

    rewrite lookup_insert in Hi1.
    rewrite lookup_fmap in Hi1.
    unfold lookup_heap.

    apply Some_included_is_Some in Hi1 as H3.
    (* Had to destruct a verbose version to mitigate strange Coq errors. *)
    destruct ((@lookup heap_addr val
      (@gmap heap_addr heap_addr_eq heap_addr_countable val)
      (@gmap_lookup heap_addr heap_addr_eq heap_addr_countable val)
      (heap_addr_constr l f) (global_heap σ))) eqn:Hlp; try done.

    2 : { simpl in *. destruct H3 as [x Hx]. simpl in Hx. discriminate. }
    
    rewrite Hlp.  
    simpl in *.
    apply Some_pair_included in Hi1 as [_ Heq].

    rewrite Some_included_total in Heq.
    rewrite to_agree_included in Heq.
    apply f_equal.
    simpl in *.
    setoid_subst. done.
  Qed.

  Lemma proc_tbl_interp_agreement σ proc proc_entry:
  (proc_tbl_interp (procs σ)) -∗ (proc_tbl_chunk proc proc_entry) -∗ 
    ⌜σ.(procs) !! proc = Some proc_entry⌝.
  Proof.
  Admitted.

End definitions.

Notation " l # f  ↦{ q } v" := (heap_maps_to l f q v)
(at level 20) : bi_scope.

Notation "'stack_own[' stk_id , frm ']' " := (stack_frame_own stk_id frm)
(at level 20) : bi_scope.

Section updates.
    Context `{!heapG Σ}.
  Lemma stack_upd_valid σ stk_id stk_frm v val:
    let σ' := update_lvar σ v stk_id val in
      ● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]} ~~>
      ● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := {| locals := <[v:=val]> (locals stk_frm) |}]}.
  Proof.
    intros σ'.
    apply auth_update.
    apply iris.algebra.gmap.gmap_local_update.
    intros stk_id'.
    destruct (stack σ !! stk_id') eqn:HstkLookup.
    - rewrite lookup_fmap. rewrite HstkLookup. simpl.
    destruct (Z.eqb stk_id stk_id') eqn:Hstkid.
      + rewrite Z.eqb_eq in Hstkid. subst stk_id'. rewrite lookup_fmap. rewrite lookup_insert. simpl. rewrite lookup_fmap. rewrite lookup_insert. simpl.

  Admitted.

  Lemma stack_lvar_upd σ stk_id stk_frm x v :
    stack_own[ stk_id, stk_frm ] ∗ stack_interp (stack σ) ==∗ 
    stack_own[stk_id, StackFrame (<[x := v]> stk_frm.(locals)) ] ∗ stack_interp (stack (update_lvar σ x stk_id v)).
  Proof.
    iIntros "[Hstk Hstack]".
    iCombine "Hstack" "Hstk" as "Hcomb".
      iPoseProof (own_update heap_stack_name 
          (● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack (update_lvar σ x stk_id v)) ⋅ ◯ to_stackR {[stk_id := {| locals := <[x:=v]> (locals stk_frm) |}]})

           with "Hcomb"
      ) 
          as "Hcomb2".
      { apply stack_upd_valid. }
      iDestruct "Hcomb2" as ">[Hstack Hstk]".
      iModIntro. iFrame.
  Qed.

  (* This needs formalization of some inductive property that σ.(max_stack_id) is always unallocated. *)
  Lemma stack_new_stk_frm_upd σ stk_frm' :
    stack_interp (stack σ) ==∗
    stack_interp (update_stack σ (Z.to_nat σ.(max_stack_id) + 1) stk_frm').(stack) ∗ stack_own[Z.to_nat σ.(max_stack_id) + 1, stk_frm'].
  Proof.
    Admitted.

  Lemma heap_upd_valid σ l fld v v':
    ● to_heapUR (global_heap σ) ⋅ ◯ {[heap_addr_constr l fld := (1%Qp, to_agree v)]} ~~>
    ● to_heapUR (global_heap (update_heap σ l fld v')) ⋅ ◯ {[heap_addr_constr l fld := (1%Qp, to_agree v')]}.
  Proof.
  Admitted.


  Lemma heap_l_upd σ l fld v v' : 
    l#fld ↦{1%Qp } v ∗ heap_interp (global_heap σ) ==∗
    l#fld ↦{1%Qp } v' ∗ heap_interp (global_heap (update_heap σ l fld v')).
  Proof.
    iIntros "[Hl Hhp]".
    iCombine "Hhp" "Hl" as "Hcomb".
    iPoseProof (own_update heap_heap_name
      (● to_heapUR (global_heap σ) ⋅ ◯ {[(heap_addr_constr l fld) := (1%Qp, to_agree v)]})
      (● to_heapUR (global_heap (update_heap σ l fld v')) ⋅ ◯ {[(heap_addr_constr l fld) := (1%Qp, to_agree v')]})
      with "Hcomb"
    ) as "Hcomb2".
    { apply heap_upd_valid. }
    iDestruct "Hcomb2" as ">[Hhp Hl]".
    iModIntro. iFrame.
  Qed.

  Lemma heap_alloc_valid :
    ∀ fs σ, 
    let l := fresh_loc (global_heap σ) in
    let σ' := fold_right 
        (λ f_v acc ,
          update_heap acc l f_v.1 f_v.2) 
      σ fs  in
    let fs_heap_map := fold_right
        (λ f_v acc, <[heap_addr_constr l f_v.1:=f_v.2]> acc) 
      ∅ fs in
    ● to_heapUR (global_heap σ) ~~> ● to_heapUR (global_heap σ') ⋅ ◯ to_heapUR fs_heap_map.
  Proof. 
    induction fs as [ | fs fss IH].

    - intros σ l σ' fs_heap_map. simpl in fs_heap_map. subst fs_heap_map. 
      (* set (σ' := (fold_left
        (λ (acc : lang.state) (f_v : fld_name * lang.val), update_heap acc l f_v.1 f_v.2)
        [] σ0)). *)
      
      simpl in σ'. subst σ'. unfold to_heapUR. rewrite fmap_empty. apply  auth_update_alloc. unfold ε. 
        set (hp1 := (λ v : lang.val, to_heap_cellR v) <$> global_heap σ : gmapUR heap_addr heap_cellR).
        assert (hp1 = ε ⋅ hp1 ) as H0. { admit. }
        rewrite -> H0 at 2.
        assert ((∅ : gmapUR heap_addr heap_cellR) = ε ⋅ (∅ : gmapUR heap_addr heap_cellR)) as H1. { admit. }
        rewrite H1.
      apply (op_local_update_discrete hp1 ε ∅).
      intros. simpl. rewrite left_id. done.

      - intros σ l σ' fs_heap_map. simpl in fs_heap_map.
       simpl in σ'.
       specialize (IH σ).

      unfold l in IH.
      remember (fresh_loc (global_heap σ)) as l0 eqn:Hl.


      remember (foldr
          (λ f_v acc, update_heap acc l0 f_v.1 f_v.2)
        σ fss
      ) as σ0 eqn:Hσ.

      remember (foldr
        (λ f_v acc, <[heap_addr_constr l0 f_v.1:=f_v.2]> acc
        ) ∅ fss
      ) as fs_heap_map0 eqn:Hfs.

      subst l.


      remember σ' as σ'0 eqn:Hσ'.
      subst σ'.
      rewrite <- Hσ in Hσ'.

      remember fs_heap_map as fs_heap_map'0 eqn:Hfs'.
      subst fs_heap_map.
      rewrite <- Hfs in Hfs'.
      subst σ'0.
      subst fs_heap_map'0.
      rewrite IH.
      unfold update_heap. simpl.
      apply auth_update.
      unfold to_heapUR at 3 4.
      rewrite fmap_insert. rewrite fmap_insert.
      apply alloc_local_update.
      
      { admit. }
      { admit. }
  Admitted.

End updates.