From iris.algebra Require Import cmra gmap.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
(* From iris_simp_lang Require Import notation tactics class_instances. *)
(* From iris_simp_lang Require Import heap_lib. *)
From iris Require Import options.
From raven_iris.simp_raven_lang Require Import ghost_state.
From stdpp Require Import gmap list.
Import uPred.
Import weakestpre.

From stdpp Require Import countable.

Class simpLangG Σ := SimpLangG {
  simpLangG_invG : invGS Σ;
  simpLangG_gen_heapG :: heapG Σ
}.

Global Instance simpLang_irisG `{!simpLangG Σ} : irisGS simp_lang Σ := {
  iris_invGS := simpLangG_invG;
  state_interp σ κs _ _ := ghost_state.state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

(* Class simpGS Σ := {
  simp_inG :> inG Σ _;
  simp_langG :> simpLangG Σ;
  (* This line provides the wp instance: *)
  simp_irisGS :> irisGS simp_lang Σ
}. *)

Section lifting.
  (* Open Scope expr_scope. *)
  (* Open Scope bi_scope. *)
  (* Check (λ e Φ, WP e @ ⊤ {{ Φ }}). *)

  Context `{!simpLangG Σ}.

  Lemma wp_heap_wr stk_id stk_frm v e val l f x msk :
    {{{ stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} x ∗ ⌜stk_frm.(locals) !! v = Some (LitLoc l)⌝ ∗ ⌜expr_step e stk_frm (Val val)⌝}}}
      (RTFldWr v f e stk_id) @ msk
    {{{RET LitUnit; stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} val}}}.
    (* Unset Printing Notations. *)
  Proof.
    iIntros (Φ) "[Hstk [Hl [%He %He2]]] HΦ" .
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate". 
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk ") as "%HstkPure".
    iModIntro. iSplit. 
    - unfold base_reducible. 
      iExists [], (RTVal LitUnit), (update_heap σ l f val), [].
      iPureIntro.
      apply (FldWrStep σ stk_id stk_frm _ f e l val); try done.
      

    - iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H as [  |  |  |  
        | σ0 stk_id0 stk_frm0 e1 fld e' l0 v0 Hstk_frm0  Hl0 Hv0 
      |  |  |  |  |  |  |  ]; subst κ efs σ2 σ0 fld stk_id0 e' e1 e2; simpl; iFrame.
      
      assert (l = l0) as Hlsubst. 
        { 
          rewrite  HstkPure in Hstk_frm0. injection Hstk_frm0 as Hstk_frm0. subst stk_frm0. 
        
        assert (Some (LitLoc l) = Some (LitLoc l0) -> l = l0) as H0. { intros Htemp; inversion Htemp; done. }

        apply H0.

        rewrite <- Hl0.
        rewrite He. done.
        } subst l0.
      assert (stk_frm0 = stk_frm) as Hstkfrm_subst. { 
          rewrite HstkPure in Hstk_frm0.  
          injection Hstk_frm0 as Hstk_frm0; try done.
      } subst stk_frm0. 
      assert (val = v0) as Hvsubst. 
        { apply (expr_step_val_unique _ _ _ _ He2 Hv0). } subst v0.
      
      iCombine "Hhp Hl" as "Hcomb".
      iSplitR; first done.
      iPoseProof (own_update heap_heap_name _ _ (heap_update _ _ _ _ val) with "Hcomb") as "Hcomb".
      iMod "Hcomb" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro.
      iSplitL "Hauth".
      + by iFrame.
        (* unfold update_heap in σ'. *)
    
      + iApply "HΦ". iFrame.
  Qed.


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






  Lemma wp_assign stk_id stk_frm v v' e msk:
    {{{ stack_own[ stk_id, stk_frm] ∗ ⌜expr_step e stk_frm (Val v')⌝}}}
      (RTAssign v e stk_id) @ msk
    {{{ RET LitUnit; stack_own[ stk_id, StackFrame (<[v:=v']>stk_frm.(locals)) ] }}}.
  Proof.
    iIntros (Φ) "[Hstk %He] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iModIntro. iSplitR.
    - unfold base_reducible.
      iExists [], (RTVal LitUnit), (update_lvar σ v stk_id v'), [].
      iPureIntro.
      apply (RTAssignStep σ stk_id stk_frm v e v'); try done.

    - iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H as [  | 
        σ0 stk_id0 stk_frm0 e1 v0 e0 Hstk_frm0 Hv0 
      |  |  |  |  |  |  |  |  |  |  ]; subst κ efs σ2 σ0 v0 e1 e2; simpl. 
      (* iFrame. *)

      assert (stk_frm0 = stk_frm) as Hstkfrm_subst. { 
          rewrite HstkPure in Hstk_frm0.  
          injection Hstk_frm0 as Hstk_frm0; try done.
      } subst stk_frm0. 
      assert (v' = e0) as Hvsubst. 
        { apply (expr_step_val_unique _ _ _ _ He Hv0). } subst v'.
      
      iCombine "Hstack" "Hstk" as "Hcomb".
      iSplitR; first done.
      iPoseProof (own_update heap_stack_name 
          (● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := {| locals := <[v:=e0]> (locals stk_frm) |}]})

           with "Hcomb"
      ) 
          as "Hcomb2".
      { apply stack_upd_valid. }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro. iFrame.
      (* iSplitL "Hauth".
      + by iFrame. *)

      + iApply "HΦ". by iFrame.

  Qed.


  Lemma wp_heap_rd stk_id stk_frm fld e val l x msk q:
  {{{ stack_own[ stk_id, stk_frm ] ∗ ⌜expr_step e stk_frm (Val (LitLoc l))⌝ ∗ l#fld ↦{q%Qp} val }}}
      (RTFldRd x e fld stk_id) @ msk
    {{{RET LitUnit; stack_own[ stk_id, StackFrame (<[x:=val]>stk_frm.(locals))] ∗ l#fld ↦{q%Qp} val}}}.
  Proof.
    iIntros (Φ) "[Hstk [%HexprStep HHeap]] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (heap_interp_agreement with "Hhp HHeap") as "%HHeapPure".
    iSplitR.
    - unfold base_reducible.
      iExists [], (RTVal LitUnit), (update_lvar σ x stk_id val), [].
      iPureIntro.
      apply (FldRdStep σ stk_id stk_frm x e fld l val); try done.

    - iModIntro. iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H as [ | | | | | 
          σ0 stk_id0 stk_frm0 v0 e0 fld0 l0 v2 Hstk_frm0 HexSt HlookUp
        |  |  |  |  |  |  ]; subst v0 e0 fld0 stk_id0 σ0 κ e2 σ2 efs. simpl. iFrame "Hproc Hhp".

      assert (stk_frm0 = stk_frm) as Hstkfrm_subst. { 
          rewrite HstkPure in Hstk_frm0.  
          injection Hstk_frm0 as Hstk_frm0; try done.
      } subst stk_frm0.
    
      assert (LitLoc l = LitLoc l0) as Hlsubst. 
        { apply (expr_step_val_unique _ _ _ _ HexprStep HexSt). } injection  Hlsubst as Hl. subst l0.
      (* iModIntro. *)

      assert (val = v2) as Hvalsubst. {
        rewrite HHeapPure in HlookUp.
        injection HlookUp as HlookUp; try done.
      } subst v2.

      iSplitR; try done.

      iCombine "Hstack" "Hstk" as "Hcomb".

      iPoseProof (own_update heap_stack_name 
          (● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := {| locals := <[x:=val]> (locals stk_frm) |}]})

           with "Hcomb"
      ) 
          as "Hcomb2".
      { apply stack_upd_valid. }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro. iFrame.
      iApply "HΦ". iFrame.
  Qed.

  Fixpoint field_list_to_iprop lexpr fld_vals : iProp Σ := match fld_vals with
  | [] => ⌜True⌝
  | (fld,val) :: fld_vals => ( lexpr#fld ↦{1%Qp}(val)) ∗(field_list_to_iprop lexpr fld_vals)
  end.

  Lemma wp_alloc stk_id stk_frm fs x msk:
    {{{ stack_own[ stk_id, stk_frm ] }}}
      (RTAlloc x fs stk_id) @ msk
    {{{RET LitUnit; ∃ l: loc, stack_own[ stk_id, StackFrame (<[x:=LitLoc l]>stk_frm.(locals))] ∗ field_list_to_iprop l fs}}}.
  Proof.
    iIntros (Φ) "Hstk HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iSplitR.
    - unfold base_reducible.
        set (l := fresh_loc σ.(global_heap)).
        set (σ' := (foldr (fun f_v  acc => update_heap acc l (fst f_v) (snd f_v)) σ fs)).
        set (σ'' := update_lvar σ' x stk_id (LitLoc l)). 
      iExists [], (RTVal LitUnit), σ'', [].
      iPureIntro.
      apply (AllocStep σ stk_id x fs); try done.

    - iModIntro. iNext. iIntros (e2 σ2 efs) "%H Hcred".
    inversion H as [  |  |  |  |  |  |  |
        | σ0 stk_id0 x0 fs0
        |  |  |  ]; subst x0 fs0 stk_id0 σ0 κ e2 σ2 efs; simpl; iFrame.
        iSplitR; try done.

      iCombine "Hstack" "Hstk" as "Hcomb".

      unfold heap_interp.

      set (fs_map := list_to_map fs : gmap fld_name lang.val).
      set (fs_heap_map := foldr (λ f_v acc, 
        <[(heap_addr_constr l f_v.1) := f_v.2]> acc) ∅ fs : gmap heap_addr lang.val).

      iPoseProof (own_update heap_heap_name
        (● to_heapUR (global_heap σ))
        (● to_heapUR (global_heap σ') ⋅ (◯  (to_heapUR fs_heap_map ) ))
        with "Hhp"
      ) as "HHeapUpd".

      { 
        
        apply (heap_alloc_valid fs σ).
      }

      assert ((stack σ) = (stack σ')) as H0. {
        clear H.

        induction fs.
        - simpl in σ'. subst σ'. done.
        - simpl in σ'. 
        remember (foldr (λ f_v acc, update_heap acc l f_v.1 f_v.2) σ fs) as σ0 eqn:Hσ.
        unfold σ' in IHfs. rewrite IHfs. subst σ'. unfold update_heap. simpl. done.
      }
      rewrite H0.

      iPoseProof (own_update heap_stack_name 
          (● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack σ'') ⋅ ◯ to_stackR {[stk_id := {| locals := <[x:=LitLoc l]> (locals stk_frm) |}]})

           with "Hcomb"
      )
          as "Hcomb2".
      { apply stack_upd_valid. }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iDestruct "HHeapUpd" as ">[HHeapUpd HHp2]".
      iModIntro. iFrame.

      assert (procs σ'' = procs σ) as H1.
      { clear H H0. subst σ''. simpl. subst σ'. induction fs.
      - simpl. done.
      - unfold fs_map in IHfs. simpl. apply IHfs.  }

      rewrite H1. iFrame.
      iApply "HΦ".
      iExists l. iFrame.

      clear H H0 H1.
      iClear "Hcred".
      iInduction fs as [ | ] "IHfs".
      + simpl. done.
      +
      simpl in fs_heap_map.
      subst fs_heap_map.
      simpl.
      unfold to_heapUR.
      rewrite fmap_insert.

      rewrite insert_singleton_op. 
      2 : { 
        (* uniqueness of fields in f_v *)
        admit.
       }
       rewrite auth_frag_op.
       iDestruct "HHp2" as "[HHp2 HHp3]".
       
       destruct a as [fld val]. simpl. iFrame.
       iApply "IHfs". iApply "HHp3".

  Admitted.

  Lemma wp_seq p q r s1 s2 mask:
  {{{ p }}} s1 @ mask {{{ RET lang.LitUnit; q }}} -∗
  {{{ q }}} s2 @ mask {{{ RET lang.LitUnit; r }}} -∗

  {{{ p }}} RTSeq s1 s2 @ mask {{{ RET lang.LitUnit; r }}}.
  Proof.
    iIntros "#Hs1 #Hs2".
    iIntros (Φ). iModIntro. iIntros "Hp HΦ".
    iApply (wp_bind (fill_item (SeqCtx s2)) _ _ _ _).
    iApply ("Hs1" with "Hp").
    iNext. iIntros "Hq".
    simpl.

    iApply wp_lift_base_step; first done.
    iIntros (σ ns κ κs nt) "Hstate".

    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iApply fupd_mask_intro. { set_unfold. try done. }
    iIntros "Hemp".
  
    iSplitR.
    - iPureIntro. unfold base_reducible. 
    exists [], s2, σ, [].
    apply SeqStep.

    - iModIntro. iIntros (e2 σ2 efs).
    
    iIntros "%H Hcred".
    inversion H as [ | | | | | | | | | | | ]; subst s0 σ0 κ s2 σ2 efs. iFrame.
    simpl. 
    iMod "Hemp". iModIntro.
    iFrame.
    iApply ("Hs2" with "Hq"). iNext; iFrame.
  Qed.

  Lemma wp_skip p mask stk_id :
  {{{ p }}} RTSkipS stk_id @ mask {{{ RET lang.LitUnit; p }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iSplitR.
    - unfold base_reducible. iExists [], (RTVal LitUnit), σ, [].
    iPureIntro. apply RTSkipStep.

    - iModIntro. iNext. iIntros (e2 σ2 efs) "%H Hcred". iModIntro.
    inversion H; subst σ0 κ e2 σ2 efs. iSplitR; try done. iFrame. simpl. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_cas_succ x e1 fld e2 e3 stk_id stk_frm l v v' mask:
  expr_step e1 stk_frm (Val (LitLoc l)) ->
  expr_step e2 stk_frm (Val v) ->
  expr_step e3 stk_frm (Val v') ->
  {{{ stack_own[ stk_id, stk_frm ] ∗ l#fld ↦{1} v }}}
    RTCAS x e1 fld e2 e3 stk_id @ mask
  {{{ RET lang.LitUnit; stack_own[ stk_id, StackFrame (<[x:=LitBool true]> stk_frm.(locals)) ] ∗ l#fld ↦{1} v'}}}.
  Proof.
    intros He1 He2 He3.
    iIntros (Φ) "[Hstk Hl] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (heap_interp_agreement with "Hhp Hl") as "%HHeapPure".

    iModIntro. iSplitR.
    - iPureIntro. unfold base_reducible. exists [], (RTVal LitUnit), (update_lvar (update_heap σ l fld v') x stk_id (LitBool true)), [].
    apply (CASSuccStep σ stk_id stk_frm x e1 fld e2 e3 l v v'); try done.

    - iNext. iIntros (e0 σ2 efs) "%H Hcred".
    inversion H; subst v0 e4 fld0 e5 e6 stk_id0 σ0 κ e0 efs.

      +
        rewrite HstkPure in H11. inversion H11; subst stk_frm0.
        assert (v' = v3) as Hv. { apply (expr_step_val_unique e3 stk_frm); try done. } subst v3.
        assert (l0 = l) as Hl. { assert (LitLoc l0 = LitLoc l). {apply (expr_step_val_unique e1 stk_frm (LitLoc l0) (LitLoc l)); try done. } inversion H0; done. } subst l0.
        clear H11 H12.
        subst σ''.
        iPoseProof (heap_l_upd σ l fld v v' with "[Hl Hhp]") as "Hhp_upd"; first iFrame.
        iPoseProof (stack_lvar_upd _ _ _ x (LitBool true) with "[Hstk Hstack]") as "Hstk_upd"; try iFrame.

        iDestruct "Hhp_upd" as ">[Hl Hhp]".
        iDestruct "Hstk_upd" as ">[Hstk Hstack]".
        iModIntro.
        iSplitR; try auto.
         
        assert (global_heap (update_lvar σ' x stk_id (LitBool true)) = global_heap σ').
        { simpl. done. }
        rewrite H0.
        iFrame.
        iApply "HΦ". iFrame.

      + rewrite HstkPure in H11. inversion H11; subst stk_frm0.
        assert (l0 = l) as Hl. { assert (LitLoc l0 = LitLoc l). { apply (expr_step_val_unique e1 stk_frm (LitLoc l0) (LitLoc l)); try done. } inversion H0; done. } subst l0.
        rewrite HHeapPure in H14. inversion H14; subst v1.
        assert (v = v2). { apply (expr_step_val_unique e2 stk_frm); try done. }
        contradiction. 
  Qed.

  Lemma wp_cas_fail x e1 fld e2 e3 stk_id stk_frm l v v0 mask:
    expr_step e1 stk_frm (Val (LitLoc l)) ->
    expr_step e2 stk_frm (Val v) ->
    not (v = v0) -> 
    {{{ stack_own[ stk_id, stk_frm ] ∗ l#fld ↦{1} v0 }}}
      RTCAS x e1 fld e2 e3 stk_id @ mask
    {{{ RET lang.LitUnit; stack_own[ stk_id, StackFrame (<[x:=LitBool false]> stk_frm.(locals)) ] ∗ l#fld ↦{1} v0}}}.
  Proof.
    intros He1 He2 Hneq.
    iIntros (Φ) "[Hstk Hl] HΦ".

    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (heap_interp_agreement with "Hhp Hl") as "%HHeapPure".

    iModIntro. iSplitR.
    - iPureIntro. unfold base_reducible. exists [], (RTVal LitUnit), (update_lvar σ x stk_id (LitBool false)), [].
    apply (CASFailStep σ stk_id stk_frm x e1 fld e2 e3 l v0 v); try done.

    - iNext. iIntros (e0 σ2 efs) "%H Hcred".
    inversion H; subst v1 e4 fld0 e5 e6 stk_id0 σ0 κ e0 efs.

      + assert (stk_frm = stk_frm0) as Hstk_frm.
        { rewrite HstkPure in H11. injection H11 as H11. done. }
        subst stk_frm0.
        assert (LitLoc l = LitLoc l0) as Hl_l0. { apply (expr_step_val_unique e1 stk_frm); try done. } injection Hl_l0 as Hl_l0. subst l0. rewrite HHeapPure in H15. injection H15 as H15. subst v2.
        assert (v = v0) as Hv_v0. { apply (expr_step_val_unique e2 stk_frm); try done. } contradiction.

      + subst σ2.
        assert (stk_frm = stk_frm0) as Hstk_frm.
          { rewrite HstkPure in H11. injection H11 as H11. done. }
        subst stk_frm0. 
        assert (LitLoc l = LitLoc l0) as Hl_l0. { apply (expr_step_val_unique e1 stk_frm); try done. } injection Hl_l0 as Hl_l0. subst l0. rewrite HHeapPure in H14. injection H14 as H14. subst v2.
        clear H15 H13 H12 v3.
        
        iPoseProof (stack_lvar_upd _ _ _ x (LitBool false) with "[Hstk Hstack]") as "Hstk_upd"; try iFrame.

        iDestruct "Hstk_upd" as ">[Hstk Hstack]".
        iModIntro. iSplitR; try done. iFrame. iApply "HΦ". iFrame.
  Qed.





End lifting.


