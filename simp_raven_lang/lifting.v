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


  Lemma heap_upd_valid :
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
        
        apply (heap_upd_valid fs σ).
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

End lifting.


