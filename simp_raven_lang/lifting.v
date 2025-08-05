From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
(* From iris_simp_lang Require Import notation tactics class_instances. *)
(* From iris_simp_lang Require Import heap_lib. *)
From iris Require Import options.
From raven_iris.simp_raven_lang Require Import ghost_state.
From stdpp Require Import gmap.
Import uPred.
Import weakestpre.



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

  Lemma wp_heap_wr stk_id stk_frm v e val l f x:
    {{{ stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} x ∗ ⌜stk_frm.(locals) !! v = Some (LitLoc l)⌝ ∗ ⌜expr_step e stk_frm (Val val)⌝}}}
      (RTFldWr v f e stk_id)
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
      |  |  |  |  |  |  ]; subst κ efs σ2 σ0 fld stk_id0 e' e1 e2; simpl; iFrame.
      
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


  (* Lemma wp_assign: similar to wp_heap_wr for the Assign statement *)

  Lemma wp_assign stk_id stk_frm v v' e:
    {{{ stack_own[ stk_id, stk_frm] ∗ ⌜expr_step e stk_frm (Val v')⌝}}}
      (RTAssign v e stk_id)
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
      |  |  |  |  |  |  |  |  |  ]; subst κ efs σ2 σ0 v0 e1 e2; simpl. 
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
      { admit. }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro. iFrame.
      (* iSplitL "Hauth".
      + by iFrame. *)

      + iApply "HΦ". by iFrame.
  Admitted.

End lifting.


