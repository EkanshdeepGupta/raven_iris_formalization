From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
(* From iris_simp_lang Require Import notation tactics class_instances. *)
(* From iris_simp_lang Require Import heap_lib. *)
From iris Require Import options.
From simp_raven_lang Require Import ghost_state.
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

Section lifting.
  (* Open Scope expr_scope. *)
  (* Open Scope bi_scope. *)
  (* Check (λ e Φ, WP e @ ⊤ {{ Φ }}). *)

  Context `{!simpLangG Σ}.

  Lemma wp_heap_wr stk_id stk_frm e v l f x:
    {{{ stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} x ∗ ⌜expr_step e stk_frm (Val v)⌝}}}
      (RTFldWr (Val (LitLoc l)) f e stk_id)
    {{{RET LitUnit; l#f ↦{1%Qp} v}}}.
  Proof.
    iIntros (Φ) "[Hstk [Hl %He]] HΦ" .
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate". 
    iDestruct "Hstate" as "[Hhp [Hproc Hstack]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk ") as "%HstkPure".
    iModIntro. iSplit. 
    - unfold base_reducible. 
      iExists [], (RTVal LitUnit), (update_heap σ l f v), [].
      iPureIntro.
      apply (FldWrStep σ stk_id stk_frm _ f e l v).
      + done. (* given by stack_interp_agreement *) 
      + apply ExprRefl.
      + done.

    - iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H; simpl; iFrame.
      iCombine "Hhp Hl" as "Hcomb".
      iSplitR; first done.
      iPoseProof (own_update heap_heap_name _ _ (heap_update _ _ _ _ v0) with "Hcomb") as "Hcomb2".
      iMod "Hcomb2" as "Hcomb2'".
      iDestruct "Hcomb2'" as "[Hauth Hfrag]".
      iModIntro.
      iSplitL "Hauth".
      + assert (l = l0). { inversion H10. done. }
        rewrite H12; by iFrame.
        (* unfold update_heap in σ'. *)
    
      + iApply "HΦ".
        assert (v = v0). {
          rewrite HstkPure in H9.  injection H9 as H9. 
          rewrite H9 in He.
          apply (expr_step_val_unique _ _ _ _ He H11).
        }
        rewrite H12. iFrame.
  Qed.

  (* Lemma wp_assign stk_id v e  z:
  {{{ True}}}
    (Stmt (Assign v e Term) stk_id)
  {{{ RET z; True}}}.

  Lemma wp_assign s E stk_id frm frm' v e v' z:
  {{{ stack_frame_own stk_id frm}}}
    Stmt (Assign v e Term) stk_id @ s; E
  {{{ RET z; (stack_frame_own stk_id frm')}}}. *)

End lifting.


