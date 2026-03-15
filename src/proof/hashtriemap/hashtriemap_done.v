From iris.bi.lib Require Import atomic.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From New.ghost Require Import ghost_var.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Import paths.
From New.proof.hashtriemap Require Import model.

Open Scope Z_scope.

Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context {sem : go.Semantics} {package_sem : hashtriemap.Assumptions}.
  Collection W := sem + package_sem.
  Set Default Proof Using "W".
  Context `{!ghost_varG Σ bool}
    `{!ghost_varG Σ (gmap w64 w64)}
    `{!mapG Σ w64 w64}
    `{!mapG Σ Z (gmap w64 w64)}
    `{!mapG Σ nat (gmap w64 w64)}
    `{!mapG Σ nat lookup_info}
    `{!mapG Σ nat lookup_status}.

  Definition nChildren : Z := 16.
  Example nChildren_ok : # nChildren = hashtriemap.nChildren := eq_refl.
  Definition nChildrenLog2 : Z := 4.
  Example nChildrenLog2_ok : # nChildrenLog2 = hashtriemap.nChildrenLog2 := eq_refl.

  Definition map_get `{!IntoVal V} `{!IntoValTyped V t} (v: option V) : V * bool :=
    (default (zero_val V) v, bool_decide (is_Some v)).

  #[global] Instance : IsPkgInit (iProp Σ) hashtriemap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf (iProp Σ) hashtriemap := build_get_is_pkg_init_wf.

  Lemma next_nibble_eq (key: w64) (path: path) :
    let h := uint.Z (hash_key key) in
    let n := (w64_word_instance.(word.and)
                                  (w64_word_instance.(word.sru) (hash_key key)
                                                       (w64_word_instance.(word.sub) (W64 (sh path)) (W64 4)))
                                  (W64 15)) in
    length path < 16 → sint.Z n = Z.land (h ≫ (sh path - 4)) 15.
  Proof.
    intros.
    unfold h.
    subst n.
    rewrite sint_eq_uint.
    - rewrite word.unsigned_and_nowrap.
      f_equiv; [|word].
      rewrite word.unsigned_sru.
      + rewrite word.unsigned_sub.
        unfold sh.
        rewrite wrap_small; auto.
        * f_equiv.
          unfold sh.
          word.
        * replace (uint.Z (W64 (64 - 4 * length path))) with (64 - 4 * length path) by word.
          replace (uint.Z (W64 4)) with 4 by word.
          replace (w64_word_instance_ok.(word.wrap) (64 - 4 * length path - 4)) with (64 - 4 * length path - 4) by word.
          unfold sh in *.
          have Hx : ((64 - 4 * length path - 4)) ≥ 0 by lia.
          have Hrng : 0 ≤ uint.Z (hash_key key) < 2^64 by word.
          split.
          -- apply Z.shiftr_nonneg. lia.
          -- destruct Hrng as [_ Hrng].
             apply (Z.le_lt_trans _ (uint.Z (hash_key key))); [|exact Hrng].
             set x := uint.Z (hash_key key).
             rewrite Z.shiftr_div_pow2; [|word].
             apply Z.div_le_upper_bound; [word|].
             assert ((2 ^ (64 - 4 * length path - 4)) > 0) by lia.
             replace x with (x * 1) at 1 by lia.
             replace (2 ^ (64 - 4 * length path - 4) * x) with (x * 2 ^ (64 - 4 * length path - 4)) by lia.
             apply Zmult_le_compat_l; word.
      + rewrite word.unsigned_sub.
        unfold sh.
        replace (uint.Z (W64 (64 - 4 * length path))) with (64 - 4 * length path) by word.
        replace (uint.Z (W64 4)) with 4 by word.
        word.
    - rewrite word.unsigned_and.
      set x := (uint.Z (w64_word_instance.(word.sru) (hash_key key)
                                            (w64_word_instance.(word.sub) (W64 (sh path)) (W64 4)))).
      replace (uint.Z (W64 15)) with 15 by word.
      replace 15 with (Z.ones 4) by reflexivity.
      rewrite Z.land_ones; [|lia].
      pose proof (Z_mod_lt x (2 ^ 4)).
      rewrite wrap_small; lia.
  Qed.

  Lemma wp_node__entry (n: loc) (e: loc) :
    {{{ is_pkg_init hashtriemap ∗
        n.[hashtriemap.node.t, "isEntry"] ↦□ true ∗
        n.[hashtriemap.node.t, "ent"] ↦□ e }}}
      n @! (go.PointerType hashtriemap.node) @! "entry" #()
      {{{ RET #e; True }}}.
  Proof.
    wp_start as "(His_entry & Hent)".
    wp_auto.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_node__indirect (n: loc) (i: loc) :
    {{{ is_pkg_init hashtriemap ∗
        n.[hashtriemap.node.t, "isEntry"] ↦□ false ∗
        n.[hashtriemap.node.t, "ind"] ↦□ i }}}
      n @! (go.PointerType hashtriemap.node) @! "indirect" #()
      {{{ RET #i; True }}}.
  Proof.
    wp_start as "(His_entry & Hind)".
    wp_auto.
    iApply "HΦ"; done.
  Qed.

  Definition entry_hit_witness (γ: ghost_names) (q: Qp) (path: path) (key v: K) : iProp Σ :=
    ∃ e: loc,
      "#Hentry" :: entry γ q e path ∗
      "#Hk" :: e.[hashtriemap.entry.t, "key"] ↦□ key ∗
      "#Hv" :: e.[hashtriemap.entry.t, "value"] ↦□ v.

  Definition entry_lookup_result (γ: ghost_names) (q: Qp) (path: path) (key: K) (r: val) : iProp Σ :=
    ((∃ v: V, ⌜r = (#v, #true)%V⌝ ∗ entry_hit_witness γ q path key v) ∨
     ⌜r = (#(zero_val V), #false)%V⌝)%I.

  Lemma entry_hit_witness_lookup γ q path key v m hm :
    map_state γ m hm -∗
    entry_hit_witness γ q path key v -∗
    |==> ⌜m !! key = Some v⌝.
  Proof. Admitted.

  Lemma entry_lookup_false_result_sound γ key r m hm :
    map_state γ m hm -∗
    ⌜r = (#(zero_val V), #false)%V⌝ -∗
    ⌜m !! key = None⌝.
  Proof. Admitted.

  Lemma entry_lookup_result_to_load_ret γ q path key r m hm :
    entry_lookup_result γ q path key r -∗
    map_state γ m hm -∗
    ⌜r = ht_load_ret m key⌝.
  Proof. Admitted.

  Lemma load_entry_lookup_finish q (key: K) (γ: ghost_names) (path: path) (r: val)
    (Φ: val → iProp Σ) :
    entry_lookup_result γ q path key r -∗
    AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
      @ ht_au_mask, ∅
      <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }> -∗
    Φ r.
  Proof. Admitted.

  Lemma wp_entry__lookup q (e: loc) (key: K) (γ: ghost_names) (path: path) :
    {{{ "#Hinit" :: is_pkg_init hashtriemap ∗
        "%Hen" :: ⌜e ≠ null⌝ ∗
        "Hentry" :: entry γ q e path ∗
        "%Hbelongs" :: ⌜belongs_to_path path (uint.Z (hash_key key))⌝ }}}
      e @! (go.PointerType hashtriemap.entry) @! "lookup" #key
    {{{ r, RET r; entry_lookup_result γ q path key r }}}.
  Proof.
    wp_start as "Hpre".
    iNamed "Hpre".
    wp_auto_lc 1.

    iAssert (
        ∃ ecur,
          "e" :: e_ptr ↦ ecur ∗
          "Hentry" ::
            if decide (ecur = null) then
              entry_lookup_result γ q path key (#(zero_val V), #false)%V
            else
              "Hentry" :: entry γ q ecur path
      )%I with "[$e Hentry]" as "Hloop".
    { rewrite decide_False; [iFrame|done]. }

    wp_for "Hloop".
    wp_if_destruct.
    - wp_alloc ret as "ret".
      wp_auto.
      iSimpl in "Hentry".
      iApply "HΦ".
      iExact "Hentry".
    - iEval (rewrite (decide_False _ _ n)) in "Hentry".
      iDestruct "Hentry" as "#Hentry".
      iPoseProof "Hentry" as "#Hentry_saved".
      iApply fupd_wp.
      iEval (rewrite entry_unfold /entry_F) in "Hentry".
      iInv "Hentry" as "HEI" "Hclose_entry".
      unfold entry_inv.
      iMod (lc_fupd_elim_later with "[$] HEI") as "HEI".
      iNamed "HEI".

      destruct (bool_decide (k = key)) eqn:Heq_key.
      + apply bool_decide_eq_true in Heq_key.
        subst k.
        iMod ("Hclose_entry" with "[$Hk $Hv $Hown_next $Hown_entry $Hnext_entry]") as "_".
        { iNext; iPureIntro; cbn; exists h; done. }
        iModIntro.
        wp_auto.
        wp_if_destruct; [|exfalso; auto].
        wp_for_post.
        wp_end.
        iLeft.
        iExists v.
        iSplit; first eauto.
        iExists ecur.
        rewrite /entry_hit_witness /named.
        iSplitL "Hentry_saved"; first iExact "Hentry_saved".
        iSplitL "Hk"; first iExact "Hk".
        iExact "Hv".
      + apply bool_decide_eq_false in Heq_key.
        iMod ("Hclose_entry" with "[$Hk $Hv $Hown_next $Hown_entry $Hnext_entry]") as "_".
        { iNext; iPureIntro; cbn; exists h; done. }
        iModIntro.
        wp_auto_lc 1.
        rewrite bool_decide_eq_false_2; [|exact Heq_key].
        wp_auto_lc 2.
        wp_apply wp_Value__Load.
        iInv "Hentry" as "HEI" "Hclose_entry".
        unfold entry_inv.
        iMod (lc_fupd_elim_later with "[$] HEI") as "HEI".
        iNamedSuffix "HEI" "0".
        iCombine "Hk" "Hk0" gives %?.
        subst k.
        iApply fupd_mask_intro; [set_solver|].
        iIntros "Hmask".
        iNext.
        iFrame "Hown_next0".
        iIntros "Hown_next".
        destruct (decide (next0 = null)) eqn:Heq_next.
        * iMod "Hmask" as "_".
          iMod ("Hclose_entry" with "[Hown_entry0 Hown_next]") as "_".
          {
            iNext.
            iFrame.
            iFrame "#".
            iPureIntro.
            exists h.
            auto.
          }
          iModIntro.
          wp_auto.
          rewrite decide_True; [|reflexivity].
          wp_auto.
          wp_for_post.
          iFrame.
          rewrite /named.
          rewrite decide_True; [|exact e0].
          iRight. done.
        * iMod "Hmask" as "_".
          iMod ("Hclose_entry" with "[$Hown_entry0 $Hown_next]") as "_".
          {
            iNext.
            iFrame "#".
            iPureIntro.
            exists h.
            auto.
          }

          iSpecialize ("Hnext_entry0" $! n0).
          iMod (lc_fupd_elim_later with "[$] Hnext_entry0") as "#Hnext_entry1".

          iModIntro.
          wp_auto.
          rewrite decide_True; [|auto].
          wp_auto.
          wp_for_post.
          iFrame.
          rewrite decide_False; [|exact n0].
          rewrite /named.
          iExact "Hnext_entry1".
  Qed.

  Lemma wp_hashInt (key: w64) (seed: w64) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.hashInt #key #seed
      {{{ (a: w64), RET (#a); ⌜a = hash_key key⌝ }}}.
  Proof. Admitted.

  Lemma wp_newIndirectNode (γ: ghost_names) (parent: loc) (path: list Z) (hm: hash_map) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.newIndirectNode #parent
      {{{ (ind: loc), RET (#ind);
          indirect γ ind path }}}.
  Proof.
    wp_start as "Hpre".
    wp_auto.
    rename i_ptr into ind_ptr.
    iRename "i" into "ind".

    wp_apply (wp_slice_make2 (V:=atomic.Value.t)).
    { word. }
    iIntros (children) "(Hchildren & _)".
    wp_auto.
    wp_alloc ind_struct as "ind_struct".
    wp_auto.

    replace (sint.nat (W64 16)) with 16%nat by word.

    set (children_vs := replicate 16 (zero_val atomic.Value.t)).

    iAssert (
        ∃ (vs: list atomic.Value.t) (idx i: w64),
          "Hvs" :: children ↦* vs ∗
          "i" :: i_ptr ↦ i ∗
          "idx" :: idx_ptr ↦ idx ∗
          "%Hi_idx" :: ⌜sint.Z i >= sint.Z idx⌝ ∗
          "%Hi_bound" :: ⌜uint.Z i <= nChildren⌝ ∗
          "%Hlen" :: ⌜length vs = Z.to_nat nChildren⌝ ∗
          "%Hprefix" :: ⌜∀ (j: nat), j ≥ 0 → j < uint.Z i →
                                     ∃ av, vs !! j = Some av ∧
                                           av = atomic.Value.mk (interface.mk_ok (go.PointerType hashtriemap.node) (# null))⌝ ∗
                                           "%Hsuffix" :: ⌜∀ (j: nat), j >= uint.Z i → j < length vs → vs !! j = children_vs !! j⌝
      )%I with "[$Hchildren $i $idx]" as "IH".
    {
      iNamed.
      unfold nChildren.
      iPureIntro.
      simpl.
      split_and!; auto; try word.
      iIntros (j Hj Hj2).
      exfalso.
      word.
    }

    unfold nChildren in *.

    wp_for "IH".

    iDestruct (own_slice_len with "Hvs") as %Hlen_slice.

    wp_if_destruct.
    2: {
      wp_alloc node as "node".

      (* iStructNamedSuffix "node" "_node". *)
      (* simpl. *)
      (* iStructNamedSuffix "ind_struct" "_ind". *)
      (* simpl. *)
      wp_auto.

      iAssert (
          indirect γ ind_struct path
        )%I with "[Hvs node ind_struct]" as "Hinv".
      {
        (* TODO: whatever this invariant ends up being, need to prove it here with M=∅ *)
        admit.
      }

      iApply "HΦ".
      iFrame "Hinv".
    }

    (* wp_pure. *)
    (* { split; word. } *)

    have Hlookup_vs : (vs !! sint.nat i = Some (zero_val atomic.Value.t)).
    {
      have Hidx_lt : uint.nat i < length vs.
      { rewrite Hlen. word. }

      have Hsuffix_i : vs !! uint.nat i = children_vs !! uint.nat i.
      { apply Hsuffix; [lia|exact Hidx_lt]. }

      have Hsuit : sint.nat i = uint.nat i.
      { word. }

      rewrite Hsuit.
      rewrite Hsuffix_i.
      rewrite lookup_replicate_2; auto.
      word.
    }

    rewrite decide_True; [|word].
    wp_apply (wp_load_slice_index with "[$Hvs]"); auto; [word|].

    iIntros "Hvs".

    wp_auto.

    iDestruct ((own_slice_elem_acc) with "[$Hvs]") as "[Helem Hcont]"; eauto; [word|].

    rewrite decide_True; [|word].

    (* iAssert (own_Value (slice_index_ref atomic.Value.t (uint.Z i) children) 1 interface.nil)%I *)
    (*   with "[Helem]" as "Helem". *)
    (* { *)
    (*   auto. *)
    (* } *)

    wp_auto.

    wp_apply wp_Value__Store.

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iFrame "Helem".
    iIntros "Helem".
    iMod "Hmask".
    iClear "Hmask".
    iApply fupd_mask_intro.
    {set_solver. }
    iIntros "_".
    wp_auto.

    iDestruct ("Hcont" with "Helem") as "Hvs".

    wp_for_post.

    iFrame "HΦ ind ind_struct".

    iFrame.

    iSplit.
    { word. }

    iSplit.
    { word. }
    iSplit.
    {
      iPureIntro.
      rewrite length_insert.
      exact Hlen.
    }
    iSplit.
    - iPureIntro. intros j Hj_ge Hj_lt.

      have Hj_lte : j ≤ uint.Z i.
      { word. }
      clear Hj_lt.

      apply Z_le_lt_eq_dec in Hj_lte.
      destruct Hj_lte as [Hlt | Heq].

      + (* j < i *)
        specialize (Hprefix j) as Hprefix.
        specialize (Hprefix Hj_ge Hlt).
        destruct Hprefix as (av & Hlookup & Hav).
        exists av.
        split; auto.

        rewrite list_lookup_insert_ne; auto.
        word.
      + (* j = i *)
        exists {|
            atomic.Value.v' :=
              interface.mk_ok (go.PointerType hashtriemap.node) (# null)
          |}.
        split; auto.
        rewrite list_lookup_insert.
        have Hbool : (sint.nat i = j ∧ (sint.nat i < length vs)%nat)%nat.
        { word. }
        by destruct (decide (sint.nat i = j ∧ (sint.nat i < length vs)%nat)) as [H|H];
        [reflexivity | exfalso; exact (H Hbool)].
    - iPureIntro. intros j Hj_ge Hj_lt.

      have Hj_ge_i1_nat : (j ≥ uint.nat i + 1)%nat.
      { word. }
      have Hj_ge_i_Z : (j >= uint.Z i).
      { word. }
      have Hj_ge_i1_Z : (j >= uint.Z i + 1).
      { word. }
      have Hj_lt_len : (j < length vs).
      { rewrite length_insert in Hj_lt. word. }

      specialize (Hsuffix j) as Hsuffix.
      specialize (Hsuffix Hj_ge_i_Z Hj_lt_len).
      rewrite list_lookup_insert_ne; auto.
      word.
  Admitted.            (* only admitted because of the ind invariant needing proof *)

  Lemma wp_HashTrieMap__initSlow (ht: loc) (γ: ghost_names) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
        hashtriemap_init ht γ }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "initSlow" #()
      {{{ RET #();
          "His_map" :: is_hashtriemap γ ht }}}.
  Proof.
    wp_start as "Hpre".
    iNamed "Hpre".
    iRename "Hinit_mu" into "Hmu".

    wp_apply wp_with_defer as "%defer defer"; simpl subst.
    wp_auto.

    wp_apply (wp_Mutex__Lock with "[$Hmu]").
    iIntros "(Hown_mutex&Hmu_inv)".
    wp_auto.

    wp_apply wp_Uint32__Load.
    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & #Hstatus_done)" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iFrame.

    iIntros "Hinited".

    iDestruct (persistently_elim with "Hstatus_done") as "#Hstatus_done'".
    iClear "Hstatus_done".
    iRename "Hstatus_done'" into "Hstatus_done".

    destruct b; simpl in *.
    {
      iMod "Hmask".
      iClear "Hmask".
      iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
      { iNext; iFrame; iFrame "Hinited Hstatus_done". }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "_".
      wp_auto.

      wp_apply (wp_Mutex__Unlock with "[$Hmu $Hown_mutex $Hmu_inv]").

      iApply "HΦ"; done.
    }

    iDestruct "Hmu_inv" as (b) "Hmu_inv".
    destruct b.
    {
      iDestruct (ghost_var_agree with "Hmu_inv Hinit_tok") as %Heq.
      inversion Heq.
    }

    iMod "Hmask".
    iClear "Hmask".
    iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
    { iNext; iFrame; iFrame "Hstatus_done Hinited". }
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".
    wp_auto.

    (* TODO: have lemma to initialize empty_map, and give the ptsto_mut part to newIndirectNode and the auth_map used for constructing ht_inv below *)
    wp_apply (wp_newIndirectNode γ null [] ∅).
    iIntros (root_node_ptr) "root_node".
    wp_auto.

    iFrame.
    wp_apply wp_Value__Store.

    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & _)" "Hclose".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hmask".
    iNext.
    iFrame.
    iExists interface.nil.

    iDestruct "Hmu_inv" as "(Hinit_tok2 & Hseed & Hroot)".
    iDestruct (ghost_var_agree with "Hinit_tok Hinit_tok2") as %Heq.
    subst b.

    iFrame.

    iIntros "Hroot".
    iMod "Hmask".
    iClear "Hmask".
    iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
    {
      iNext.
      iFrame.
      iFrame "Hstatus_done Hinited".
    }

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".
    wp_auto.

    iDestruct "Hseed" as (seed) "Hseed".

    wp_auto.
    iPersist "Hseed".

    wp_apply wp_Uint32__Store.

    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & _)" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iFrame.
    iIntros "Hinited".
    iMod "Hmask".
    iClear "Hmask".
    destruct b.
    {
      iDestruct (ghost_var_agree with "Hinit_tok Hinit_tok2") as %Heq.
      exfalso. congruence.
    }

    iMod (ghost_var_update_halves true with "Hinit_tok Hinit_tok2") as "(Htok1 & Htok2)".

    iAssert (ht_inv γ ht)%I (* with "[$]" *) as "Hhtinv".
    {
      admit.
    }

    iMod (invariants.inv_alloc mapN _ (
              "Hinv" :: ht_inv γ ht
            ) with "[$Hhtinv]") as "#His_map".

    iMod ("Hclose" with "[Htok1 Hinited His_map]") as "_".
    { iNext. iFrame. iFrame "Hinited". unfold init_status_done. unfold is_hashtriemap. iFrame "#". }
    iApply fupd_mask_intro.
    {set_solver. }
    iIntros "_".
    wp_auto.

    iAssert (init_mu_inv ht γ)%I with "[Htok2]" as "Hmu_inv_true".
    { simpl. iExists true. iFrame "Htok2". }

    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hown_mutex $Hmu_inv_true]").
    iApply "HΦ".
    iFrame.
    unfold is_hashtriemap.
    iFrame "#".
  Admitted.

  (*precondition: either inited is 0 and we call initSlow, or its 1 and we already have the initialization requirements*)
  Lemma wp_HashTrieMap__initHT (ht: loc) (γ: ghost_names) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
        hashtriemap_init ht γ }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "initHT" #()
      {{{ RET #();
          "His_map" :: is_hashtriemap γ ht }}}.
  Proof.
    wp_start as "Hpre".
    iNamed "Hpre".
    iRename "Hinit_mu" into "Hmu".

    wp_auto.

    wp_apply wp_Uint32__Load.
    iInv "Hinit" as "Hinit2" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iDestruct "Hinit2" as (b) "(Hinited & Hinit_tok & #Hstatus_done)".
    iFrame.
    iIntros "Hinited".
    iMod "Hmask".
    iClear "Hmask".
    iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
    { iNext. iFrame. iFrame "Hstatus_done". }
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".
    wp_auto.

    wp_if_destruct.
    - wp_apply (wp_HashTrieMap__initSlow).
      { iFrame. iFrame "Hinit Hmu". }
      iIntros.
      wp_auto.
      iApply "HΦ".
      iFrame "#".
    - iApply "HΦ".
      iFrame.
      unfold is_hashtriemap.
      simpl in n.
      destruct b; simpl.
      + iFrame "#".
      + congruence.
  Qed.

  Lemma wp_load_root γ (ht: loc) :
    ∀ Φ,
    (is_pkg_init atomic ∗
     "His_map" ∷ (ht_inv γ ht)) -∗
    (∀ root : loc,
       "#Hroot_indirect" :: indirect γ root [] -∗
       Φ #root)
    -∗
    WP TypeAssert (go.PointerType hashtriemap.indirect)
      ((ht.[hashtriemap.HashTrieMap.t, "root"]) @!
         (go.PointerType atomic.Value) @! "Load"
         (# ()))
      {{ v, Φ v }}.
  Proof.
    wp_start_folded as "Hpre".
    iNamed.
    wp_apply (wp_Value__Load with "[$]").
    iInv "His_map" as "[Hroot Hmap]" "Hclose".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hmask".
    iNext.
    iNamed "Hroot".
    iFrame "Hown_root".
    iIntros "Hown_root".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    rewrite decide_True; [|reflexivity].
    wp_end.
  Qed.

  (* dont actually need the is_hashtriemap precondition for any of the lemmas because initHT gives it to us *)
  Lemma wp_HashTrieMap__Load (ht: loc) (key: w64) (γ: ghost_names) :
    ∀ (Φ: val → iProp Σ),
    (is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync)
    -∗
    ("Hinit" :: hashtriemap_init ht γ ∗
     "Hau" ::
       AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
       @ ht_au_mask, ∅
                     <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }>) -∗
    WP ht @! (go.PointerType hashtriemap.HashTrieMap) @! "Load" #key {{ Φ }}.
  Proof.
    wp_start.
    iNamed "HΦ".

    wp_auto.

    wp_apply (wp_HashTrieMap__initHT with "[$]").
    iIntros.
    iNamed.
    iNamed "His_map".
    iNamed "Hseed".
    wp_auto.

    wp_apply wp_hashInt.
    iIntros (hash) "%Hhash".

    wp_auto.

    wp_bind (TypeAssert _ _).

    iApply (wp_load_root with "[# $]").
    iIntros.
    iNamed.
    wp_auto.

    set h := uint.Z (hash_key key).

    iAssert (∃ (path: path) (shift: Z) (cur: loc),
                "Hcur" :: i_ptr ↦ cur ∗
                "Hhash_shift" :: hashShift_ptr ↦ W64 shift ∗
                "#Hi_indirect" :: indirect γ cur path ∗
                "%Hshift" :: ⌜shift = sh path⌝ ∗
                "%Hpath_len" :: ⌜length path < 16⌝ ∗
                "%Hkey_path" :: ⌜belongs_to_path path h⌝
            )%I with ("[$Hroot_indirect $hashShift $i]") as "Hloop_inv".
    {
      repeat iSplit; eauto.
      iPureIntro.
      unfold belongs_to_path, sh, path_to_prefix.
      simpl.
      rewrite Z.shiftr_div_pow2; word.
    }
    iClear "Hroot_indirect".
    clear root.

    wp_for "Hloop_inv".

    iEval (rewrite indirect_unfold /indirect_F) in "Hi_indirect".
    iNamed "Hi_indirect".

    rewrite bool_decide_false.
    2: {
      replace shift with (sh path).
      unfold sh.
      word.
    }
    rewrite decide_True; [|auto].
    wp_auto.

    iDestruct (own_slice_len with "Hchildren_slice") as %Hlen_children.

    subst hash.
    rewrite Hshift.
    rewrite next_nibble_eq; [|exact Hpath_len].
    set next_nibble := (Z.land (uint.Z (hash_key key) ≫ (sh path - 4)) 15).
    replace (sint.Z children_slice.(slice.len)) with 16 by word.

    have Hnib_u : 0 ≤ next_nibble < 16.
    {
      subst next_nibble.
      replace 15 with (Z.ones 4) by reflexivity.
      rewrite Z.land_ones; [|word].
      word.
    }
    rewrite decide_True; [|word].

    destruct (lookup_lt_is_Some_2 children_vals (Z.to_nat next_nibble))
      as [v Hv].
    { word. }

    wp_auto.

    have Hdom : h ∈ path_to_domain path by rewrite -in_domain.

    wp_apply wp_Value__Load.
    iInv "His_map" as "[Hroot >Hmap]" "Hclose_ht".
    iInv "Hind_inv" as "HI" "Hclose_ind".

    unfold own_ht_map.
    iApply fupd_mask_intro.
    { apply empty_subseteq. }
    iIntros "Hmask".
    iNext.

    iEval (unfold childrenP) in "HI".

    iNamed.
    iNamed "Hmap".

    iDestruct (big_sepL_lookup_acc with "Hchildren") as "[Hchild Hchildren_close]"; [exact Hv|].
    replace (Z.of_nat (Z.to_nat next_nibble)) with next_nibble by word.
    iNamed "Hchild".
    iFrame "Hown_child".
    iIntros "Hown_child".

    unfold ht_load_ret.
    iEval (unfold childP) in "Hchild".

    set next_path := (path ++ [next_nibble]).

    have Hlen : length next_path = (length path + 1)%nat by
                                     rewrite app_length /=.

    have Hh : h = uint.Z (hash_key key) by reflexivity.
    have Hdom_child : h ∈ path_to_domain next_path.
    {
      have H : belongs_to_path next_path h.
      {
        rewrite /belongs_to_path.
        apply (next_nibble_extend path h next_nibble).
        { word. }
        all: done.
      }
      rewrite -in_domain; done.
    }

    destruct (decide (nodeptr = null)).
    {
      iMod "Hmask" as "_".

      iMod (fupd_mask_subseteq ht_au_mask) as "Hclose_au_mask".
      {
        unfold ht_au_mask.
        apply subseteq_difference_l.
        set_solver.
      }

      iMod "Hau" as (m) "[Hown Hclose_au]". (* linearization point *)
      iDestruct (map_state_agree with "Hmap Hown") as %Heq.
      subst m.

      iDestruct (user_map_lookup Hdom_child Hh with "Hmap Hchild") as %Hum.

      iDestruct ("Hchildren_close" with "[Hown_child Hchild]") as "Hchildren".
      {
        iExists nodeptr.
        iFrame.
        unfold childP.
        rewrite decide_True; [|done].
        iFrame.
      }

      iMod ("Hclose_au" with "Hown") as "HΦ".
      iMod "Hclose_au_mask" as "_".
      iMod ("Hclose_ind" with "Hchildren") as "_".
      iMod ("Hclose_ht" with "[$Hroot $Hmap]") as "_".

      iModIntro.

      wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

      rewrite bool_decide_true; [|exact e].

      wp_auto.
      wp_alloc d_ptr as "d_ptr".
      wp_auto.
      wp_for_post.

      unfold empty_map_fn in Hum.
      rewrite lookup_empty in Hum.

      iEval (rewrite Hum; simpl) in "HΦ".

      wp_end.
    }

    iNamed "Hchild".

    destruct is_entry.
    {
      iEval (unfold entry_node) in "Hchild".
      iNamed "Hchild".
      iMod "Hmask" as "_".

      iMod (fupd_mask_subseteq ht_au_mask) as "Hclose_au_mask".
      {
        unfold ht_au_mask.
        apply subseteq_difference_l.
        set_solver.
      }

      iDestruct ("Hchildren_close" with "[Hown_child Hown_path]") as "Hchildren".
      {
        iExists nodeptr. iFrame. unfold childP.
        rewrite (decide_False _ _ n).
        iExists true.
        rewrite /named.
        iSplit; eauto.
        unfold entry_node.
        iExists ent.
        iExists map.
        iExists hash.
        iFrame "Hown_path".
        iFrame "#".
        done.
      }

      iMod "Hclose_au_mask" as "_".
      iMod ("Hclose_ind" with "Hchildren") as "_".
      iMod ("Hclose_ht" with "[$Hroot $Hmap]") as "_".

      iModIntro.

      wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

      rewrite bool_decide_false; [|done].

      wp_auto.

      wp_apply (wp_node__entry with "[# $]").
      wp_apply (wp_entry__lookup with "[$Hchild_entry]").
      { iFrame "#".
        rewrite /named.
        repeat iSplit; eauto.
        iPureIntro.
        subst h.
        rewrite in_domain; [|auto].
        exact Hdom_child.
      }
      iIntros (r) "Hres".
      iDestruct "Hres" as "[Hhit|%Hfalse]".
      - iDestruct "Hhit" as (vhit) "(%Hr & Hwit)".
        rewrite Hr.
        wp_auto.
        wp_for_post.
        iPoseProof (load_entry_lookup_finish (1/2)%Qp key γ next_path (#vhit, #true)%V Φ with "[Hwit] Hau") as "HΦ".
        { iLeft. iExists vhit. iSplit; first eauto. iExact "Hwit". }
        iExact "HΦ".
      - rewrite Hfalse.
        wp_auto.
        wp_for_post.
        iPoseProof (load_entry_lookup_finish (1/2)%Qp key γ next_path (#(zero_val V), #false)%V Φ with "[] Hau") as "HΦ".
        { iRight. iPureIntro. reflexivity. }
        iExact "HΦ".
    }
    unfold indirect_node.
    iNamed "Hchild".

    iDestruct ("Hchildren_close" with "[Hown_child]") as "Hchildren".
    { iExists nodeptr. iFrame. unfold childP.
      rewrite (decide_False _ _ n).
      iExists false. iFrame "#".
      iPureIntro. split; done.
    }

    iMod "Hmask" as "_".
    iMod ("Hclose_ind" with "Hchildren") as "_".
    iMod ("Hclose_ht" with "[$]") as "_".

    iModIntro.

    wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

    rewrite bool_decide_false; [|exact n].

    wp_auto.
    wp_apply (wp_node__indirect with "[$]").
    wp_for_post.
    replace (w64_word_instance.(word.sub)
                                 (W64 (sh path)) (W64 4)) with (W64 (sh path - 4)) by word.
    iFrame.
    iFrame "#".
    iPureIntro.

    split_and!; auto; try done.
    - rewrite sh_snoc.
      reflexivity.
    - rewrite in_domain; [exact Hdom_child|].
      apply Hh.
  Qed.

End proof.
