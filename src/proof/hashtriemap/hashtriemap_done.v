From iris.bi.lib Require Import atomic.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From Perennial.algebra Require Import ghost_var.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Import paths.
From New.proof.hashtriemap Require Import model.

Open Scope Z_scope.

Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}
    `{!ghost_varG Σ bool}
    `{!ghost_varG Σ (gmap w64 w64)}
    `{!mapG Σ w64 w64}
    `{!mapG Σ Z (gmap w64 w64)}
    `{!globalsGS Σ} {go_ctx: GoContext}.

  Definition map_get `{!IntoVal V} `{!IntoValTyped V t} (v: option V) : V * bool :=
    (default (default_val V) v, bool_decide (is_Some v)).

  #[global] Instance : IsPkgInit hashtriemap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf hashtriemap := build_get_is_pkg_init_wf.

  Lemma next_nibble_eq (key: w64) (path: path) :
    let h := uint.Z (hash_key key) in
    let n := w64_word_instance.(word.and)
                                 (w64_word_instance.(word.sru) (hash_key key)
                                                      (w64_word_instance.(word.sub) (W64 (sh path)) (W64 4)))
                                 (W64 15) in
    length path < 16 → uint.Z n = Z.land (h ≫ (sh path - 4)) 15.
  Proof.
    intros.
    (* subst n. *)
    (* zify. *)
    unfold h.
    rewrite word.unsigned_and_nowrap.
    rewrite word.unsigned_sru.
    - rewrite word.unsigned_sub.
      f_equiv; [|word].
      unfold sh.
      rewrite wrap_small; auto.
      + f_equiv.
        word.
      + replace (uint.Z (W64 (64 - 4 * length path))) with (64 - 4 * length path) by word.
        replace (uint.Z (W64 4)) with 4 by word.
        replace (w64_word_instance_ok.(word.wrap) (64 - 4 * length path - 4)) with (64 - 4 * length path - 4) by word.
        unfold sh in *.
        have Hx : ((64 - 4 * length path - 4)) ≥ 0 by lia.
        have Hrng : 0 ≤ uint.Z (hash_key key) < 2^64 by word.
        split.
        * apply Z.shiftr_nonneg. lia.
        * destruct Hrng as [_ Hrng].
          apply (Z.le_lt_trans _ (uint.Z (hash_key key))); [|exact Hrng].
          set x := uint.Z (hash_key key).
          rewrite Z.shiftr_div_pow2; [|word].
          apply Z.div_le_upper_bound; [word|].
          set z := 2 ^ (64 - 4 * length path - 4).
          have Hz : 1 ≤ z.
          {
            replace 1 with (2^0) by lia.
            apply Z.pow_le_mono_r; lia.
          }
          replace (z * x) with (x * z) by lia.
          clear Hx.
          have Hx : 0 ≤ x by word.
          have Hy : 1 ≤ z by lia.
          have : x * 1 ≤ x * z.
          { apply (Z.mul_le_mono_nonneg_l _ _ _ Hx).
            exact Hy. }
          word.
    - replace (w64_word_instance.(word.sub) (W64 (sh path)) (W64 4)) with (W64 (sh path - 4)) by word.
      unfold sh.
      replace (uint.Z (W64 (64 - 4 * length path - 4))) with (64 - 4 * length path - 4) by word.
      word.
  Qed.

  Lemma wp_node__entry (n: loc) (e: loc) :
    {{{ is_pkg_init hashtriemap ∗
        n ↦s[hashtriemap.node :: "isEntry"]□ true ∗
        n ↦s[hashtriemap.node :: "ent"]□ e }}}
      n @ (ptrT.id hashtriemap.node.id) @ "entry" #()
      {{{ RET #e; True }}}.
  Proof.
    wp_start as "(His_entry & Hent)".
    wp_auto.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_node__indirect (n: loc) (i: loc) :
    {{{ is_pkg_init hashtriemap ∗
        n ↦s[hashtriemap.node :: "isEntry"]□ false ∗
        n ↦s[hashtriemap.node :: "ind"]□ i }}}
      n @ (ptrT.id hashtriemap.node.id) @ "indirect" #()
      {{{ RET #i; True }}}.
  Proof.
    wp_start as "(His_entry & Hind)".
    wp_auto.
    iApply "HΦ"; done.
  Qed.

  (* precondition: returns value, true if k is in kvs *)
  Lemma wp_entry__lookup (ht: loc) (e: loc) (key: K) (γ: ghost_names) (path: path) :
    ∀ (Φ: val → iProp Σ),
    is_pkg_init hashtriemap -∗
    "Hpre" :: (
        "#His_map" :: is_hashtriemap γ ht ∗
        "%Hen" ∷ ⌜e ≠ null⌝ ∗
        "Hentry" :: entry γ (1 / 2) e path ∗
        "Hau" :: (AU <{ ∃∃ m, own_ht_map γ m }>
                    @ ht_au_mask, ∅
                  <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }>) ∗
        "%Hbelongs" :: ⌜belongs_to_path path (uint.Z (hash_key key))⌝
      ) -∗
    WP e @ (ptrT.id hashtriemap.entry.id) @ "lookup" #key {{ Φ }}.
  Proof.
    intros.
    set h := (uint.Z (hash_key key)).
    iIntros.
    iNamed.
    iNamed "Hpre".
    wp_method_call. wp_call.

    wp_auto.

    iAssert (
        ∃ e,
          "e" :: e_ptr ↦ e ∗
          "Hentry" ::
            if decide (e = null) then
              Φ (ht_load_ret ∅ key)
            else
              "Hau" ∷ (AU <{ ∃∃ m, own_ht_map γ m }>
                         @ ht_au_mask, ∅
                                       <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }>) ∗
              "Hentry" ∷ entry γ (1 / 2) e path
      )%I with "[$e Hentry Hau]" as "Hloop".
    { rewrite decide_False; [iFrame|done]. }
    clear Hen e.

    wp_for "Hloop".

    wp_if_destruct.
    {
      wp_alloc ret as "ret".
      wp_auto.
      unfold ht_load_ret.
      iSimpl in "Hentry".
      iApply "Hentry".
    }

    iRevert "Hentry".
    rewrite decide_False; [|exact n].
    iIntros "Hentry".
    iNamed "Hentry".

    (* { *)
    (*   iApply wp_fupd. *)
    (*   wp_alloc ret as "ret". *)
    (*   wp_auto. *)

    (*   (* iEval (rewrite decide_False) in "Hentry". *) *)
    (*   iEval (rewrite entry_unfold /entry_F) in "Hentry". *)
    (*   iNamed "His_map". *)
    (*   iInv "His_map" as (rooti hm user_map) "(>? & >? & >? & #Hroot_indirect & >? & >? & >?)" "Hclose_map". *)
    (*   iNamed. *)
    (*   iInv "Hentry_inv" as "HEI" "Hclose_entry". *)
    (*   unfold entry_inv. *)
    (*   iSimpl in "HEI". *)
    (*   iMod "HEI" as "Hown_empty". *)
    (* (* iDestruct "HEI" as (next k v h0 rest_map) "(>? & >? & >? & >? & >? & >? & HEI)". *) *)
    (* (* iNamed. *) *)
    (*   (* iInv "Hentry_inv" as "HEI" "Hclose_entry". *) *)
    (*   (* unfold entry_inv. *) *)
    (*   (* iEval (simpl) in "HEI". *) *)
    (*   (* iMod "HEI". *) *)
    (*   (* iNamed. *) *)
    (*   (* iMod (fupd_mask_subseteq (⊤ ∖ ↑mapN ∖ ↑indN ∖ ↑entryN)) as "Hclose_au_mask"; [set_solver|]. *) *)
    (*   iMod "Hau" as (m) "[Hown Hclose_au]". *)

    (*   iDestruct (ghost_var_agree with "Hown Huser_map") as %Heq. *)
    (*   subst m. *)

    (*   have Hdom : h ∈ path_to_domain path. *)
    (*   { *)
    (*     rewrite list_elem_of_filter. *)
    (*     split; [exact Hbelongs|]. *)
    (*     apply full_domain_elem. *)
    (*   } *)

    (*   iDestruct (own_path_lookup _ _ _ h with "Hown_empty") as "[Hptsto Hptsto_close]"; [exact Hdom|]. *)
    (*   iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup. *)
    (*   iDestruct ("Hptsto_close" with "Hptsto") as "Hown_empty". *)

    (*   have Hnone : user_map !! key = None. *)
    (*   { *)
    (*     rewrite Hflat. *)
    (*     rewrite (Hbuckets _ _ _ Hlookup); done. *)
    (*   } *)

    (*   iNamed. *)

    (*   iMod ("Hclose_au" with "[$]") as "HΦ". *)
    (*   (* iMod "Hclose_au_mask" as "_". *) *)
    (*   iMod ("Hclose_entry" with "[Hown_empty]") as "_"; [iNext; done|]. *)
    (*   iMod ("Hclose_map" with "[$Hauth_map $Hown_root $Hroot_indirect $Hown //]") as "_". *)
    (*   iApply fupd_mask_intro; [set_solver|]. *)
    (*   iIntros "_". *)
    (*   unfold ht_load_ret. *)
    (*   iEval (rewrite Hnone; simpl) in "HΦ". *)
    (*   iApply "HΦ". *)
    (* } *)

    iApply fupd_wp.
    rewrite entry_unfold /entry_F.
    iNamed.

    iInv "Hentry_inv" as "HEI" "Hclose_entry".
    unfold entry_inv.
    destruct (decide (e = null)); [exfalso; auto|].
    iDestruct "HEI" as (next k v h0 rest_map) "(>? & >? & >? & >? & >? & >? & HEI)".
    iNamed.

    destruct (bool_decide (k = key)) eqn:Heq_key.
    - apply bool_decide_eq_true in Heq_key.
      replace h0 with h by (unfold h; subst; reflexivity).

      iNamed "His_map".
      iInv "His_map" as "[Hroot >Hmap]" "Hclose_map".
      iNamed "Hmap".
      iNamed "Hmap".
      iMod (fupd_mask_subseteq (⊤ ∖ ↑mapN ∖ ↑indN ∖ ↑entryN)) as "Hclose_au_mask"; [set_solver|].
      iMod "Hau" as (m) "[Hown Hclose_au]".

      (* linearization point *)

      iDestruct (map_state_agree with "Hmap Hown") as %Heq.
      subst m.

      have Hdom : h ∈ path_to_domain path by apply (in_domain _ (hash_key key)).

      have Hh : h = uint.Z (hash_key key) by reflexivity.
      iDestruct (user_map_lookup Hdom Hh with "Hmap Hown_path") as %Hsome.
      revert Hsome.
      unfold singleton_map_fn.
      rewrite decide_True; [|reflexivity].
      rewrite lookup_insert.
      rewrite Heq_key.
      rewrite decide_True; [|reflexivity].
      intro Hsome.

      iNamed.

      iMod ("Hclose_au" with "[$]") as "HΦ".
      iMod "Hclose_au_mask" as "_".
      iMod ("Hclose_map" with "[$Hmap $Hroot]") as "_".
      iMod ("Hclose_entry" with "[$Hown_path $HEI $Hown_next]") as "_".
      {
        iNext.
        iFrame "#".
        iPureIntro; subst k; done.
      }

      iApply fupd_mask_intro; [set_solver|].
      iIntros "_".
      wp_auto.
      wp_if_destruct; [|exfalso; auto].

      wp_for_post.

      unfold ht_load_ret.

      iEval (rewrite Hsome; simpl) in "HΦ".
      wp_end.
    - apply bool_decide_eq_false in Heq_key.

      iMod ("Hclose_entry" with "[$Hown_path $HEI $Hown_next]") as "_";
        [ iNext; iFrame "#"; iPureIntro; done |].

      iApply fupd_mask_intro; [set_solver|].
      iIntros "_".

      wp_auto.

      wp_if_destruct; [exfalso; auto|].
      clear n1.
      wp_apply wp_Value__Load.

      iInv "Hentry_inv" as "HEI" "Hclose_entry".
      unfold entry_inv.
      destruct (decide (e = null)); [exfalso; auto|].
      iNamed "HEI".
      iDestruct "HEI" as (next0 k0 v0 h0 rest_map0) "(>Hk0 & >Hv0 & >? & >? & >? & >? & HEI)".

      iNamedSuffix "Hk0" "0".
      iCombine "Hk" "Hk0" gives %[? ?].

      iClear "Hk".
      iClear "Hv".
      subst k.
      (* clear Hbelongs. *)
      (* rename Hbelongs0 into Hbelongs. *)
      (* clear Heq_key. *)
      clear n0.
      clear next.
      rename next0 into next.
      clear v rest_map.
      iNamed.

      destruct (decide (e = null)); [exfalso; auto|].

      iApply fupd_mask_intro; [set_solver|].
      iIntros "Hmask".
      iNext.

      iNamed.
      iFrame "Hown_next".
      iIntros "Hown_next".

      destruct (decide (next = null)) eqn:Heq_next.
      + iNamed "His_map".
        iMod "Hmask" as "_".
        iInv "His_map" as "[Hroot >Hmap]" "Hclose_map".
        iNamed "Hmap".
        iNamed "Hmap".
        iMod "Hau" as (m) "[Hown Hclose_au]".

        iDestruct (map_state_agree with "Hmap Hown") as %Heq.
        subst m.

        have Hdom : h ∈ path_to_domain path by apply (in_domain _ (hash_key key)).

        have Hh : h = uint.Z (hash_key key) by reflexivity.
        iDestruct (user_map_lookup Hdom Hh with "Hmap Hown_path") as %Hsome.
        (* revert Hsome. *)
        (* unfold singleton_map_fn. *)
        (* rewrite decide_True; [|reflexivity]. *)
        (* rewrite lookup_insert. *)
        (* rewrite Heq_key. *)
        (* rewrite decide_True; [|reflexivity]. *)
        (* intro Hsome. *)

        iDestruct "HEI" as %Hrest_null.
        subst rest_map0.
        unfold singleton_map_fn in Hsome.

        (* iDestruct (hm_lookup with "Hown_path") as %Hlookup. *)

        (* iDestruct (own_path_lookup _ _ _ _ _ Hdom with "Hown_path") as "[Hptsto Hptsto_close]". *)
        (* iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup. *)
        (* iDestruct ("Hptsto_close" with "Hptsto") as "Hown_empty". *)

        have Hnone : user_map !! key = None.
        {
          destruct (decide (h = h0)).
          - rewrite lookup_insert in Hsome.
            rewrite decide_False in Hsome; auto.
          - rewrite lookup_empty in Hsome.
            done.
        }

        iNamed.

        iMod ("Hclose_au" with "[$]") as "HΦ".
        iMod ("Hclose_map" with "[$Hroot $Hmap]") as "_".
        iMod ("Hclose_entry" with "[Hown_path Hown_next]") as "_".
        {
          iNext.
          iFrame.
          iFrame "#".
          rewrite decide_True; done.
        }
        iApply fupd_mask_intro; [set_solver|].
        iIntros "_".
        unfold ht_load_ret.
        iEval (rewrite Hnone; simpl) in "HΦ".
        wp_apply wp_interface_type_assert; [auto|].

        wp_for_post.
        iFrame.
        rewrite decide_True; [|exact e0].
        rewrite lookup_empty.
        wp_end.
      + iNamed "HEI".

        iMod "Hmask" as "_".
        iMod ("Hclose_entry" with "[$Hown_path $Hown_next]") as "_".
        {
          iNext.
          rewrite decide_False; [|exact n2].
          iFrame "#".
          iPureIntro; done.
        }

        iApply fupd_mask_intro; [set_solver|].
        iIntros "_".

        wp_apply wp_interface_type_assert; [auto|].

        wp_for_post.
        iFrame.
        rewrite decide_False; [|exact n2].
        iFrame "Hau".
        iFrame "Hnext_entry".
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
    { unfold hashtriemap.nChildren. word. }
    iIntros (children) "(Hchildren & _)".
    wp_auto.
    wp_alloc ind_struct as "ind_struct".
    wp_auto.

    set (children_vs := replicate (sint.nat (W64 hashtriemap.nChildren))
                          atomic.into_val_typed_Value.(default_val atomic.Value.t)).

    iAssert (
        ∃ (vs: list atomic.Value.t) (idx i: w64),
          "Hvs" :: children ↦* vs ∗
          "i" :: i_ptr ↦ i ∗
          "idx" :: idx_ptr ↦ idx ∗
          "%Hi_idx" :: ⌜sint.Z i >= sint.Z idx⌝ ∗
          "%Hi_bound" :: ⌜uint.Z i <= hashtriemap.nChildren⌝ ∗
          "%Hlen" :: ⌜length vs = Z.to_nat hashtriemap.nChildren⌝ ∗
          "%Hprefix" :: ⌜∀ (j: nat), j ≥ 0 → j < uint.Z i →
                                     ∃ av, vs !! j = Some av ∧
                                           av = atomic.Value.mk (interface.mk (ptrT.id hashtriemap.node.id) (# null))⌝ ∗
                                           "%Hsuffix" :: ⌜∀ (j: nat), j >= uint.Z i → j < length vs → vs !! j = children_vs !! j⌝
      )%I with "[$Hchildren $i $idx]" as "IH".
    {
      iNamed.
      unfold hashtriemap.nChildren.
      iPureIntro.
      simpl.
      split_and!; auto; try word.
      iIntros (j Hj Hj2).
      exfalso.
      word.
    }

    wp_for "IH".

    iDestruct (own_slice_len_keep with "Hvs") as "(Hvs & %Hlen_slice & _)".

    wp_if_destruct.
    2: {
      wp_alloc node as "node".

      iApply struct_fields_split in "ind_struct".
      iNamed "ind_struct".
      iApply struct_fields_split in "node".
      iNamed "node".
      simpl.
      wp_auto.

      iAssert (
          indirect γ ind_struct path
        )%I with "[Hvs Hnode Hdead Hmu Hparent Hchildren HisEntry Hent Hind]" as "Hinv".
      {
        (* TODO: whatever this invariant ends up being, need to prove it here with M=∅ *)
        admit.
      }

      iApply "HΦ".
      iFrame "Hinv".
    }

    wp_pure.
    { split; word. }

    have Hlookup_vs : (vs !! sint.nat i = Some (atomic.into_val_typed_Value.(default_val atomic.Value.t))).
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

    wp_apply (wp_load_slice_elem with "[$Hvs]"); auto.
    { word. }

    iIntros "Hvs".

    wp_auto.

    wp_pure.
    { split; cbn; word. }

    wp_auto.

    iDestruct ((own_slice_elem_acc) with "[$Hvs]") as "[Helem Hcont]"; eauto.
    { word. }

    iAssert (own_Value (slice.elem_ref_f children atomic.Value i) 1 interface.nil)%I
      with "[Helem]" as "Helem".
    {
      auto.
    }

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
        exists {| atomic.Value.v' := interface.mk (ptrT.id hashtriemap.node.id) (# null) |}.
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
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "initSlow" #()
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

    wp_apply (wp_store_ty with "Hseed").
    Unshelve.
    2: { eapply into_val_typed_w64. }

    iIntros "Hseed".
    iPersist "Hseed".

    wp_auto.
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
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "initHT" #()
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
      destruct b; simpl.
      + iFrame "#".
      + exfalso. congruence.
  Qed.

  Lemma wp_load_root γ (ht: loc) :
    ∀ Φ,
    (is_pkg_init atomic ∗
     "His_map" ∷ (ht_inv γ ht)) -∗
    (∀ root : loc,
       "#Hroot_indirect" :: indirect γ root [] -∗
       Φ #root)
    -∗
    WP interface.type_assert
      (#
         (method_callv (ptrT.id atomic.Value.id) "Load"
            (#(struct.field_ref_f hashtriemap.HashTrieMap "root" ht)))
         (#()))
      (#(ptrT.id hashtriemap.indirect.id))
      {{ v, Φ v }}.
  Proof.
    wp_start_folded as "Hpre".
    iNamed.
    wp_apply (wp_Value__Load with "[$]").
    iInv "His_map" as "Hhtinv" "Hclose".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hmask".
    iNext.
    iNamed "Hhtinv".
    iNamed "Hroot".
    iNamed "Hroot".
    iNamed "Hown_root".
    iFrame "Hown_root".
    iIntros "Hown_root".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_apply wp_interface_type_assert; [auto|].
    wp_end.
  Qed.

  (* dont actually need the is_hashtriemap precondition for any of the lemmas because initHT gives it to us *)
  Lemma wp_HashTrieMap__Load (ht: loc) (key: w64) (γ: ghost_names) :
    ∀ (Φ: val → iProp Σ),
    (is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
     "Hinit" :: hashtriemap_init ht γ ∗
     "Hau" ::
       AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
       @ ht_au_mask, ∅
                     <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }>) -∗
    WP ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Load" #key {{ Φ }}.
  Proof.
    iIntros (Φ) "(#? & #? & #? & Hpre)".
    iNamed "Hpre".

    wp_method_call. wp_call.

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

    wp_bind (interface.type_assert _ _).

    iApply (wp_load_root with "[# $]").
    iIntros.
    iNamed.
    wp_auto.

    set h := uint.Z (hash_key key).

    iAssert (∃ (path: path) (shift: w64) (cur: loc),
                "Hcur" :: i_ptr ↦ cur ∗
                "Hhash_shift" :: hashShift_ptr ↦ shift ∗
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
      rewrite Z.shiftr_div_pow2; try word.
    }
    iClear "Hroot_indirect".
    clear root.

    wp_for "Hloop_inv".

    iEval (rewrite indirect_unfold /indirect_F) in "Hi_indirect".
    iNamed "Hi_indirect".

    wp_if_destruct.
    {
      wp_apply wp_panic.
      iPureIntro.
      unfold sh in e.
      word.
    }

    iDestruct (own_slice_len with "Hchildren_slice") as "(%Hlen_children_16 & _)".
    have Hlen_children : uint.Z children_slice.(slice.len_f) = 16.
    { word. }
    clear Hlen_children_16.

    unfold hashtriemap.nChildrenLog2, hashtriemap.nChildrenMask in *.
    wp_pure.
    {
      have Hlen16 : uint.Z children_slice.(slice.len_f) = 16 by word.
      set (x := w64_word_instance.(word.sru) (hash_key key)
                                    (w64_word_instance.(word.sub) (W64 (64 - 4 * length path)) (W64 4))).
      have Hnib_u : 0 ≤ uint.Z (w64_word_instance.(word.and) x (W64 15)) < 16.
      {
        rewrite word.unsigned_and_nowrap.
        change (uint.Z (W64 15)) with 15.
        change 15 with (Z.ones 4).
        rewrite Z.land_ones; word.
      }
      have Hsint :
        sint.Z (w64_word_instance.(word.and) x (W64 15)) =
        uint.Z (w64_word_instance.(word.and) x (W64 15)).
      { word. }
      rewrite Hsint.
      word.
    }

    set next_nibble := (w64_word_instance.(word.and)
                                            (w64_word_instance.(word.sru)
                                                                 (hash_key key)
                                                                 (w64_word_instance.(word.sub)
                                                                                      (W64 (sh path))
                                                                                      (W64 4)))
                                            (W64 15)).

    have Hnib_u : 0 ≤ uint.Z next_nibble < 16.
    {
      unfold next_nibble.
      rewrite word.unsigned_and_nowrap.
      change (uint.Z (W64 15)) with 15.
      split.
      - apply Z.land_nonneg.
        right.
        word.
      - change 15 with (Z.ones 4).
        rewrite Z.land_ones.
        + apply Z_mod_lt.
          word.
        + word.
    }

    have Hlt_nat : (sint.nat next_nibble < length children_vals)%nat by
                     (rewrite Hchildren_len; word).
    destruct (lookup_lt_is_Some_2 children_vals (sint.nat next_nibble) Hlt_nat)
      as [v Hv].

    wp_auto.

    have Hdom : h ∈ path_to_domain path by apply (in_domain _ (hash_key key)).

    wp_apply wp_Value__Load.
    iInv "His_map" as "[Hroot >Hmap]" "Hclose_ht".
    iInv "Hind_inv" as "HI" "Hclose_ind".

    unfold own_ht_map.
    iApply fupd_mask_intro.
    { apply empty_subseteq.
    (* set_solver. doesnt work, only when Hdom is defined? *) }
    iIntros "Hmask".
    iNext.

    iEval (unfold childrenP) in "HI".

    iNamed.
    iNamed "Hmap".

    (* iNamed "Hhtinv". *)
    (* iNamed "Hinv". *)

    iDestruct (big_sepL_lookup_acc with "Hchildren") as "[Hchild Hchildren_close]".
    { exact Hv. }
    iNamed "Hchild".
    iExists (interface.mk (ptrT.id hashtriemap.node.id) (# nodeptr)).
    replace (W64 (sint.nat next_nibble)) with next_nibble by word.
    iFrame "Hown_child".
    iIntros "Hown_child".

    unfold ht_load_ret.
    iEval (unfold childP) in "Hchild".

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

      have Hh : h = uint.Z (hash_key key) by reflexivity.
      iDestruct (user_map_lookup Hdom Hh with "Hmap Hchild") as %Hum.

      (* iDestruct (own_path_lookup _ _ _ h with "Hchild") as "[Hptsto Hptsto_close]"; [exact Hdom|]. *)
      (* (* iDestruct (big_sepL_elem_of_acc with "Hchild") as "[Hptsto Hptsto_close]". *) *)
      (* (* { exact Hdom. } *) *)
      (* iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup. *)
      (* iDestruct ("Hptsto_close" with "Hptsto") as "Hchild". *)

      iDestruct ("Hchildren_close" with "[Hown_child Hchild]") as "Hchildren".
      { iExists nodeptr. iFrame. unfold childP.
        destruct (decide (nodeptr = null)).
        - iFrame.
        - contradiction n0.
      }

      iMod ("Hclose_au" with "Hown") as "HΦ".
      iMod "Hclose_au_mask" as "_".
      iMod ("Hclose_ind" with "Hchildren") as "_".
      iMod ("Hclose_ht" with "[$Hroot $Hmap]") as "_".

      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "_".

      wp_apply wp_interface_type_assert.
      { auto. }

      wp_bind.
      replace (bool_decide (nodeptr = null)) with true.
      2: { symmetry. rewrite (bool_decide_eq_true (nodeptr = null)). exact e. }

      wp_auto.
      wp_bind.
      wp_alloc d_ptr as "d_ptr".
      wp_auto.
      wp_for_post.

      unfold empty_map_fn in Hum.
      rewrite lookup_empty in Hum.

      iEval (rewrite Hum; simpl) in "HΦ".

      wp_end.
    }

    iDestruct "Hchild" as (is_entry) "(#Hnodeis_entry & #Hchild)".
    destruct is_entry.
    {
      iDestruct "Hchild" as (ent) "(%Hent_notnull & #Hent & #Hind_null & #Hentry)".
      iMod "Hmask" as "_".

      iMod (fupd_mask_subseteq ht_au_mask) as "Hclose_au_mask".
      {
        unfold ht_au_mask.
        apply subseteq_difference_l.
        set_solver.
      }

      iDestruct ("Hchildren_close" with "[Hown_child]") as "Hchildren".
      {
        iExists nodeptr. iFrame. unfold childP.
        destruct (decide (nodeptr = null)).
        - contradiction n0.
        - iExists true. iFrame "#". done.
      }

      iMod "Hclose_au_mask" as "_".
      iMod ("Hclose_ind" with "[$Hchildren]") as "_".
      iMod ("Hclose_ht" with "[$Hroot $Hmap]") as "_".

      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "_".

      wp_apply wp_interface_type_assert.
      { auto. }
      replace (bool_decide (nodeptr = null)) with false.
      2: { symmetry. rewrite (bool_decide_eq_false (nodeptr = null)). exact n0. }

      wp_auto.

      wp_apply (wp_node__entry with "[# $]").
      wp_apply wp_entry__lookup.
      iFrame "#".
      rewrite /named.
      repeat iSplit; eauto.
      (* { *)
      (*   rewrite entry_unfold /entry_F. *)
      (*   iFrame "#". *)
      (* } *)
      iAuIntro.
      iApply aupd_aacc in "Hau".
      iRevert "Hau".
      iApply atomic_acc_wand.
      iSplit.
      - iIntros.
        iFrame.
      -
        unfold ht_load_ret.
        iIntros (m) "HΦ".
        (* unfold ht_load_ret. *)
        wp_auto.
        destruct (m !! key) eqn:Hlookup_key.
        all: rewrite Hlookup_key.
        all: wp_auto.
        all: wp_for_post.
        all: iFrame.
    }
    iDestruct "Hchild" as (ind) "(%Hnext_path_len & #Hent_null & #Hind & #Hindirect)".

    iDestruct ("Hchildren_close" with "[Hown_child]") as "Hchildren".
    { iExists nodeptr. iFrame. unfold childP.
      destruct (decide (nodeptr = null)).
      - contradiction n0.
      - iExists false. iFrame "#".
        iPureIntro. exact Hnext_path_len.
    }

    iMod "Hmask" as "_".
    iMod ("Hclose_ind" with "Hchildren") as "_".
    iMod ("Hclose_ht" with "[$]") as "_".

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".

    wp_apply wp_interface_type_assert.
    { auto. }

    replace (bool_decide (nodeptr = null)) with false.
    2: { symmetry. rewrite (bool_decide_eq_false (nodeptr = null)). exact n0. }

    wp_auto.
    wp_apply (wp_node__indirect with "[$]").
    wp_for_post.
    iFrame.
    iFrame "#".
    iPureIntro.

    set next := Z.of_nat (sint.nat next_nibble).
    set next_path := (path ++ [next]).

    have Hlen : length next_path = (length path + 1)%nat by
                                     rewrite app_length /=.

    have Hz : uint.Z next_nibble = Z.land (h ≫ (sh path - 4)) 15.
    {
      rewrite next_nibble_eq.
      - reflexivity.
      - auto.
    }

    split_and!; auto.
    - rewrite sh_snoc. unfold sh. word.
    - apply (next_nibble_extend path h next); try done.
      + unfold h.
        pose proof (word.unsigned_range (hash_key key)) as [H0 _].
        exact H0.
      + unfold next.
        rewrite Z2Nat.id; [|word].
        rewrite <- Z2Nat.id with (n:=sint.Z next_nibble) by word.
        word.
  Qed.

End proof.
