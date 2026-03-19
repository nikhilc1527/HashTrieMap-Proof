From iris.bi.lib Require Import fractional atomic.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From New.ghost Require Import ghost_var dghost_var.
From New.ghost Require Import mono_list.
From New.ghost Require Import token.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Export paths.

From Stdlib Require Import ZArith List.
(* From stdpp Require Import base. *)

Open Scope Z_scope.

Section model.
  (* namespace definitions *)
  Definition mapN         : namespace := nroot .@ "hashtriemap".
  Definition init_statusN : namespace := nroot .@ "init_status".
  Definition indN         : namespace := nroot .@ "indirect".
  Definition entryN       : namespace := nroot .@ "entry".
  Definition bucketN      : namespace := nroot .@ "bucket".

  Record hash_history_names := mkHashHistoryNames {
    hh_hist_name : gname;
    hh_lookup_name : gname;
  }.

  (* Ghost state for the hashtriemap. *)
  Record ghost_names := mkNames {
                            (* bool *)
                            init_name : gname;
                            (* auth_map w64 (gmap K V) *)
                            map_name : gname;
                            (* auth_map K V *)
                            user_name : gname;
                            (* auth_map Z gname *)
                            buckets_name : gname;
                            (* auth_map (Z * nat) (gmap loc nat) *)
                            idxs_name : gname;
                            histories_name : gname;
                          }.

  (* discount generics *)
  Definition K : Type := w64.
  Definition V : Type := w64.
  #[global] Instance K_inhab : Inhabited K := _.
  #[global] Opaque K V.

  Context `{hG: heapGS Σ, !ffi_semantics _ _}
    {sem: go.Semantics}.

  Context `{!globalsGS Σ, !ghost_varG Σ (gmap w64 w64)}
           `{!ghost_varG Σ bool}
    `{!mapG Σ K V}
    `{!mapG Σ Z (gmap K V)}
    `{!mapG Σ nat (gmap K V)}
    `{!mapG Σ Z gname}
    `{!mapG Σ (Z * nat) (gmap loc nat) }
    `{!mapG Σ Z hash_history_names}.

  Inductive lookup_status :=
  | LookupPending
  | LookupDoneFalse
  | LookupConsumed.

  (* Abstract map state seen by clients. *)
  Definition own_ht_map (γ: ghost_names) (m: gmap K V) : iProp Σ :=
    map_ctx γ.(user_name) (1/2) m.

  Definition ht_load_ret (m: gmap K V) (key: K) : val :=
    (match m !! key with
    | Some v => (#v, #true)
    | None => (#(zero_val V), #false)
    end)%V.

  Definition ht_au_mask : coPset :=
    ⊤ ∖ ↑mapN ∖ ↑indN ∖ ↑entryN.

  Definition lookup_pending_au (γ : ghost_names) (key : K) (Φ : val → iProp Σ) : iProp Σ :=
    AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
      @ ht_au_mask, ∅
      <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }>.

  Definition lookup_done_ret : val :=
    (#(zero_val V), #false)%V.

  Record lookup_info := mkLookupInfo {
                            lookup_key : K;
                            lookup_version : nat;
                            lookup_done_name : gname;
                            lookup_lstatus : lookup_status;
                            lookup_post : (val → iProp Σ);
                          }.

  Context `{!mapG Σ nat lookup_info}.

  Definition lookup_status_interp
    (γ : ghost_names) (linfo : lookup_info) : iProp Σ :=
    match linfo.(lookup_lstatus) with
    | LookupPending => lookup_pending_au γ linfo.(lookup_key) linfo.(lookup_post)
    | LookupDoneFalse => linfo.(lookup_post) lookup_done_ret
    | LookupConsumed => token linfo.(lookup_done_name)
    end.

  Definition map_current_version (hist : list (gmap K V)) : nat :=
    pred (length hist).

  Parameter hash_key : K → w64.

  Definition hash_map : Type := gmap Z (gmap K V).

  Definition empty_hash_map : hash_map :=
    gset_to_gmap ∅ (list_to_set full_domain).

  Inductive path_ownership :=
  | Empty
  | Singleton (h: Z) (m: gmap K V).

  Context `{!mapG Σ gname lookup_info}.

  Definition own_hash_history γ (γh : hash_history_names) q (map : gmap K V) : iProp Σ :=
    ∃ hist (lookups : gmap gname lookup_info),
      "Hown_hist" ∷ mono_list_auth_own γh.(hh_hist_name) q hist ∗
      "%Hhistory_cur" ∷ ⌜hist !! map_current_version hist = Some map⌝ ∗
      "Hown_lookups" ∷ map_ctx γh.(hh_lookup_name) q lookups ∗
      "Hlookups" ∷
        ([∗ map] γdone ↦ linfo ∈ lookups,
           (⌜linfo.(lookup_done_name) = γdone⌝ ∗
           ptsto_mut γh.(hh_lookup_name) linfo.(lookup_done_name) (q/2) linfo ∗
           lookup_status_interp γ linfo ∗
           ⌜linfo.(lookup_version) < length hist⌝ ∗
           ⌜linfo.(lookup_version) < length hist - 1 → linfo.(lookup_lstatus) ≠ LookupPending⌝)
        ).

  #[global] Instance own_hash_history_timeless (γ : ghost_names) (γhist : hash_history_names) q map : Timeless (own_hash_history γ γhist q map).
  Proof.
    rewrite /own_hash_history.
    apply _.
    unfold Timeless.
  Qed.

  #[global] Instance own_hash_history_fractional γhist map :
    Fractional (λ q, own_hash_history γhist q map).
  Proof.
    intros p q. rewrite /own_hash_history.
    iSplit.
    - iIntros "H1".
      iNamed "H1".
      iDestruct "Hown_hist" as "[H1 H2]".
      iDestruct "Hown_lookups" as "[H3 H4]".
      iSplitL "H1 H3"; iFrame; done.
    - iIntros "[H1 H2]".
      iNamedSuffix "H1" "1".
      iNamedSuffix "H2" "2".
      iDestruct (mono_list_auth_own_agree with "Hown_hist1 Hown_hist2") as %[_ ->].
      iDestruct (map_ctx_agree with "Hown_lookups1 Hown_lookups2") as %->.
      iCombine "Hown_hist1 Hown_hist2" as "H1".
      iCombine "Hown_lookups1 Hown_lookups2" as "H2".
      iFrame.
      done.
  Qed.

  #[global] Instance own_hash_history_as_fractional γhist q map :
    AsFractional (own_hash_history γhist q map) (λ q, own_hash_history γhist q map) q.
  Proof. split; [done|apply _]. Qed.

  #[global] Instance own_hash_history_combine_gives γhist q1 q2 m1 m2 :
    CombineSepGives (own_hash_history γhist q1 m1) (own_hash_history γhist q2 m2) (⌜(q1 + q2 ≤ 1)%Qp⌝ ∗ ⌜m1 = m2⌝).
  Proof.
    unfold CombineSepGives.
    iIntros "(H1 & H2)".
    unfold own_hash_history in *.
    iNamedSuffix "H1" "1".
    iNamedSuffix "H2" "2".
    iDestruct (mono_list_auth_own_agree with "Hown_hist1 Hown_hist2") as %[x ->].
    iDestruct (map_ctx_agree with "Hown_lookups1 Hown_lookups2") as %->.
    assert (m1 = m2) as -> by congruence.
    auto.
  Qed.

  Definition own_domain
    (γ : ghost_names) (q: Qp) (dom : domain) (ownership : path_ownership) : iProp Σ :=
    let γmap := γ.(map_name) in
    let γhists := γ.(histories_name) in
    match ownership with
    | Empty =>
        [∗ list] hash ∈ dom,
          ∃ γhist map,
            hash [[γmap]]↦{q} map ∗
            hash [[γhists]]↦ro γhist ∗
            own_hash_history γhist q map
    | Singleton h m =>
        [∗ list] hash ∈ dom,
          if decide (hash = h)
          then
            hash [[γmap]]↦{q} m
          else
            ∃ γhist map,
              hash [[γmap]]↦{q} map ∗
              hash [[γhists]]↦ro γhist ∗
              own_hash_history γhist q map
    end.

  Definition own_path
    (γ : ghost_names) (q: Qp) (p : path) (ownership : path_ownership) : iProp Σ :=
    own_domain γ q (path_to_domain p) ownership.

  #[global] Instance own_path_timeless γ dom q f : Timeless (own_path γ q dom f).
  Proof.
    unfold own_path, own_domain.
    apply _.
  Qed.

  #[global] Instance own_path_fractional γ dom f :
    Fractional (λ q, own_path γ q dom f).
  Proof.
    intros p q. rewrite /own_path /own_domain.
    destruct f.
    {
      iSplit.
      - iIntros "H1".
        iApply (fractional_big_sepL _ (
                    λ n hash y,
                      ∃ γhist (map : gmap K V),
                                               hash [[γ.(map_name)]]↦{
                                               y} map ∗
                                               hash [[γ.(histories_name)]]↦ro γhist ∗
                                               own_hash_history γhist (y) map
                  )%I); [|iFrame].
        iIntros (i h).
        iIntros (p0 q0).
        iSplit.
        + iIntros "(%a & %b & (H1 & #H2 & H3))".
          iDestruct "H1" as "[Hh1 Hh2]".
          iDestruct "H3" as "[Hh3 Hh4]".
          iFrame.
          iFrame "#".
        + iIntros "((%a & %b & H1 & #H2 & H3) & (%a2 & %b2 & H4 & #H5 & H6))".
          iDestruct (ptsto_agree with "H1 H4") as %->.
          iDestruct (ptsto_ro_agree with "H2 H5") as %->.
          iCombine "H1 H4" as "H1".
          iCombine "H3 H6" as "H".
          iFrame.
          iFrame "#".
      - iIntros "[H1 H2]".
        iApply (fractional_big_sepL _ (
                    λ n hash y,
                      ∃ γhist (map : gmap K V),
                        hash [[γ.(map_name)]]↦{
                            y} map ∗
                        hash [[γ.(histories_name)]]↦ro γhist ∗
                        own_hash_history γhist (y) map
                  )%I with "[H1 H2]"); [|iFrame].
        iIntros (i h).
        iIntros (p0 q0).
        iSplit.
        + iIntros "(%a & %b & (H1 & #H2 & H3))".
          iDestruct "H1" as "[Hh1 Hh2]".
          iDestruct "H3" as "[Hh3 Hh4]".
          iFrame.
          iFrame "#".
        + iIntros "((%a & %b & H1 & #H2 & H3) & (%a2 & %b2 & H4 & #H5 & H6))".
          iDestruct (ptsto_agree with "H1 H4") as %->.
          iDestruct (ptsto_ro_agree with "H2 H5") as %->.
          iCombine "H1 H4" as "H1".
          iCombine "H3 H6" as "H".
          iFrame.
          iFrame "#".
    }
    {
      iSplit.
      - iIntros "H1".
        iApply (fractional_big_sepL _ (
                    λ n hash y,
                      if decide (hash = h)
                      then hash [[γ.(map_name)]]↦{y} m
                      else
                        ∃ γhist (map : gmap K V),
                          hash [[
                                γ.(map_name)]]↦{
                              y} map ∗
                          hash [[
                                γ.(histories_name)]]↦ro γhist ∗
                          own_hash_history γhist (y) map
                  )%I); [|iFrame].
        intros i x.
        iIntros (p0 q0).
        iSplit.
        + iIntros "H1".
          destruct (decide (x = h)).
          * iDestruct "H1" as "[H1 H2]".
            iFrame.
          * iDestruct "H1" as "(%a & %b & (H1 & #H2 & H3))".
            iDestruct "H1" as "[Hh1 Hh2]".
            iDestruct "H3" as "[Hh3 Hh4]".
            iFrame.
            iFrame "#".
        + iIntros "H1".
          destruct (decide (x = h)).
          * iDestruct "H1" as "[H1 H2]".
            iCombine "H1 H2" as "H1".
            iFrame.
          * iDestruct "H1" as "((%a & %b & H1 & #H2 & H3) & (%a2 & %b2 & H4 & #H5 & H6))".
            iDestruct (ptsto_agree with "H1 H4") as %->.
            iDestruct (ptsto_ro_agree with "H2 H5") as %->.
            iCombine "H1 H4" as "H1".
            iCombine "H3 H6" as "H".
            iFrame.
            iFrame "#".
      - iIntros "[H1 H2]".
        iApply (fractional_big_sepL _ (
                    λ n hash y,
                      if decide (hash = h)
                      then hash [[γ.(map_name)]]↦{y} m
                      else
                        ∃ γhist (map : gmap K V),
                          hash [[γ.(map_name)]]↦{y} map ∗
                          hash [[γ.(histories_name)]]↦ro γhist ∗
                          own_hash_history γhist (y) map
                  )%I with "[H1 H2]"); [|iFrame].
        intros i x.
        iIntros (p0 q0).
        iSplit.
        + iIntros "H1".
          destruct (decide (x = h)).
          * iDestruct "H1" as "[H1 H2]".
            iFrame.
          * iDestruct "H1" as "(%a & %b & (H1 & #H2 & H3))".
            iDestruct "H1" as "[Hh1 Hh2]".
            iDestruct "H3" as "[Hh3 Hh4]".
            iFrame.
            iFrame "#".
        + iIntros "H1".
          destruct (decide (x = h)).
          * iDestruct "H1" as "[H1 H2]".
            iCombine "H1 H2" as "H1".
            iFrame.
          * iDestruct "H1" as "((%a & %b & H1 & #H2 & H3) & (%a2 & %b2 & H4 & #H5 & H6))".
            iDestruct (ptsto_agree with "H1 H4") as %->.
            iDestruct (ptsto_ro_agree with "H2 H5") as %->.
            iCombine "H1 H4" as "H1".
            iCombine "H3 H6" as "H".
            iFrame.
            iFrame "#".
    }
  Qed.

  #[global] Instance own_path_as_fractional γ path f q :
    AsFractional (own_path γ q path f) (λ q, own_path γ q path f) q.
  Proof. split; [done|apply _]. Qed.

  Lemma own_path_acc {γ q p h k} :
    h = uint.Z (hash_key k) →
    valid_path p →
    length p ≤ 16 →
    belongs_to_path p h →
    own_path γ q p Empty ⊣⊢
    ∃ γhist m,
      own_path γ q p (Singleton h m) ∗
      h [[γ.(histories_name)]]↦ro γhist ∗
      own_hash_history γhist q m.
  Proof.
    intros Hh Hvalid Hlen Hbelongs.
    rewrite /own_path /own_domain.
    rewrite (in_domain _ Hh) in Hbelongs.
    pose proof (path_to_domain_lookup p h Hvalid Hlen Hbelongs) as Hin.
    pose proof (path_to_domain_split_exact _ _ Hvalid Hlen Hbelongs) as Hsplit.
    iSplit.
    - iIntros "Hdom".
      iEval (rewrite (big_sepL_delete' _ _ _ _ Hin)) in "Hdom".
      iDestruct "Hdom" as "((%γhist & %map & Ha & Hb & Hc) & Hd)".
      iExists γhist, map.
      iSplitR "Hb Hc"; [|iFrame].
      rewrite Hsplit.
      iDestruct (big_sepL_app with "Hd") as "[Hb Hc]".
      iDestruct (big_sepL_app with "Hc") as "[Hc Hd]".
      rewrite length_seqZ.
      iApply (big_sepL_app).
      iSplitL "Hb".
      {
        iApply (big_sepL_mono with "Hb").
        iIntros (i j Hj) "Ha".
        assert (i ≠ Z.to_nat (h - lo p)) as Hneq.
        {
          intros Heq.
          rewrite Heq in Hj.
          pose proof (lookup_seqZ_ge (lo p) (h - lo p) (Z.to_nat (h - lo p))).
          assert (h - lo p <= Z.to_nat (h - lo p)) by lia.
          specialize (H H0).
          rewrite Hj in H.
          apply Some_ne_None in H.
          exact H.
        }
        iSpecialize ("Ha" $! Hneq).
        rewrite decide_False; [iFrame|].
        intros Hneq2.
        rewrite Hneq2 in Hj.
        rewrite lookup_seqZ in Hj.
        destruct Hj as [-> Hk].
        lia.
      }
      iApply (big_sepL_app).
      iSplitL "Ha Hc".
      {
        iApply big_sepL_singleton.
        rewrite decide_True; [|lia].
        iFrame.
      }
      {
        iApply (big_sepL_mono with "Hd").
        iIntros (i j Hj) "Ha".
        rewrite singleton_length.
        rewrite -in_domain in Hbelongs; [|exact Hh].
        rewrite shiftr_eq_iff_interval in Hbelongs; unfold sh; [|lia|subst h; word].
        assert (h - lo p >= 0) by lia.
        replace (Z.to_nat (h - lo p) + (1 + i))%nat with (Z.to_nat (h - lo p + 1 + i)) by lia.
        assert (Z.to_nat (h - lo p + 1 + i) ≠ Z.to_nat (h - lo p)) as Hneq by lia.
        iSpecialize ("Ha" $! Hneq).
        rewrite decide_False; [iFrame|].
        intros Hneq2.
        rewrite Hneq2 in Hj.
        rewrite lookup_seqZ in Hj.
        destruct Hj as [Hj Hk].
        lia.
      }
    - iIntros "Hdom".
      iDestruct "Hdom" as "(%γhist & %map & Ha & Hb & Hc)".
      rewrite Hsplit.
      iDestruct (big_sepL_app with "Ha") as "[Hd He]".
      iDestruct (big_sepL_app with "He") as "[He Hf]".
      iApply (big_sepL_app).
      iSplitL "Hd".
      {
        iApply (big_sepL_mono with "Hd").
        iIntros (i j Hj) "Ha".
        assert (i ≠ Z.to_nat (h - lo p)) as Hneq.
        {
          intros Heq.
          rewrite Heq in Hj.
          pose proof (lookup_seqZ_ge (lo p) (h - lo p) (Z.to_nat (h - lo p))).
          assert (h - lo p <= Z.to_nat (h - lo p)) by lia.
          specialize (H H0).
          rewrite Hj in H.
          apply Some_ne_None in H.
          exact H.
        }
        rewrite decide_False; [iFrame|].
        intros Hneq2.
        rewrite Hneq2 in Hj.
        rewrite lookup_seqZ in Hj.
        destruct Hj as [-> Hk].
        lia.
      }
      iApply (big_sepL_app).
      iSplitL "Hb Hc He".
      {
        iApply big_sepL_singleton.
        iFrame.
        iApply (big_sepL_singleton (
                    λ n y,
                      if decide (y = h)
                           then y [[γ.(map_name)]]↦{q} map
                           else
                            ∃ γhist0 (map0 : gmap K V),
                              y [[γ.(map_name)]]↦{q} map0 ∗
                              y [[γ.(histories_name)]]↦ro γhist0 ∗
                              own_hash_history γhist0 q map0
                  )%I) in "He".
        rewrite decide_True; [|lia].
        iFrame.
      }
      {
        iApply (big_sepL_mono with "Hf").
        iIntros (i j Hj) "Ha".
        rewrite -in_domain in Hbelongs; [|exact Hh].
        rewrite shiftr_eq_iff_interval in Hbelongs; unfold sh; [|lia|subst h; word].
        assert (h - lo p >= 0) by lia.
        replace (Z.to_nat (h - lo p) + (1 + i))%nat with (Z.to_nat (h - lo p + 1 + i)) by lia.
        assert (Z.to_nat (h - lo p + 1 + i) ≠ Z.to_nat (h - lo p)) as Hneq by lia.
        rewrite decide_False; [iFrame|].
        intros Hneq2.
        rewrite Hneq2 in Hj.
        rewrite lookup_seqZ in Hj.
        destruct Hj as [Hj Hk].
        lia.
      }
  Qed.

  #[global] Opaque own_domain.
  #[local] Transparent own_domain.

  #[global] Opaque own_path.
  #[local] Transparent own_path.

  Definition bucket_of_map (m : gmap K V) (h : Z) : gmap K V :=
    map_filter (λ x : K * V, uint.Z (hash_key x.1) = h) _ m.

  (* Definition bucket_snapshot (γ : ghost_names) (ver : nat) (h : Z) (bm : gmap K V) : iProp Σ := *)
  (*   ∃ mver, *)
  (*     mono_list_idx_own γ.(hist_name) ver mver ∗ *)
  (*     ⌜bm = bucket_of_map mver h⌝. *)

  Definition flatten (hm: hash_map) : gmap K V :=
    map_fold (λ (_: Z) (sub: gmap K V) (acc: gmap K V), sub ∪ acc) ∅ hm.

  Definition own_entry (γ: ghost_names) (q: Qp) (k: K) (v: V) : iProp Σ :=
    ptsto_mut γ.(user_name) k q v.

  Definition entry_next (ent next : loc) q := ent.[hashtriemap.entry.t, "overflow"] ↦ᵥ{q}
                           (interface.mk_ok (hashtriemap.entry) (#next)).

  (* entry cannot own the path, then it becomes duplicate ownership between the entries *)
  (* the indirect (node) holding the entry chain needs to own the path, and then the entries *)
  (* own keys that belong to that path *)
  Definition entry_inv
    (γ: ghost_names) (q: Qp)
    (entry: loc -d> Z -d> iProp Σ)
    (e: loc) (h: Z)
    : iProp Σ :=
    ∃ (next: loc) (k: K) (v: V) (γbucket : gname),
      "#Hk" :: e.[hashtriemap.entry.t, "key"]   ↦□ k ∗
      "#Hv" :: e.[hashtriemap.entry.t, "value"] ↦□ v ∗
      "Hown_next" :: entry_next e next (q/2) ∗
      "Hown_entry" ∷ own_entry γ q k v ∗
      "%Hhash" :: ⌜uint.Z (hash_key k) = h⌝ ∗
      "#Hnext_entry" :: (⌜next ≠ null⌝ -∗ ▷ entry next h) ∗
      "Hname" ∷ ptsto_ro γ.(buckets_name) h γbucket ∗
      "Hbucket_frag" ∷ auth_set_frag γbucket e.

  Definition entry_F
    (γ: ghost_names) (q: Qp)
    (entry: loc -d> Z -d> iProp Σ)
    : loc -d> Z -d> iProp Σ :=
    λ e h,
      ("#Hentry_inv" :: inv (entryN .@ e) (entry_inv γ q entry e h))%I.

  #[global] Instance entry_F_contractive γ q : Contractive (entry_F γ q).
  Proof.
    rewrite /entry_F /entry_inv.
    intros n f g Hfg e path.
    (* repeat (f_equiv; try solve_contractive). *)
    do 15 f_equiv.
    solve_contractive.
  Qed.

  Definition entry (γ: ghost_names) (q: Qp) (e: loc) (h: Z) : iProp Σ :=
    fixpoint (entry_F γ q) e h.

  Lemma entry_unfold γ q e path :
    entry γ q e path ⊣⊢ entry_F γ q (entry γ q) e path.
  Proof. apply (fixpoint_unfold (entry_F γ q)). Qed.

  #[global] Instance entry_persistent γ q e path : Persistent (entry γ q e path).
  Proof.
    rewrite entry_unfold /entry_F.
    apply _.
  Qed.

  Definition indirect_node
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp)
    (nodeptr: loc)
    (path child_path: path) : iProp Σ :=
    ∃ ind,
      "%Hchild_path_len" ∷ ⌜length child_path < 16⌝ ∗
      "%Hchild_not_null" ∷ ⌜ind ≠ null⌝ ∗
      "#Hchild_ind_ptr" ∷ nodeptr.[hashtriemap.node.t, "ind"] ↦□ ind ∗
      "#Hchild_ent_ptr" ∷ nodeptr.[hashtriemap.node.t, "ent"] ↦□ null ∗
      "#Hchild_ind" ∷ ▷ child_indirect ind child_path.

  Definition bucket (γ : ghost_names) (γbucket : gname) (q: Qp) (hash: Z) (sub : gmap K V) (ver : nat) (first_ent : loc) : iProp Σ :=
    ∃ (entries : gset loc) (idxs : gmap loc nat),
      "Hentries_auth" ∷ auth_set_auth γbucket entries ∗
      "#Hidxs" ∷ ptsto_ro γ.(idxs_name) (hash, ver) idxs ∗
      "%Hfirst" ∷ ⌜idxs !! first_ent = Some 0%nat⌝ ∗
      "%Hidxs_dom" ∷ ⌜dom idxs = entries⌝ ∗
      ([∗ set] ent ∈ entries,
         ∃ (next : loc) idx,
           "%Hidx" ∷ ⌜idxs !! ent = Some idx⌝ ∗
           "Hnext" ∷ entry_next ent next (q/2) ∗
           "%Hnext_idx" ∷ ⌜
             if (decide (next ≠ null))
             then (idxs !! next) = Some (S idx)
             else (S idx = size sub)⌝
      ).

  Definition entry_node
    (γ: ghost_names) (q: Qp)
    (nodeptr: loc)
    (path: path) : iProp Σ :=
    ∃ ent map hash γbucket ver,
      "Hown_path" ∷ own_path γ q path (Singleton hash map) ∗
      "%Hchild_not_null" ∷ ⌜ent ≠ null⌝ ∗
      "#Hchild_ent_ptr" ∷ nodeptr.[hashtriemap.node.t, "ent"] ↦□ ent ∗
      "#Hchild_ind_ptr" ∷ nodeptr.[hashtriemap.node.t, "ind"] ↦□ null ∗
      "#Hchild_entry" ∷ entry γ q ent hash ∗
      "%Hbelongs" ∷ ⌜belongs_to_path path hash⌝ ∗
      "#Hnames" ∷ ptsto_ro γ.(buckets_name) hash γbucket ∗
      "Hbucket" ∷ bucket γ γbucket q hash map ver ent.

  (* definition of node *)
  Definition childP
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp)
    (nodeptr: loc)
    (path child_path: path) : iProp Σ :=
    if (decide (nodeptr = null)) then
      "Hchild" ∷ own_path γ q child_path Empty
    else
      (∃ (is_entry: bool),
          "#Hnode_is_entry" ∷ nodeptr.[hashtriemap.node.t, "isEntry"] ↦□ is_entry ∗
          "Hchild" ∷
            (if is_entry then
               entry_node γ q nodeptr child_path
             else
               indirect_node child_indirect γ q nodeptr path child_path))%I.

  Definition childrenP
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp) (children_slice: slice.t)
    (children_vals: list atomic.Value.t)
    (ind: loc) (path: path) : iProp Σ :=
    "Hchildren" :: [∗ list] i ↦ val ∈ children_vals,
      ∃ (nodeptr: loc),
        "Hown_child" :: (slice.slice_index_ref atomic.Value.t i children_slice) ↦ᵥ{q}
          (interface.ok (interface.mk (go.PointerType hashtriemap.node) #nodeptr)) ∗
        "Hchild" :: childP child_indirect γ q nodeptr path (path ++ [Z.of_nat i]).

  (* split 50/50 between an invariant and the mutex to allow for lock-free reads *)
  (* we always have read permission on any indirect, but only can write if we acquire the lock *)
  (* the only things ever modified are atomic values (atomic pointers), everything else is □ ownership *)
  Definition indirect_F
    (γ: ghost_names)
    (indirect: loc -d> (list Z) -d> iProp Σ)
    : loc -d> (list Z) -d> iProp Σ :=
    λ ind path,
      (∃ (children_vals: list atomic.Value.t) (children_slice: slice.t),
          "#Hown_children" :: ind.[hashtriemap.indirect.t, "children"] ↦□ children_slice ∗
          "#Hchildren_slice" :: children_slice ↦*□ children_vals ∗
          "%Hchildren_len" :: ⌜length children_vals = 16%nat⌝ ∗
          "#Hind_inv" :: inv (indN) ((childrenP indirect γ (1/2) children_slice children_vals ind path)) ∗
          "#Hind_mutex" :: is_Mutex ind.[hashtriemap.indirect.t, "mu"] (
              (* dont need to split dead between inv and mutex because its only used for modification of the tree *)
              ∃ (dead: bool),
                "Hdead" ∷ own_Bool ind.[hashtriemap.indirect.t, "dead"] (DfracOwn 1) dead ∗
                "Hmu_inv" ∷ ((* ⌜dead = false⌝ -∗ *) childrenP indirect γ (1/2) children_slice children_vals ind path)))%I.

  (* Prove contractiveness *)
  #[global] Instance indirect_F_contractive γ : Contractive (indirect_F γ).
  Proof.
    rewrite /indirect_F.
    intros n f g Hfg ind path.
    unfold childrenP, childP.
    do 24 f_equiv.
    2: do 4 f_equiv.
    all: solve_contractive.
  Qed.

  Definition indirect (γ: ghost_names) (ind: loc) (path: path) : iProp Σ :=
    fixpoint (indirect_F γ) ind path.

  Lemma indirect_unfold γ ind path :
    indirect γ ind path ⊣⊢
    indirect_F γ (indirect γ) ind path.
  Proof. apply (fixpoint_unfold (indirect_F γ)). Qed.

  #[global] Instance indirect_persistent γ ind path : Persistent (indirect γ ind path).
  Proof.
    rewrite indirect_unfold /indirect_F.
    apply _.
  Qed.

  #[global] Instance indirect_node_persistent γ q nodeptr path child_path : Persistent (indirect_node (indirect γ) γ q nodeptr path child_path).
  Proof. apply _. Qed.

  Definition lookup_token
    (γ : ghost_names) (id ver : nat) (key : K)
    (Φ : val → iProp Σ) : iProp Σ :=
    ∃ h γhist γdone (mver : gmap K V),
      "%Hhash" ∷ ⌜h = uint.Z (hash_key key)⌝ ∗
      "Hhist_name" ∷ ptsto_ro γ.(histories_name) h γhist ∗
      "#Hver" ∷ mono_list_idx_own γhist.(hh_hist_name) ver mver ∗
      "Hpending" ∷ lookup_pending_au γ key Φ ∗
      "Hdone_token" ∷ token γdone.

  Definition buckets_map (γ: ghost_names) : iProp Σ :=
    (* ∃ buckets, *)
    (*   map_ctx γ.(buckets_name) 1 buckets ∗ *)
      ([∗ list] h ∈ (seqZ 0 (2^64)),
         ∃ (γbucket : gname),
           ptsto_ro γ.(buckets_name) h γbucket).

  (* abstract the state of the entire map, can be fully abstracted away from hashtriemap.v *)
  Definition map_state (γ: ghost_names) (user_map: gmap K V) (hm: hash_map) : iProp Σ :=
    (* idxs: (hash, ver) -> idxs *)
    ∃ (idxs : gmap (Z * nat) (gmap loc nat)),
    "Hauth_map" :: map_ctx γ.(map_name) 1 hm ∗
    "Huser_map" :: own_ht_map γ user_map ∗
    "%Hflat" :: ⌜user_map = flatten hm⌝ ∗
    "Hidxs_auth" ∷ map_ctx γ.(idxs_name) 1 idxs ∗
    (* bucket correctness - if a key exists, then its in the correct bucket *)
    "%Hbuckets" ::     (⌜∀ h sub k,
                         hm !! h = Some sub →
                         uint.Z (hash_key k) = h →
                         flatten hm !! k = sub !! k⌝) ∗
    "%Hbuckets_rev" ∷ (⌜∀ h sub k v,
                         hm !! h = Some sub →
                         sub !! k = Some v →
                         uint.Z (hash_key k) = h⌝).

  (* this is usually only really needed once per function, so it's convenient if its bundled away *)
  Definition own_root
    (γ: ghost_names) (ht: loc) (rooti: loc) : iProp Σ :=
    "Hown_root" ∷ ht.[hashtriemap.HashTrieMap.t, "root"] ↦ᵥ
                       (interface.ok (interface.mk (go.PointerType hashtriemap.indirect) #rooti)) ∗
    "#Hroot_indirect" ∷ indirect γ rooti [].

  Definition ht_inv
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    inv mapN (
        ∃ root user_map hm,
          own_root γ ht root ∗
          map_state γ user_map hm
      ).

  (* Public predicate exposed to clients. *)
  Definition is_hashtriemap
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    ("#Hseed" :: ∃ (seed: w64), ht.[hashtriemap.HashTrieMap.t, "seed"] ↦□ seed) ∗
    "#His_map" :: ht_inv γ ht.

  (* designed to be split between an invariant and a mutex, so that reading can be done outside of the critical section and writing can only be done inside *)
  Definition init_tok `{!ghost_varG Σ bool} (γ: ghost_names) (b: bool) : iProp Σ :=
    ghost_var γ.(init_name) (1/2)%Qp b.

  Definition init_status_done
    (γ: ghost_names) (ht: loc) (b: bool) : iProp Σ :=
    (if b then is_hashtriemap γ ht else True%I).

  Definition init_status_inv
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      own_Uint32 ht.[hashtriemap.HashTrieMap.t, "inited"] 1
        (if b then W32 1 else W32 0) ∗
      init_tok γ b ∗
      □ init_status_done γ ht b.

  Definition init_status
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    inv init_statusN (init_status_inv ht γ).

  (* Initialization lock invariant for HashTrieMap. *)
  Definition init_mu_inv `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      if b
      then init_tok γ true
      else (init_tok γ false ∗
            (∃ (seed: w64),
                ht.[hashtriemap.HashTrieMap.t, "seed"] ↦ seed) ∗
            ht.[hashtriemap.HashTrieMap.t, "root"] ↦ᵥ interface.nil
           )%I.

  Definition init_mu `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    is_Mutex ((ht.[hashtriemap.HashTrieMap.t, "initMu"]))
      (init_mu_inv ht γ).

  Definition hashtriemap_init
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    "#Hinit" :: init_status ht γ ∗
    "#Hinit_mu" :: init_mu ht γ.

  Lemma hashtriemap_pre_auth_init
    `{!mapG Σ nat lookup_info, !mapG Σ Z gname,
      !mapG Σ (Z * nat) (gmap loc nat), !mapG Σ Z hash_history_names} :
    ⊢ |==> ∃ γ,
      init_tok γ false ∗ init_tok γ false.
  Proof.
    iMod (ghost_var_alloc (false)) as (init_γ) "[Hinit1 Hinit2]".
    iMod (ghost_var_alloc (∅ : gmap K V)) as (map_γ) "Hmap".
    iMod (ghost_var_alloc (∅ : gmap K V)) as (user_γ) "[Huser1 Huser2]".
    iMod (map_init (∅ : gmap Z gname)) as (buckets_γ) "Hbuckets".
    iMod (map_init (∅ : gmap (Z * nat) (gmap loc nat))) as (idxs_γ) "Hidxs".
    iMod (map_init (∅ : gmap Z hash_history_names)) as (histories_γ) "Hhistories".

    iMod (token_alloc) as (γ) "_".

    iModIntro.
    iExists (mkNames init_γ map_γ user_γ
               buckets_γ idxs_γ histories_γ).
    iFrame.
  Qed.

  Lemma hashtriemap_zero_init
    `{!mapG Σ nat lookup_info, !mapG Σ Z gname,
      !mapG Σ (Z * nat) (gmap loc nat), !mapG Σ Z hash_history_names}
    {sync_sem : sync.Assumptions} {E}
    (ht: loc) :
    ht ↦ zero_val hashtriemap.HashTrieMap.t ={E}=∗
    ∃ γ, hashtriemap_init ht γ.
  Proof.
    iIntros "Hht".
    iDestruct (typed_pointsto_split with "Hht") as "Hfields".
    iNamed "Hfields".
    simpl.
    iMod (hashtriemap_pre_auth_init) as (γ) "(Htok1 & Htok2)".

    iMod (inv_alloc init_statusN _ (init_status_inv ht γ) with "[Htok1 inited]") as "#Hinit".
    {
      iNext.
      iExists false.
      iFrame.
      done.
    }
    set (m := ht.[hashtriemap.HashTrieMap.t, "initMu"]).

    iMod (init_Mutex (init_mu_inv ht γ) E m with "initMu [Htok2 seed root]") as "Hmutex".
    {
      iNext.
      iExists false.
      iFrame.
    }

    iModIntro.
    iExists γ.
    iFrame.
    iFrame "#".
  Qed.

  Lemma own_path_lookup h path γ q m :
    h ∈ path_to_domain path →
    own_path γ q path (Singleton h m) -∗
    ptsto_mut γ.(map_name) h q m ∗
      (ptsto_mut γ.(map_name) h q m -∗ own_path γ q path (Singleton h m)).
  Proof.
    iIntros (Hdom) "Hpath".
    Local Transparent own_path.
    Local Transparent own_domain.
    unfold own_path, own_domain.
    iDestruct (big_sepL_elem_of_acc with "Hpath") as "[Hptsto Hclose]"; [exact Hdom|].
    iSplitL "Hptsto".
    - rewrite decide_True; [done|done].
    - iIntros "Hptsto".
      iApply "Hclose".
      rewrite decide_True; [done|done].
  Qed.

  Lemma buckets_disjoint
    (hm : gmap Z (gmap K V))
    (Hbuckets_rev : ∀ h sub k v,
       hm !! h = Some sub →
       sub !! k = Some v →
       uint.Z (hash_key k) = h) :
    ∀ h1 h2 sub1 sub2,
    hm !! h1 = Some sub1 →
    hm !! h2 = Some sub2 →
    h1 ≠ h2 →
    sub1 ##ₘ sub2.
  Proof.
    intros h1 h2 sub1 sub2 H1 H2 Hneq.
    apply map_disjoint_spec; intros k v1 v2 Hk1 Hk2.
    have Hh1 : uint.Z (hash_key k) = h1 :=
      Hbuckets_rev _ _ _ _ H1 Hk1.
    have Hh2 : uint.Z (hash_key k) = h2 :=
      Hbuckets_rev _ _ _ _ H2 Hk2.
    congruence.
  Qed.

  Lemma flatten_update_update
    hm h k v old :
    hm !! h = Some old →
    uint.Z (hash_key k) = h →
    (∀ h0 sub k v, hm !! h0 = Some sub → sub !! k = Some v → uint.Z (hash_key k) = h0) →
    flatten (<[h:=<[k:=v]> old]> hm) = <[k:=v]> (flatten hm).
  Proof.
    intros Hh Hhash Hbuckets_rev.

    have Hhm_eq : hm = <[h:=old]> (delete h hm).
    {
      apply map_eq; intro h0.
      destruct (decide (h0 = h)) as [->|Hneq].
      - rewrite lookup_insert lookup_delete_eq Hh. rewrite decide_True; reflexivity.
      - rewrite lookup_insert_ne; [|done].
        rewrite lookup_delete_ne; [|done].
        reflexivity.
    }

    rewrite Hhm_eq.
    rewrite insert_insert.

    unfold flatten.
    rewrite map_fold_insert_L; [| |rewrite lookup_delete_eq; reflexivity].
    2: {
      intros.
      rewrite map_union_assoc.
      symmetry.
      rewrite map_union_assoc.
      replace (z2 ∪ z1) with (z1 ∪ z2); [reflexivity|].
      apply map_union_comm.

      have H0' : hm !! j1 = Some z1 by rewrite -Hhm_eq in H0; exact H0.
      have H1' : hm !! j2 = Some z2 by rewrite -Hhm_eq in H1; exact H1.
      eapply buckets_disjoint; eauto.
    }

    rewrite decide_True; [|reflexivity].

    rewrite map_fold_insert_L; [| |rewrite lookup_delete_eq; reflexivity].
    2: {
      intros.
      rewrite map_union_assoc.
      symmetry.
      rewrite map_union_assoc.
      replace (z2 ∪ z1) with (z1 ∪ z2); [reflexivity|].
      apply map_union_comm.

      set (hm'' := <[h:=<[k:=v]> old]> (delete h hm)).
      have Hbuckets_rev' :
        ∀ h0 sub k0 v0,
        hm'' !! h0 = Some sub →
        sub !! k0 = Some v0 →
        uint.Z (hash_key k0) = h0.
      {
        intros h0 sub k0 v0 Hlook Hsub.
        destruct (decide (h0 = h)) as [->|Hneq].
        - rewrite lookup_insert in Hlook.
          rewrite decide_True in Hlook; [|reflexivity].
          inversion Hlook; subst sub.
          destruct (decide (k0 = k)) as [->|Hk].
          + exact Hhash.
          + have Hold : old !! k0 = Some v0 by rewrite lookup_insert_ne in Hsub; [exact Hsub|symmetry; exact Hk].
            have Hh_old : uint.Z (hash_key k0) = h :=
              Hbuckets_rev _ _ _ _ Hh Hold.
            exact Hh_old.
        - rewrite lookup_insert_ne in Hlook; [|symmetry; exact Hneq].
          eapply Hbuckets_rev; eauto.
          apply lookup_delete_Some in Hlook as [_ Hhm].
          exact Hhm.
      }

      have H0' : hm'' !! j1 = Some z1 := H0.
      have H1' : hm'' !! j2 = Some z2 := H1.
      eapply buckets_disjoint; eauto.
    }

    apply map_eq; intro k'.
    destruct (decide (k' = k)) as [->|Hk].
    - rewrite lookup_insert.
      rewrite lookup_union.
      rewrite lookup_insert.
      rewrite decide_True; [|reflexivity].
      rewrite decide_True; [|reflexivity].
      apply union_Some_l.
    - rewrite lookup_insert_ne; [|done].
      rewrite lookup_union.
      rewrite lookup_insert_ne; [|done].
      change (map_fold (λ (_ : Z) (sub acc : gmap K V), sub ∪ acc) ∅ (delete h hm)) with (flatten (delete h hm)).
      rewrite lookup_union.
      reflexivity.
  Qed.

  Lemma own_path_update_key key value γ hm path h old :
    h = uint.Z (hash_key key) →
    let hm' := <[h := <[key:=value]> old]> hm in
    belongs_to_path path h →
    "Hctx" ∷ map_ctx γ.(map_name) 1 hm -∗
    "Hpath" ∷ own_path γ 1 path (Singleton h old) ==∗
    "Hctx" ∷ map_ctx γ.(map_name) 1 hm' ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h (<[key:=value]> old)).
  Proof.
    intros Hhash hm' Hbelongs.
    iIntros "Hctx Hpath".
    subst hm'.
    have Hbelongs' : belongs_to_path path (uint.Z (hash_key key)).
    { rewrite <- Hhash. exact Hbelongs. }
    have Hdom0 : uint.Z (hash_key key) ∈ path_to_domain path.
    { apply (path_to_domain_elem _ _); [apply full_domain_elem|exact Hbelongs']. }
    have Hdom : h ∈ path_to_domain path.
    { rewrite Hhash. exact Hdom0. }
    unfold own_path, own_domain.
    set (dom := path_to_domain path) in *.
    have Hnodup : base.NoDup dom by apply dom_no_dup.
    iInduction dom as [|h' dom] "IH".
    { rewrite elem_of_nil in Hdom. done. }
    apply NoDup_ListNoDup in Hnodup.
    apply NoDup_cons_iff in Hnodup as [Hnotin Hnodup].
    simpl.
    iDestruct "Hpath" as "[Hh' Hpath]".
    rewrite elem_of_cons in Hdom.
    destruct Hdom as [-> | Hdom].
    - iClear "IH".
      rewrite decide_True; [|done].
      iMod (map_update h' old (<[key:=value]> old) with "Hctx Hh'") as "[Hctx Hh']".
      iModIntro.
      rewrite decide_True; [|done].
      iFrame "Hctx Hh'".
      iApply (big_sepL_mono with "Hpath").
      iIntros (i y Hy) "Hy".
      destruct (decide (y = h')) as [Heq|Hneq].
      {
        subst y.
        exfalso.
        apply Hnotin.
        apply list_elem_of_lookup_2 in Hy.
        rewrite list_elem_of_In in Hy.
        exact Hy.
      }
      iFrame.
    - rewrite decide_False.
      2: {
        intro Heq.
        subst h'.
        rewrite list_elem_of_In in Hdom.
        exact (Hnotin Hdom).
      }
      subst h.
      apply NoDup_ListNoDup in Hnodup.
      iSpecialize ("IH" $! Hdom Hdom Hnodup with "Hctx Hpath").
      iMod "IH" as "(Hctx & Hpath)".
      iModIntro.
      iFrame.
      rewrite decide_False; [iFrame|].
      intros ->.
      rewrite -list_elem_of_In in Hnotin.
      apply Hnotin.
      exact Hdom.
  Qed.

  Lemma hm_lookup {h path γ m hm q sub} :
    h ∈ path_to_domain path →
    map_state γ m hm -∗
    own_path γ q path (Singleton h sub) -∗
    ⌜hm !! h = Some sub⌝.
  Proof.
    iIntros (Hdom) "Hmap_state Hown_path".
    iNamed "Hmap_state".
    iDestruct (own_path_lookup h _ _ _ _ Hdom with "Hown_path") as "[Hptsto _]".
    iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
    done.
  Qed.

  Lemma entry_lookup {γ q k v m hm} :
    map_state γ m hm -∗
    own_entry γ q k v -∗
    ⌜m !! k = Some v⌝.
  Proof.
    iIntros "Hmap_state Hentry".
    iNamed "Hmap_state".
    unfold own_entry, own_ht_map.
    iDestruct (map_valid with "Huser_map Hentry") as %Hlookup.
    done.
  Qed.

  Lemma user_map_lookup {h path γ m hm q k sub} :
    h ∈ path_to_domain path →
    h = uint.Z (hash_key k) →
    map_state γ m hm -∗
    own_path γ q path (Singleton h sub) -∗
    ⌜m !! k = sub !! k⌝.
  Proof.
    iIntros (Hdom Hh) "Hmap_state Hown_path".
    iDestruct (hm_lookup Hdom with "Hmap_state Hown_path") as %Hhm.
    iNamed "Hmap_state".
    rewrite Hflat.
    iPureIntro.
    apply (Hbuckets h sub k); auto.
  Qed.

  Lemma map_state_agree {γ m m2 hm} :
    map_state γ m hm -∗ own_ht_map γ m2 -∗ ⌜m = m2⌝.
  Proof.
    iIntros "Hmap_state Huser_map2".
    iNamed "Hmap_state".
    iDestruct (map_ctx_agree with "Huser_map Huser_map2") as %Hx.
    done.
  Qed.

  Lemma map_state_bucket_of_path {h path γ m hm q sub} :
    h ∈ path_to_domain path →
    map_state γ m hm -∗
    own_path γ q path (Singleton h sub) -∗
    ⌜sub = bucket_of_map m h⌝.
  Proof.
    iIntros (Hdom) "Hmap_state Hown_path".
    iDestruct (hm_lookup Hdom with "Hmap_state Hown_path") as %Hhm.
    iNamed "Hmap_state".
    iPureIntro.
    have Hhm_sub : hm !! h = Some sub.
    { exact Hhm. }
    apply map_eq; intro k.
    destruct (decide (uint.Z (hash_key k) = h)) as [Hhash|Hhash].
    - destruct (m !! k) as [v|] eqn:Hmk.
      + have Hsub : sub !! k = Some v.
        {
          rewrite <- (Hbuckets h sub k Hhm_sub Hhash).
          rewrite <- Hflat.
          exact Hmk.
        }
        rewrite Hsub.
        symmetry.
        apply map_lookup_filter_Some.
        split; [exact Hmk|exact Hhash].
      + have Hsub : sub !! k = None.
        {
          rewrite <- (Hbuckets h sub k Hhm_sub Hhash).
          rewrite <- Hflat.
          exact Hmk.
        }
        rewrite Hsub.
        symmetry.
        apply map_lookup_filter_None.
        left.
        exact Hmk.
    - rewrite /bucket_of_map.
      destruct (sub !! k) as [v|] eqn:Hsub; last first.
      { symmetry.
        apply map_lookup_filter_None.
        right.
        intros x Hmx Hpred.
        apply Hhash.
        exact Hpred.
      }
      exfalso.
      apply Hhash.
      eapply Hbuckets_rev; eauto using Hhm_sub.
  Qed.

  Lemma own_hash_history_snapshot (γhist : hash_history_names) m :
    own_hash_history γhist 1 m -∗
    ∃ hist,
      own_hash_history γhist 1 m ∗
      mono_list_lb_own γhist.(hh_hist_name) hist ∗
      ⌜hist !! map_current_version hist = Some m⌝.
  Proof.
    iIntros "Hhistory".
    iNamed "Hhistory".
    iDestruct (mono_list_lb_own_get with "Hown_hist") as "#Hhist_lb".
    iExists hist.
    iSplitL "Hown_hist Hown_lookups".
    - rewrite /own_hash_history.
      iExists hist, lookups.
      iFrame.
      done.
    - iFrame "Hhist_lb".
      done.
  Qed.

  Lemma own_hash_history_current_eq_from_snapshot
    (γhist : hash_history_names) hist ver mcur mver :
    mono_list_lb_own γhist.(hh_hist_name) hist -∗
    mono_list_idx_own γhist.(hh_hist_name) ver mver -∗
    ⌜hist !! map_current_version hist = Some mcur⌝ -∗
    ⌜map_current_version hist = ver⌝ -∗
    ⌜mcur = mver⌝.
  Proof.
    iIntros "#Hhist_lb #Hidx %Hcur %Hver_eq".
    have Hlt : (ver < length hist)%nat.
    {
      rewrite -Hver_eq /map_current_version.
      destruct hist as [|x hist']; first done.
      simpl. lia.
    }
    iDestruct (mono_list_lb_idx_lookup with "Hhist_lb Hidx") as %Hlookup; first exact Hlt.
    iPureIntro.
    rewrite Hver_eq in Hcur.
    congruence.
  Qed.

  Lemma map_state_insert
    {γ path hm user_map user_map2 h old} key value
    (Hhash : h = uint.Z (hash_key key))
    (Hnone : user_map !! key = None)
    (Hbelongs : belongs_to_path path h) :
    let um' := <[key:=value]> user_map in
    let hm' := <[h := <[key:=value]> old]> hm in
    "Hmap" ∷ map_state γ user_map hm ∗
    "Huser_map2" ∷ own_ht_map γ user_map2 ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h old) ==∗
    "Hmap" ∷ map_state γ um' hm' ∗
    "Huser_map2" ∷ own_ht_map γ um' ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h (<[key:=value]> old)) ∗
    "Hentry" ∷ own_entry γ 1 key value.
  Proof.
    intros um' hm'.
    iIntros "x".
    iNamed "x".
    iNamed "Hmap".
    unfold own_ht_map.
    have Hdom : h ∈ path_to_domain path by rewrite -in_domain.
    iDestruct (own_path_lookup h _ _ _ _ Hdom with "Hpath") as "[Hptsto Hptsto_close]".
    iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
    iDestruct ("Hptsto_close" with "Hptsto") as "Hpath".
    iDestruct (map_ctx_agree with "Huser_map Huser_map2") as %Hagree.
    subst user_map2.
    iCombine "Huser_map Huser_map2" as "Huser_map".
    iMod (map_alloc key value Hnone with "Huser_map") as "[Huser_map Hentry]".
    iDestruct "Huser_map" as "[Huser_map Huser_map2]".
    subst h.
    iMod (own_path_update_key key value with "Hauth_map Hpath") as "x"; [lia|exact Hbelongs|]; iNamed "x".
    set (h := uint.Z (hash_key key)) in *.
    iNamed.
    assert (Hum' : (um' = flatten hm')).
    {
      subst um' hm'.
      symmetry.
      subst user_map.
      apply (flatten_update_update hm h key value old).
      - exact Hlookup.
      - reflexivity.
      - intros.
        eapply Hbuckets_rev.
        + exact H.
        + exact H0.
    }
    iModIntro.
    unfold map_state.
    iFrame "Huser_map2 Hentry".
    iFrame "Hctx Huser_map".
    iSplitR "Hpath"; [|iFrame].
    iFrame "Hidxs_auth".
    iSplit; first done.
    iPureIntro.
    split.
    - intros h0 sub k Hhm' Hhash0.
      rewrite -Hum'.
      subst um' hm'.
      destruct (decide (h0 = h)) as [->|Hneq].
      + rewrite lookup_insert in Hhm'.
        rewrite decide_True in Hhm'; [|reflexivity].
        inversion Hhm'; subst sub; clear Hhm'.
        destruct (decide (k = key)) as [->|Hk].
        * rewrite lookup_insert. rewrite lookup_insert.
          rewrite decide_True; [|reflexivity].
          rewrite decide_True; [|reflexivity].
          done.
        * rewrite lookup_insert_ne; [|done].
          have Hnone_k : user_map !! k = old !! k.
          {
            rewrite Hflat.
            apply (Hbuckets h); auto.
          }
          rewrite Hnone_k.
          rewrite lookup_insert_ne; [|done].
          done.
      + rewrite lookup_insert_ne in Hhm'; [|done].
        subst h h0.
        rewrite lookup_insert_ne; [|congruence].
        rewrite Hflat.
        eapply Hbuckets; eauto.
    - subst hm'. simpl in *.
      intros.
      destruct (decide (h0 = h)) as [->|Hneq].
      + rewrite lookup_insert in H.
        rewrite decide_True in H; [|done].
        assert (sub = (<[key:=value]> old)) by (inversion H; reflexivity); subst sub.
        destruct (decide (k = key)) as [->|Hk].
        * done.
        * rewrite lookup_insert_ne in H0; [|done].
          apply (Hbuckets_rev h old k v); auto.
      + rewrite lookup_insert_ne in H; [|done].
        eapply Hbuckets_rev; eauto.
  Qed.

  Lemma map_state_version_insert
    {γ path hm user_map user_map2 h old γhist} key value
    (Hhash : h = uint.Z (hash_key key))
    (Hnone : user_map !! key = None)
    (Hbelongs : belongs_to_path path h) :
    let new := <[key:=value]> old in
    let um' := <[key:=value]> user_map in
    let hm' := <[h := new]> hm in
    "Hmap" ∷ map_state γ user_map hm ∗
    "Huser_map2" ∷ own_ht_map γ user_map2 ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h old) ∗
    "#Hhist_name" ∷ ptsto_ro γ.(histories_name) h γhist ∗
    "Hhist" ∷ own_hash_history γhist 1 old ∗
    "Hfinish_old" ∷ (own_hash_history γhist 1 old ==∗ own_hash_history γhist 1 new)
    ==∗
    "Hmap" ∷ map_state γ um' hm' ∗
    "Huser_map2" ∷ own_ht_map γ um' ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h (<[key:=value]> old)) ∗
    "#Hhist_name" ∷ ptsto_ro γ.(histories_name) h γhist ∗
    "Hhist" ∷ own_hash_history γhist 1 (<[key:=value]> old) ∗
    "Hentry" ∷ own_entry γ 1 key value.
  Proof.
    intros new um' hm'.
    iIntros "(Hmap & Huser_map2 & Hpath & #Hhist_name & Hhist & Hfinish_old)".
    iMod (map_state_insert key value Hhash Hnone Hbelongs with "[$Hmap $Huser_map2 $Hpath]")
      as "(Hmap & Huser_map2 & Hpath & Hentry)".
    iMod ("Hfinish_old" with "Hhist") as "Hhist".
    iModIntro.
    iNamed.
    iFrameNamed.
  Qed.

  Lemma map_state_register_lookup {γ m hm E h γhist sub}
    (key : K) (Φ : val → iProp Σ) :
    h = uint.Z (hash_key key) →
    map_state γ m hm -∗
    ptsto_ro γ.(histories_name) h γhist -∗
    own_hash_history γhist 1 sub -∗
    lookup_pending_au γ key Φ ={E}=∗
    ∃ id ver,
      map_state γ m hm ∗
      ptsto_ro γ.(histories_name) h γhist ∗
      own_hash_history γhist 1 sub ∗
      lookup_token γ id ver key Φ.
  Proof.
    iIntros (?) "Hmap #Hhist_name Hhist Hau".
    iNamed "Hhist".
    set (ver := map_current_version hist).
    have Hver_lookup : hist !! ver = Some sub by exact Hhistory_cur.
    have Hver_lt : (ver < length hist)%nat.
    {
      rewrite /ver /map_current_version.
      destruct hist as [|x hist']; first done.
      simpl; lia.
    }
    iDestruct (mono_list_lb_own_get with "Hown_hist") as "#Hhist_lb".
    iDestruct (mono_list_idx_own_get with "Hhist_lb") as "#Hver"; first exact Hver_lookup.
    iMod (token_alloc) as (γdone) "Hdone".
    set (id := fresh (dom lookups)).
    have Hid_fresh : lookups !! id = None.
    {
      apply not_elem_of_dom.
      apply is_fresh.
    }
    iMod (map_alloc id (mkLookupInfo key ver γdone LookupPending) Hid_fresh with "Hown_lookups")
      as "[Hown_lookups _]".
    iModIntro.
    iExists id, ver.
    iFrame "Hmap".
    iFrame "#".
    iSplitL "Hown_hist Hown_lookups".
    {
      rewrite /own_hash_history.
      iExists hist, (<[id := mkLookupInfo key ver γdone LookupPending]> lookups).
      iFrame.
      iSplit.
      { iPureIntro. exact Hhistory_cur. }
      iSplit.
      - iPureIntro.
        intros id' linfo Hlookup.
        destruct (decide (id' = id)) as [->|Hneq].
        + rewrite lookup_insert in Hlookup.
          rewrite decide_True in Hlookup; [|done].
          inversion Hlookup; clear Hlookup; subst.
          cbn.
          lia.
        + rewrite lookup_insert_ne in Hlookup; [|done].
          eauto.
      - iPureIntro.
        intros id' linfo Hlookup Hold.
        destruct (decide (id' = id)) as [->|Hneq].
        + rewrite lookup_insert in Hlookup.
          rewrite decide_True in Hlookup; [|done].
          inversion Hlookup; clear Hlookup; subst.
          cbn in Hold.
          lia.
        + rewrite lookup_insert_ne in Hlookup; [|done].
          eapply Hold_done; eauto.
    }
    iExists γdone.
    iFrame.
    done.
  Qed.

  Lemma lookup_token_status_acc {γ id ver key Φ h γhist sub} :
    lookup_token γ id ver key Φ -∗
    ptsto_ro γ.(histories_name) h γhist -∗
    own_hash_history γhist 1 sub -∗
    ∃ info,
      ⌜info.(lookup_key) = key⌝ ∗
      ⌜info.(lookup_version) = ver⌝ ∗
      lookup_status_interp γ info Φ.
  Proof. Admitted.

  Lemma lookup_token_version_snapshot {γ id ver key Φ} :
    lookup_token γ id ver key Φ -∗
    ∃ h γhist (mver : gmap K V),
      ptsto_ro γ.(histories_name) h γhist ∗
      mono_list_idx_own γhist.(hh_hist_name) ver mver.
  Proof.
    iIntros "Htok".
    iDestruct "Htok" as (h γhist γdone mver) "(_ & #Hhist_name & #Hidx & _ & _)".
    iExists h, γhist, mver.
    iFrame "#".
  Qed.

  #[global] Opaque map_state.

End model.
