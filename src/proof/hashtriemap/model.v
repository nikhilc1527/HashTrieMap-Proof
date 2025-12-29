From New.generatedproof.hashtriemap Require Import hashtriemap.
From New.proof Require Import sync.
From New.proof.sync Require Import atomic.
From New.proof.sync_proof Require Import mutex.
From Perennial.algebra Require Import auth_map.
From Perennial.algebra Require Import ghost_var.
From Perennial.Helpers Require Import NamedProps.
Export named_props_ascii_notation.
From Perennial.Helpers.Word Require Import Integers.
From coqutil.Word Require Import Interface.
From iris.algebra Require Import gmap.
From Perennial.base_logic.lib Require Import invariants.
From iris.algebra Require Import dfrac.
From stdpp Require Import gmap list fin_maps.
From Coq Require Import List.
Import ListNotations.
From New.proof.hashtriemap Require Import aux.
Open Scope Z_scope.

Section model.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx: GoContext}.

  (* Ghost state for the abstract map (auth map from Perennial). *)
  Definition ht_map_auth `{!mapG Σ w64 w64} (γ: gname) (M: gmap w64 w64) : iProp Σ :=
    map_ctx γ 1 M.

  Definition ht_map_ptsto `{!mapG Σ w64 w64} (γ: gname) (k: w64) (v: w64) : iProp Σ :=
    ptsto_mut γ k 1 v.

  Definition ht_map_frag `{!mapG Σ w64 w64} (γ: gname) (m: gmap w64 w64) : iProp Σ :=
    ([∗ map] k ↦ v ∈ m, ht_map_ptsto γ k v).

  (* Ghost names (inspired by sharded_hashmap). *)
  Record ghost_names := mkNames {
                            user_name : gname;
                            map_name : gname;
                            init_name : gname;
                          }.

  Definition init_tok `{!ghost_varG Σ bool} (γ: ghost_names) (b: bool) : iProp Σ :=
    ghost_var γ.(init_name) (DfracOwn (1/2)) b.

  Definition hashtriemap_tok `{!ghost_varG Σ (gmap w64 w64)} (γ: ghost_names) (m: gmap w64 w64) :=
    ghost_var γ.(user_name) (DfracOwn (1/2)) m.

  Definition hashtriemap_auth `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (γ: ghost_names) (m: gmap w64 w64) : iProp Σ :=
    ht_map_auth γ.(map_name) m ∗
                    ghost_var γ.(user_name) (DfracOwn (1/2)) m.

  Definition hashtriemap_sub `{!mapG Σ w64 w64} (γ: ghost_names) (sub_m: gmap w64 w64) : iProp Σ :=
    ht_map_frag γ.(map_name) sub_m.

  Definition hashtriemap_pre_auth `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (γ: ghost_names) : iProp Σ :=
    ghost_var γ.(user_name) (DfracOwn (1/2)) (∅: gmap w64 w64) ∗
                  ht_map_auth γ.(map_name) (∅: gmap w64 w64).

  Lemma hashtriemap_pre_auth_to_auth `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (γ: ghost_names) :
    hashtriemap_pre_auth γ -∗ hashtriemap_auth γ (∅: gmap w64 w64).
  Proof.
    iIntros "[Huser Hmap]".
    iFrame.
  Qed.

  (* Concrete representation predicates. These are kept abstract but structured. *)
  Parameter entry_chain : loc → list (w64 * w64) → Prop.
  Parameter hash_key : w64 → w64.

  (* depth=0 at root, using top bits first (as in Go): idx = (h >> (64-4*(d+1))) & 0xF *)
  Definition hash_index (h: w64) (depth: nat) : nat :=
    let shift := 64 - 4 * (Z.of_nat (S depth)) in
    Z.to_nat (Z.land (Z.shiftr (word.unsigned h) shift) 15).

  (* prefix is the top 4*depth bits of h (lower bits zeroed). *)
  Definition hash_prefix (h: w64) (depth: nat) : w64 :=
    let shift := 64 - 4 * (Z.of_nat depth) in
    word.of_Z (Z.shiftl (Z.shiftr (word.unsigned h) shift) shift).

  (* extend prefix with the next 4-bit child index at depth+1. *)
  Definition child_prefix (prefix: w64) (depth idx: nat) : w64 :=
    let shift := 64 - 4 * (Z.of_nat (S depth)) in
    word.of_Z (word.unsigned prefix + Z.shiftl (Z.of_nat idx) shift).

  Definition same_hash (ks: list w64) : Prop :=
    ∀ k1 k2, k1 ∈ ks → k2 ∈ ks → hash_key k1 = hash_key k2.

  Definition entry_model (e: loc) (m: gmap w64 w64) : Prop :=
    ∃ kvs,
      entry_chain e kvs ∧
        m = list_to_map kvs ∧
        NoDup (map fst kvs) ∧
        same_hash (map fst kvs).

  (* trie_model should encode path/hash routing invariants for prefix/depth. *)
  Definition maps_union (ms: gmap nat (gmap w64 w64)) : gmap w64 w64 :=
    map_fold (λ _ m acc, m ∪ acc) ∅ ms.

  (* Optional strengthening assumptions/lemmas for later proofs. *)
  Definition children_disjoint (child_ms: gmap nat (gmap w64 w64)) : Prop :=
    ∀ i j m1 m2, child_ms !! i = Some m1 → child_ms !! j = Some m2 → i ≠ j → m1 ##ₘ m2.

  Lemma maps_union_lookup_disjoint (child_ms: gmap nat (gmap w64 w64)) idx m k v :
    children_disjoint child_ms →
    child_ms !! idx = Some m →
    m !! k = Some v →
    maps_union child_ms !! k = Some v.
  Proof.
    revert idx m k v.
    induction child_ms as [|i x m' Hnone Hfold IH] using map_fold_fmap_ind.
    - intros idx m k v Hdisj Hidx Hmk. rewrite lookup_empty in Hidx. congruence.
    - intros idx m k v Hdisj Hidx Hmk.
      (* specialize the fold equation for union *)
      have Hfold' := Hfold (gmap w64 w64) (gmap w64 w64)
                       (λ _ m acc, m ∪ acc) (λ y, y) ∅ x.
      simpl in Hfold'. rewrite map_fmap_id in Hfold'. simpl in Hfold'.
      rewrite /maps_union in Hfold'.
      specialize (Hfold' _ _).
      (* split on whether idx is the inserted key *)
      destruct (decide (idx = i)) as [->|Hneq].
      + rewrite lookup_insert_eq in Hidx. inversion Hidx. subst m. clear Hidx.
        rewrite /maps_union. rewrite Hfold'.
        (* left map wins the union lookup *)
        by eapply lookup_union_Some_l.
      + rewrite lookup_insert_ne in Hidx; [|done].
        rewrite /maps_union. rewrite Hfold'.
        (* show x does not have key k using disjointness with m *)
        assert (Hdisj_x : x ##ₘ m).
        { apply (Hdisj i idx x m); try done.
          - rewrite lookup_insert_eq. done.
          - rewrite lookup_insert_ne; done. }
        assert (Hxnone : x !! k = None).
        { destruct (x !! k) eqn:Hxk; [|done].
          exfalso.
          have Hdisj_spec := map_disjoint_spec x m.
          rewrite Hdisj_spec in Hdisj_x.
          apply (Hdisj_x k w v); auto. }
        rewrite (lookup_union_r _ _ _ Hxnone).
        (* restrict disjointness to the tail map *)
        assert (Hdisj_m : children_disjoint m').
        { intros j1 j2 m1 m2 Hj1 Hj2 Hne.
          assert (Hj1ne : j1 ≠ i).
          { intros ->. rewrite Hnone in Hj1. inversion Hj1. }
          assert (Hj2ne : j2 ≠ i).
          { intros ->. rewrite Hnone in Hj2. inversion Hj2. }
          apply (Hdisj j1 j2 m1 m2).
          - rewrite lookup_insert_ne; [exact Hj1|intro H; apply Hj1ne; symmetry; exact H].
          - rewrite lookup_insert_ne; [exact Hj2|intro H; apply Hj2ne; symmetry; exact H].
          - exact Hne. }
        eapply IH; eauto.
  Qed.

  Definition trie_model (i: loc) (prefix: w64) (depth: nat) (m: gmap w64 w64) : Prop :=
    (∃ child_ms,
        m = maps_union child_ms ∧
          (∀ idx sub_m, child_ms !! idx = Some sub_m →
                        (∀ k v, sub_m !! k = Some v →
                                hash_prefix (hash_key k) depth = prefix ∧
                                  hash_index (hash_key k) depth = idx))) ∧
      (depth < 16)%nat.

  Definition child_node (children: vec atomic.Value.t (uint.nat (W64 16)))
    (idx: nat) (n: loc) : Prop :=
    ∃ av, vec_to_list children !! idx = Some av ∧ atomic_value_model av (Some n).

  Definition child_nil (children: vec atomic.Value.t (uint.nat (W64 16)))
    (idx: nat) : Prop :=
    ∃ av, vec_to_list children !! idx = Some av ∧ atomic_value_model av None.

  Definition node_is_entry (n e: loc) : iProp Σ :=
    n ↦s[hashtriemap.node :: "isEntry"] (true) ∗
      n ↦s[hashtriemap.node :: "ent"] e ∗
      n ↦s[hashtriemap.node :: "ind"] (null).

  Definition node_is_indirect (n i: loc) : iProp Σ :=
    n ↦s[hashtriemap.node :: "isEntry"] (false) ∗
      n ↦s[hashtriemap.node :: "ent"] (null) ∗
      n ↦s[hashtriemap.node :: "ind"] i.

  Definition node_model (n: loc) (m: gmap w64 w64) : iProp Σ :=
    (∃ e, node_is_entry n e ∗ ⌜entry_model e m⌝) ∨
      (∃ i, node_is_indirect n i ∗ ⌜trie_model i 0 0 m⌝).

  Definition children_model
    (children: vec atomic.Value.t (uint.nat (W64 16)))
    (prefix: w64) (depth: nat)
    (child_ms: gmap nat (gmap w64 w64)) : iProp Σ :=
    ∀ (idx: nat),
      ⌜(idx < 16)%nat⌝ -∗
                          ((∃ sub_m, ⌜child_ms !! idx = Some sub_m⌝ ∗
                                                          ((∃ n, ⌜child_node children idx n⌝ ∗
                                                                   ((∃ e, node_is_entry n e ∗ ⌜entry_model e sub_m⌝) ∨
                                                                      (∃ i, node_is_indirect n i ∗
                                                                              ⌜trie_model i (child_prefix prefix depth idx) (S depth) sub_m⌝)))
                                                           ∨ (⌜child_nil children idx⌝ ∗ ⌜sub_m = ∅⌝)))
                           ∨ (⌜child_ms !! idx = None⌝ ∗ ⌜child_nil children idx⌝)).

  Definition entry_rep (e: loc) (m: gmap w64 w64) : iProp Σ :=
    ⌜entry_model e m⌝.

  Definition node_rep (n: loc) (m: gmap w64 w64) : iProp Σ :=
    node_model n m.

  Definition indirect_rep (i: loc) (prefix: w64) (depth: nat) (m: gmap w64 w64) : iProp Σ :=
    ⌜trie_model i prefix depth m⌝.

  (* Per-indirect lock invariant. *)
  Definition indirect_inv `{!mapG Σ w64 w64} (γ: ghost_names) (i: loc)
    (prefix: w64) (depth: nat) (M: gmap w64 w64) : iProp Σ :=
    ∃ (child_ms: gmap nat (gmap w64 w64)) (dead: atomic.Bool.t)
      (node parent: loc) (children: vec atomic.Value.t (uint.nat (W64 16))),
      i ↦s[hashtriemap.indirect :: "node"] node ∗
        node_is_indirect node i ∗
        i ↦s[hashtriemap.indirect :: "dead"] dead ∗
        i ↦s[hashtriemap.indirect :: "parent"] parent ∗
        i ↦s[hashtriemap.indirect :: "children"] children ∗
        children_model children prefix depth child_ms ∗
        ⌜maps_union child_ms = M⌝ ∗
                                 indirect_rep i prefix depth M ∗
                                 hashtriemap_sub γ M.

  Definition is_indirect `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (γ: ghost_names) (i: loc) (prefix: w64) (depth: nat) (M: gmap w64 w64) : iProp Σ :=
    is_Mutex (struct.field_ref_f hashtriemap.indirect "mu" i)
      (indirect_inv γ i prefix depth M).

  (* Global invariant tying the trie to the abstract map. *)
  Definition ht_inv `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (seed: w64) (i: loc) M,
      ht ↦s[hashtriemap.HashTrieMap :: "seed"] seed ∗
        own_Value  (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) (DfracOwn 1)
        (Some (# (interface.mk (ptrT.id hashtriemap.indirect.id) (# i)))) ∗
        is_indirect γ i 0 0 M ∗
        hashtriemap_auth γ M.

  (* Public predicate exposed to clients. *)
  Let N := nroot .@ "hashtriemap".
  Definition init_statusN : namespace := nroot .@ "hashtriemap.init_status".

  Definition is_hashtriemap `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    inv N (ht_inv ht γ).

  Definition init_status_done
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
    (γ: ghost_names) (ht: loc) (b: bool) : iProp Σ :=
    (if b then is_hashtriemap γ ht else True%I).

  Definition init_status_inv
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      own_Uint32 (struct.field_ref_f hashtriemap.HashTrieMap "inited" ht) (DfracOwn 1)
        (if b then W32 1 else W32 0) ∗
        init_tok γ b ∗
        □ init_status_done γ ht b.

  Definition init_status
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    inv init_statusN (init_status_inv ht γ).

  (* Initialization lock invariant for HashTrieMap. *)
  Definition init_mu_inv `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      if b
      then init_tok γ true
      else (init_tok γ false ∗
              (∃ (seed: w64),
                  ht ↦s[hashtriemap.HashTrieMap :: "seed"] seed) ∗
              own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) (DfracOwn 1) None ∗
              hashtriemap_pre_auth γ)%I.

  Definition init_mu `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    is_Mutex (struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht)
      (init_mu_inv ht γ).

  Definition hashtriemap_init
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    init_status ht γ ∗ init_mu ht γ ∗ hashtriemap_tok γ (∅: gmap w64 w64).

  Lemma hashtriemap_pre_auth_init
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool} :
    ⊢ |==> ∃ γ, hashtriemap_pre_auth γ ∗ init_tok γ false ∗ init_tok γ false ∗
                  hashtriemap_tok γ (∅: gmap w64 w64).
  Proof.
    iMod (ghost_var_alloc (false)) as (init_γ) "[Hinit1 Hinit2]".
    iMod (ghost_var_alloc (∅ : gmap w64 w64)) as (user_γ) "[Huser Hvar]".
    iMod (map_init (∅ : gmap w64 w64)) as (map_γ) "Hmap".
    iModIntro.
    iExists (mkNames user_γ map_γ init_γ).
    iFrame.
  Qed.

  Lemma hashtriemap_zero_init
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool, !syncG Σ}
    (ht: loc) :
    own_Uint32 (struct.field_ref_f hashtriemap.HashTrieMap "inited" ht) (DfracOwn 1) (W32 0) -∗
                                                                                                (struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht) ↦ (default_val sync.Mutex.t) -∗
                                                                                                                                                                                         own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) (DfracOwn 1) None -∗
                                                                                                                                                                                                                                                                               ht ↦s[hashtriemap.HashTrieMap :: "seed"] (W64 0) -∗
                                                                                                                                                                                                                                                                                                                                   |==> ∃ γ,
                                                                                                                                                                                                                                                                                                                                     hashtriemap_init ht γ.
  Proof. Admitted.

End model.
