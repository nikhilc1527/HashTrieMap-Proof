From iris.bi.lib Require Import fixpoint_mono.
From iris.bi.lib Require Import fractional.
From New.code.hashtriemap Require Import hashtriemap.
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
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
           `{!globalsGS Σ, !ghost_varG Σ (gmap w64 w64)} {go_ctx: GoContext}.

  (* namespace definitions *)
  Definition mapN         : namespace := nroot .@ "hashtriemap".
  Definition init_statusN : namespace := nroot .@ "hashtriemap.init_status".

  (* just to be clear, and to not get confused with w64's everywhere *)
  Definition K : Type := w64.
  Definition V : Type := w64.
  Definition hashT : Type := w64.

  Definition nibble : Type := Z.
  Definition nibble_list : list nibble :=
    seqZ 0 16.
  Definition path : Type := list nibble.
  Definition domain : Type := list Z.

  Definition full_domain : domain :=
    seqZ 0 (2^64).

  (* ghost state:  *)

  Definition path_to_prefix := foldl (λ acc x, acc ≪ 4 + x) 0.

  (* free bits *)
  Definition sh (p : path) : Z :=
    64 - 4 * length p.

  Definition lo (p : path) : Z := (path_to_prefix p)     ≪ sh p.
  Definition hi (p : path) : Z := (path_to_prefix p + 1) ≪ sh p.

  Definition belongs_to_path p k :=
    k ≫ sh p = path_to_prefix p.

  #[global] Instance belongs_to_path_dec p k : Decision (belongs_to_path p k).
  Proof.
    unfold belongs_to_path.
    apply _.
  Qed.

  Definition path_to_domain (p : path) : domain :=
    base.filter
      (belongs_to_path p)
      (full_domain).

  (* Definition path_ok (p : path) : Prop := *)
  (*   length p ≤ 16 ∧ Forall (λ n, n ∈ nibble_list) p. *)

  (* Definition P (p : path) k : Prop := *)
  (*   k ≫ (sh p) = pref p. *)

  Lemma path_to_prefix_snoc (p : path) (n : nibble) :
    path_to_prefix (p ++ [n]) =
    ((path_to_prefix p) ≪ 4) + n.
  Proof.
    unfold path_to_prefix.
    (* use foldl_app; stdpp has foldl_app, otherwise prove it *)
    rewrite foldl_app.
    simpl.
    reflexivity.
  Qed.

  (* TODO: replace all the 4's with hashtriemap.nChildrenLog2, 16 with hashtriemap.nChildren *)

  Lemma len_snoc (p : path) (n : nibble) :
    length (p ++ [n]) = S (length p).
  Proof.
    rewrite app_length /=.
    word.
  Qed.

  Lemma sh_snoc (p : path) (n : nibble) :
    sh (p ++ [n]) = sh p - 4.
  Proof.
    unfold sh.
    rewrite app_length /=.
    lia.
  Qed.

  Lemma sh_nonneg (p : path) :
    (Z.of_nat (length p) < 64 `div` 4)%Z ->
    0 ≤ sh p.
  Proof.
    unfold sh.
    word.
  Qed.

  Lemma shiftr_eq_iff_interval (p : path) (u : Z) :
    0 ≤ sh p ->
    0 ≤ u ->
    (u ≫ (sh p) = path_to_prefix p) ↔ (lo p ≤ u < hi p).
  Proof.
    intros Hsh_nonneg Hu_nonneg.
    repeat unfold lo, hi in *.
    set (pp := path_to_prefix p) in *.
    set (s := sh p) in *.
    repeat rewrite Z.shiftr_div_pow2; try word.
    repeat rewrite Z.shiftl_mul_pow2; try word.
    set (b := 2 ^ s) in *.
    have Hbne : b > 0.
    { unfold b. word. }
    
    split.
    - intro H.
      rewrite (Z.div_mod u b).
      2: { word. }
      rewrite H.
      split.
      + word.
      + have Hmod : 0 <= u mod b < b by apply Z.mod_pos_bound; lia.
        lia.
    - intros [Hlo Hhi].
      have H : (pp = u `div` b ↔ u `div` b = pp) by word.
      rewrite -H.
      apply (Z.div_unique u b pp (u - pp*b)).
      + lia.
      + have : 0 <= u - pp*b < b by lia.
        word.
  Qed.

  Lemma interval_split (p : path) (n : Z) :
    4 ≤ sh p ->
    lo (p ++ [n]) = lo p + n * (2 ^ (sh p - 4)).
  Proof.
    (* expand lo, use path_to_prefix_snoc + sh_snoc + shiftl algebra *)
    intros Hsh_nonneg.
    unfold lo.
    rewrite path_to_prefix_snoc.
    rewrite sh_snoc.
    simpl.
    repeat rewrite Z.shiftl_mul_pow2; try word.
    rewrite Z.mul_add_distr_r.
    have Hpow : 2 ^ 4 * 2 ^ (sh p - 4) = 2 ^ (sh p).
    {
      rewrite -Z.pow_add_r; try word.
      simpl.
      have H : 4 + (sh p - 4) = sh p by word.
      rewrite H.
      reflexivity.
    }
    have H : path_to_prefix p * 2 ^ 4 * 2 ^ (sh p - 4) + n * 2 ^ (sh p - 4) = path_to_prefix p * (2 ^ 4 * 2 ^ (sh p - 4)) + n * 2 ^ (sh p - 4) by lia.
    rewrite H.
    rewrite Hpow.
    done.
  Qed.

  Lemma interval_consecutive (p : path) (n : Z) :
    4 ≤ sh p ->
    hi (p ++ [n]) = lo (p ++ [n+1]).
  Proof.
    intros Hsh_nonneg.
    repeat unfold hi, lo in *.
    repeat rewrite path_to_prefix_snoc.
    repeat rewrite sh_snoc.
    have H : path_to_prefix p ≪ 4 + n + 1 = path_to_prefix p ≪ 4 + (n + 1) by lia.
    rewrite H.
    reflexivity.
  Qed.

  Lemma full_domain_elem (k : w64) :
    uint.Z k ∈ full_domain.
  Proof.
    unfold full_domain.
    apply elem_of_seqZ; word.
  Qed.

  Lemma path_to_domain_elem (p : path) (k : Z) :
    k ∈ full_domain →
    k ∈ path_to_domain p ↔ k ≫ sh p = path_to_prefix p.
  Proof.
    intro Hk.
    unfold path_to_domain.
    rewrite list_elem_of_filter.
    split; intro H.
    - destruct H as [Hk' Hpred].
      exact Hk'.
    - split; done.
  Qed.

  Lemma nibble_list_range (n : Z) :
    n ∈ nibble_list ↔ 0 ≤ n < 16.
  Proof.
    apply elem_of_seqZ.
  Qed.

  Lemma next_nibble_exists (p : path) (k : Z) :
    0 ≤ k →
    length p < 16 ->
    belongs_to_path p k ->
    ∃ n, 0 ≤ n < 16 ∧ belongs_to_path (p ++ [n]) k.
  Proof.
    intros Hk Hlen Hbelong.
    unfold belongs_to_path in *.
    unfold lo, hi in *.
    set (s := sh p) in *.
    set (pp := path_to_prefix p) in *.
    have Hinterval : pp ≪ s ≤ k < (pp + 1) ≪ s.
    {
      apply shiftr_eq_iff_interval; [|word|word].
      unfold sh.
      word.
    }
    set (n := Z.land (k ≫ (s - 4)) (Z.ones 4)).
    exists n.
    split.
    - (* show 0 ≤ n < 16 *)
      unfold n.
      set (x := k ≫ (s - 4)).
      have Hland : Z.land x 15 = x mod 2^4.
      { change 15 with (Z.ones 4) in *. rewrite Z.land_ones; auto. word. }
      rewrite Hland. apply Z.mod_pos_bound.
      word.
    - (* show belongs_to_path (p ++ [n]) k *)
      unfold belongs_to_path.
      have Hs : 4 ≤ sh p.
      {
        unfold sh.
        word.
      }
      replace (sh (p ++ [n])) with (s - 4) by (rewrite sh_snoc; word).
      rewrite path_to_prefix_snoc.
      set (x := k ≫ (s-4)).
      assert (Hxmod : x mod 16 = n).
      {
        subst x n. change 16 with (2^4).
        rewrite Z.land_ones; try word.
      }
      assert (Hxdiv : x / 16 = pp).
      {
        subst x.
        rewrite Z.shiftr_div_pow2; [|word].
        rewrite Z.shiftr_div_pow2 in Hbelong; [|word].
        rewrite Z.pow_sub_r; try word.
        rewrite -Hbelong.
        replace (2^4) with 16 by word.
        set (x := 2^s).
        have Hxge16 : (16 ≤ x).
        {
          unfold x, s.
          change (16 ≤ 2 ^ sh p) with (2 ^ 4 ≤ 2 ^ (sh p)).
          apply Z.pow_le_mono_r; lia.
        }
        rewrite Z.div_div; [|word|word].
        have Hx : x mod 16 = 0.
        {
          unfold x.
          have Ht : s mod 4 = 0 by (unfold s, sh; word).
          have Hdiv : Z.divide 4 s.
          { apply Z.mod_divide; lia. }
          destruct Hdiv as [y Hy].
          replace (y * 4) with (4 * y) in Hy by word.
          rewrite Hy.
          rewrite Z.pow_mul_r; [|word|word].
          replace (2^4) with 16 by word.
          have Hypos : 1 ≤ y by lia.
          have Hdiv : Z.divide 16 (16 ^ y).
          {
            exists (16 ^ (y - 1)).
            replace y with (y - 1 + 1) by lia.
            rewrite Z.pow_succ_r; [|word].
            simpl.
            replace (y - 1 + 1 - 1) with (y - 1) by word.
            word.
          }
          rewrite Z.mod_divide; [|word].
          exact Hdiv.
        }
        replace (x / 16 * 16) with (x) by word.
        reflexivity.
      }
      have Hx : x = pp * 16 + n.
      {
        rewrite (Z.div_mod x 16); word.
      }
      change 16 with (2^4) in Hx.
      rewrite -Z.shiftl_mul_pow2 in Hx; try word.
      exact Hx.
  Qed.

  Lemma next_nibble_unique (p : path) (k : Z) n1 n2 :
    belongs_to_path (p ++ [n1]) k ->
    belongs_to_path (p ++ [n2]) k ->
    n1 = n2.
  Proof.
    intros H1 H2.
    unfold belongs_to_path in *.
    have Hlen : sh (p ++ [n1]) = sh (p ++ [n2]) by
      rewrite !sh_snoc; lia.
    rewrite Hlen in H1.
    (* now both equal the same LHS *)
    have Hpref : path_to_prefix (p ++ [n1]) = path_to_prefix (p ++ [n2]) by
      etrans; [symmetry; exact H1| exact H2].
    rewrite !path_to_prefix_snoc in Hpref.
    word.
  Qed.

  Lemma path_to_domain_split (p : path) :
    length p < 16 ->            (* length p < (sizeof hashT) / nChildrenLog2 *)
    path_to_domain p =
    concat (map (λ n, path_to_domain (p ++ [n])) nibble_list).
  Proof.
    intro Hlen.
    apply list_eq. intros.
    apply option_eq; intro k.
    split; intro H.
    - (* → *)
      apply list_elem_of_lookup_2 in H.
      rewrite list_elem_of_filter in H.
      destruct H as [Hbelong Hfull].
      (* Hfull: k ∈ full_domain *)
      rewrite elem_of_seqZ in Hfull.
      have Hk_nonneg : 0 ≤ k := proj1 Hfull.
      destruct (next_nibble_exists p k) as [x [Hnrange Hbelongn]];
        try done.
      set (l := concat (map (λ n : nibble, path_to_domain (p ++ [n])) nibble_list)).
  Admitted.

  Definition hash_map : Type := gmap Z (gmap K V).

  Definition empty_hash_map : hash_map :=
    gset_to_gmap ∅ (list_to_set full_domain).

  (* own the whole w64 domain, using lookup to decide Some/None *)
  Definition own_domain
    `{!mapG Σ K V}
    `{!mapG Σ Z (gmap K V)}
    (γ : gname) d (dom : domain) (hm : hash_map) : iProp Σ :=
    [∗ list] hash ∈ dom, ∃ sub_m, ⌜hm !! hash = Some(sub_m)⌝ ∗ ptsto_mut γ hash d sub_m.

  (* own some subdomain of all w64's *)
  Definition own_path
               `{!mapG Σ K V}
               `{!mapG Σ Z (gmap K V)}
               (γ : gname) (p : path) (hm : hash_map) d : iProp Σ :=
    own_domain γ d (path_to_domain p) hm.

  (* pure definitions, mostly hash-related stuff *)
  Parameter hash_key : w64 → w64.


  (* index is the 4 bits at depth (0-based) of h. *)

  (* Definition hash_index (h: w64) (depth: nat) : nat := *)
  (*   let shift := 64 - 4 * (Z.of_nat (S depth)) in *)
  (*   Z.to_nat (Z.land (Z.shiftr (word.unsigned h) shift) 15). *)

  (* (* prefix is the top 4*depth bits of h (lower bits zeroed). *) *)
  (* Definition hash_prefix (h: w64) (depth: nat) : w64 := *)
  (*   let shift := 64 - 4 * (Z.of_nat depth) in *)
  (*   word.of_Z (Z.shiftl (Z.shiftr (word.unsigned h) shift) shift). *)

  (* (* extend prefix with the next 4-bit child index at depth+1. *) *)
  (* Definition child_prefix (prefix: w64) (depth idx: nat) : w64 := *)
  (*   let shift := 64 - 4 * (Z.of_nat (S depth)) in *)
  (*   word.of_Z (word.unsigned prefix + Z.shiftl (Z.of_nat idx) shift). *)

  Definition same_hash (ks: list w64) : Prop :=
    ∀ k1 k2, k1 ∈ ks → k2 ∈ ks → hash_key k1 = hash_key k2.

  Definition own_hash (path: list Z) (hash: Z) : Prop :=
    Z.shiftr hash (hashtriemap.hashBits - hashtriemap.nChildrenLog2 * Z.of_nat (length path)) = (path_to_prefix path).

  #[global] Instance own_hash_dec path hash : Decision (own_hash path hash).
  Proof.
    unfold own_hash.
    apply _.
  Qed.

  (* Ghost state for the hashtriemap. *)

  Record ghost_names := mkNames {
                           map_name : gname;
                           init_name : gname;
                         }.

  (* both of these are designed to be split between an invariant and a mutex, so that reading can be done outside of the critical section and writing can only be done inside *)
  Definition init_tok `{!ghost_varG Σ bool} (γ: ghost_names) (b: bool) : iProp Σ :=
    ghost_var γ.(init_name) (DfracOwn (1/2)) b.

  Definition indirect_par node_inv (γ: ghost_names) (ind: loc) (path: list Z) : iProp Σ :=
    ∃ (children: list loc),
      (* ownership of the indirect struct’s children field *)
      let tok := (
                  ind ↦s[hashtriemap.indirect :: "children"]{DfracOwn (1/2)} children ∗
                  ⌜Z.of_nat (length children) = hashtriemap.nChildren ⌝ ∗
                  (* for each child slot, either empty or a node_inv *)
                  ([∗ list] i ↦ cloc ∈ children,
                     ∃ (nptr: loc),
                       own_Value cloc (DfracOwn (1/2)) (interface.mk (ptrT.id hashtriemap.node.id) #nptr) ∗
                       (⌜ nptr = null ⌝ ∨ node_inv (DfracOwn (1/2)) nptr (path ++ [Z.of_nat i])))
                )%I
      in
      (* splitting half outside, half inside the mutex for lock-free read and locked write *)
      tok ∗ is_Mutex (struct.field_ref_f hashtriemap.indirect "mu" ind) tok.

  Definition entry_recF (γ: ghost_names) d (Φ: loc * gmap w64 w64 → iProp Σ)
    : loc * gmap w64 w64 → iProp Σ :=
    λ '(ent,owned_ghost),
      (if bool_decide (ent = null) then
         ⌜ owned_ghost = ∅ ⌝
       else
         ∃ (k: w64) (v: w64) (overflow: loc) (overflow_loc: loc) (rest: gmap w64 w64),
           ent ↦s[hashtriemap.entry :: "key"] k ∗
           ent ↦s[hashtriemap.entry :: "value"] v ∗
           ent ↦s[hashtriemap.entry :: "overflow"] overflow ∗
           own_Value overflow d (interface.mk (ptrT.id hashtriemap.entry.id) (# overflow_loc)) ∗
           ⌜ owned_ghost = <[k := v]> rest ⌝ ∗
           Φ (overflow_loc, rest))%I.

  Definition entry_rec (γ: ghost_names) (ent: loc) (owned_ghost: gmap w64 w64) d : iProp Σ :=
    bi_least_fixpoint (entry_recF γ d) (ent, owned_ghost).

  Definition entry (γ: ghost_names) (e: loc) (path: list Z) d : iProp Σ :=
    ∃ (m: gmap w64 w64) (owned_ghost: gmap w64 w64),
      entry_rec γ e owned_ghost d.

  Definition nodeF (γ: ghost_names)
                   (Φ: dfrac * loc * list Z → iProp Σ)
    : dfrac * loc * list Z → iProp Σ :=
    λ '(d, n, path),
      (
        ∃ (is_entry: bool),
          n ↦s[hashtriemap.node :: "isEntry"] is_entry ∗
          if is_entry
          then
            let entry_loc := struct.field_ref_f hashtriemap.node "entry" n in
            entry γ entry_loc path d
          else
            let indirect_loc := struct.field_ref_f hashtriemap.node "indirect" n in
            indirect_par (curry3 Φ) γ indirect_loc path
      )%I.

  Definition node (γ: ghost_names) d n path : iProp Σ :=
    bi_least_fixpoint (nodeF γ) (d, n, path).

  Definition indirect γ := indirect_par (node γ) γ.

  (* Global invariant tying the trie to the abstract map. *)
  Definition ht_inv `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
                    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (i: loc),
      own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) 1
                (interface.mk (ptrT.id hashtriemap.indirect.id) (# i)) ∗
      indirect γ i [].

  (* Public predicate exposed to clients. *)
  (* HOCAP style *)
  Definition is_hashtriemap `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
                            (γ: ghost_names) (ht: loc)
                            (* (P: gmap w64 w64 → iProp Σ) *) : iProp Σ :=
    inv mapN (
          (* ∃ m, *)
            (* "HP" :: P m ∗ *)
            "Hinv" :: ht_inv ht γ).

  Definition init_status_done
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
               (γ: ghost_names) (ht: loc) (b: bool)
               (* (P: gmap w64 w64 → iProp Σ) *) : iProp Σ :=
    (if b then is_hashtriemap γ ht (* P *) else True%I).

  Definition init_status_inv
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
               (ht: loc) (γ: ghost_names) (* (P: gmap w64 w64 → iProp Σ) *) : iProp Σ :=
    ∃ (b: bool),
      own_Uint32 (struct.field_ref_f hashtriemap.HashTrieMap "inited" ht) 1
                 (if b then W32 1 else W32 0) ∗
      init_tok γ b ∗
      □ init_status_done γ ht b (* P *).

  Definition init_status
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
               (ht: loc) (γ: ghost_names) (* P *) : iProp Σ :=
    inv init_statusN (init_status_inv ht γ (* P *)).

  (* Initialization lock invariant for HashTrieMap. *)
  Definition init_mu_inv `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
                         (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      if b
      then init_tok γ true
      else (init_tok γ false ∗
            (∃ (seed: w64),
                ht ↦s[hashtriemap.HashTrieMap :: "seed"] seed) ∗
            own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) 1 interface.nil
           )%I.

  Definition init_mu `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
                     (ht: loc) (γ: ghost_names) : iProp Σ :=
    is_Mutex (struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht)
             (init_mu_inv ht γ).

  Definition hashtriemap_init
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
               (ht: loc) (γ: ghost_names) (* P *) : iProp Σ :=
    init_status ht γ (* P *) ∗ init_mu ht γ (* ∗ P ∅ *).

  Lemma hashtriemap_pre_auth_init
          `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool} :
    ⊢ |==> ∃ γ, init_tok γ false ∗ init_tok γ false.
  Proof.
    iMod (ghost_var_alloc (false)) as (init_γ) "[Hinit1 Hinit2]".
    iMod (ghost_var_alloc (∅ : gmap w64 w64)) as (map_γ) "[Huser Hvar]".
    iModIntro.
    iExists (mkNames map_γ init_γ).
    iFrame.
  Qed.

  Lemma hashtriemap_zero_init
          `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
          (ht: loc) E (P: gmap w64 w64 → iProp Σ) :
    ht ↦ default_val hashtriemap.HashTrieMap.t (* ∗ P ∅ *) ⊢
    |={E}=> ∃ γ, hashtriemap_init ht γ (* P *).
  Proof.
    iIntros "Hht".
    iDestruct (struct_fields_split with "Hht") as "Hfields".
    iNamed "Hfields".
    simpl.
    iMod (hashtriemap_pre_auth_init) as (γ) "(Htok1 & Htok2)".

    iApply struct_fields_split in "Hinited".
    iNamed "Hinited".
    iDestruct (Uint32_unfold with "Hv") as "Hinited".
    iClear "H_0".

    iApply struct_fields_split in "Hroot".
    iNamed "Hroot".
    iDestruct (Value_unfold with "Hv") as "Hroot".

    iMod (inv_alloc init_statusN _ (init_status_inv ht γ (* P *)) with "[Htok1 Hinited]") as "#Hinit".
    {
      iNext.
      iExists false.
      iFrame.
      simpl.
      done.
    }

    iAssert (▷ init_mu_inv ht γ)%I with "[Htok2 Hseed Hroot]" as "Hmu_inv".
    {
      iNext.
      iExists false.
      iFrame "Htok2".
      iSplitL "Hseed".
      { iExists (W64 0). iFrame. }
      iFrame "Hroot".
    }

    set (m := struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht).

    iAssert (|={E}=> is_Mutex m (init_mu_inv ht γ))%I with "[HinitMu Hmu_inv]" as "Hmutex".
    {
      iDestruct (init_Mutex (init_mu_inv ht γ) ⊤ m with "[$]") as "Hmu".
      iSpecialize ("Hmu" with "Hmu_inv").
      (* iExact "Hmu". *)
      (* TODO *)
      (* Error: Tactic failure: iExact: "Hmu" : (|={⊤}=> is_Mutex m (init_mu_inv ht γ))%I does not match goal. *)
      (* goal: *)
      (* |={⊤}=> is_Mutex m (init_mu_inv ht γ) *)
      (* ????? *)
      admit.
    }

    iMod "Hmutex".

    iModIntro.
    iExists γ.
    iFrame "Hinit Hmutex".
  Admitted.

End model.
