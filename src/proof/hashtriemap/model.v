From iris.bi.lib Require Import fractional.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From Perennial.algebra Require Import ghost_var.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Export paths.

Open Scope Z_scope.

Section model.
  (* namespace definitions *)
  Definition mapN         : namespace := nroot .@ "hashtriemap".
  Definition init_statusN : namespace := nroot .@ "hashtriemap.init_status".
  Definition indN         : namespace := nroot .@ "indirect".
  Definition entryN       : namespace := nroot .@ "entry".

  (* Ghost state for the hashtriemap. *)
  Record ghost_names := mkNames {
                            map_name : gname;
                            init_name : gname;
                            user_name : gname;
                          }.

  (* just to be clear, and to not get confused with w64's everywhere *)
  Definition K : Type := w64.
  Definition V : Type := w64.
  Definition hashT : Type := w64.

  Context `{hG: heapGS Σ, !ffi_semantics _ _}
    `{!globalsGS Σ, !ghost_varG Σ (gmap w64 w64)}
    `{!mapG Σ K V}
    `{!mapG Σ Z (gmap K V)}
    {go_ctx: GoContext}.

  Definition hash_map : Type := gmap Z (gmap K V). (* TODO: should be gmap hashT (gmap K V), its just Z for now to make the above helper lemmas easier *)

  Definition empty_hash_map : hash_map :=
    gset_to_gmap ∅ (list_to_set full_domain).

  Parameter hash_key : w64 → w64.

  Definition own_domain
    (γ : gname) (q: Qp) (dom : domain) (f: Z → gmap K V) : iProp Σ :=
    [∗ list] hash ∈ dom, ptsto_mut γ hash q (f hash).

  Global Opaque own_domain.
  Local Transparent own_domain.

  Definition own_path
    (γ : gname) (q: Qp) (p : path) (f: Z → gmap K V) : iProp Σ :=
    own_domain γ q (path_to_domain p) f.

  Global Opaque own_path.
  Local Transparent own_path.

  (* Constant function: all hashes map to empty *)
  Definition empty_map_fn : Z → gmap K V := λ _, ∅.

  (* Single hash has value, rest are empty *)
  Definition singleton_map_fn (h: Z) (m: gmap K V) : Z → gmap K V :=
    λ h', if decide (h' = h) then m else ∅.

  Definition flatten (hm: hash_map) : gmap K V :=
    map_fold (λ (_: Z) (sub: gmap K V) (acc: gmap K V), sub ∪ acc) ∅ hm.

  #[global] Instance own_path_timeless γ dom q f : Timeless (own_path γ q dom f) := _.

  #[global] Instance own_path_fractional γ dom f :
    Fractional (λ q, own_path γ q dom f).
  Proof.
    intros p q. rewrite /own_path /own_domain -big_sepL_sep.
    iSplit.
    - iIntros "H1".
      iApply (big_sepL_mono with "H1").
      iIntros (i h Hin) "Hh1".
      iDestruct "Hh1" as "[Hh1 Hh2]".
      iFrame.
    - iIntros "H1".
      iApply (big_sepL_mono with "H1").
      iIntros (i h Hin) "Hh1".
      iDestruct "Hh1" as "[Hh1 Hh2]".
      iCombine "Hh1 Hh2" as "Hh".
      iFrame.
  Qed.

  #[global] Instance own_path_as_fractional γ path f q :
    AsFractional (own_path γ q path f) (λ q, own_path γ q path f) q.
  Proof.
    split; [done|apply _].
  Qed.

  Definition entry_inv
    (γ: ghost_names) (q: Qp)
    (entry: loc -d> path -d> iProp Σ)
    (e: loc) (path: path) : iProp Σ :=
    (if decide (e = null) then
       own_path γ.(map_name) q path empty_map_fn
     else
       ∃ (next: loc) (k: K) (v: V) (h: Z) rest_map,
         "#Hk" :: e ↦s[hashtriemap.entry :: "key"]□ k ∗
         "#Hv" :: e ↦s[hashtriemap.entry :: "value"]□ v ∗
         "%Hhash" :: ⌜uint.Z (hash_key k) = h⌝ ∗
         "%Hbelongs" :: ⌜belongs_to_path path h⌝ ∗
         "Hown_next" :: (struct.field_ref_f hashtriemap.entry "overflow" e) ↦ᵥ{q} (interface.mk (ptrT.id hashtriemap.entry.id) #next) ∗
         "Hown_path" :: own_path γ.(map_name) q path (singleton_map_fn h (<[k:=v]> rest_map)) ∗
         if decide (next = null) then
           ⌜rest_map = ∅⌝
         else
           "#Hnext_entry" :: ▷ entry next path)%I.

  Definition entry_F
    (γ: ghost_names) (q: Qp)
    (entry: loc -d> path -d> iProp Σ)
    : loc -d> path -d> iProp Σ :=
    λ e path,
      ("#Hentry_inv" :: inv entryN (entry_inv γ q entry e path))%I.

  Global Instance entry_F_contractive γ q : Contractive (entry_F γ q).
  Proof.
    rewrite /entry_F /entry_inv.
    intros n f g Hfg e path.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    solve_contractive.
  Qed.

  Definition entry (γ: ghost_names) (q: Qp) (e: loc) (path: path) : iProp Σ :=
    fixpoint (entry_F γ q) e path.

  Lemma entry_unfold γ q e path :
    entry γ q e path ⊣⊢ entry_F γ q (entry γ q) e path.
  Proof. apply (fixpoint_unfold (entry_F γ q)). Qed.

  #[global] Instance entry_persistent γ q e path : Persistent (entry γ q e path).
  Proof.
    rewrite entry_unfold /entry_F.
    apply _.
  Qed.

  Definition childP
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp)
    nodeptr (path child_path: path) : iProp Σ :=
    if (decide (nodeptr = null)) then
      own_path γ.(map_name) q path empty_map_fn
    else
      (∃ (is_entry: bool),
          nodeptr ↦s[hashtriemap.node :: "isEntry"]□ is_entry ∗
          if is_entry then
            ∃ ent,
              ⌜ent ≠ null⌝ ∗
              nodeptr ↦s[hashtriemap.node :: "ent"]□ ent ∗
              nodeptr ↦s[hashtriemap.node :: "ind"]□ null ∗
              entry γ q ent path
          else
            ∃ ind,
              ⌜length child_path < 16⌝ ∗
              nodeptr ↦s[hashtriemap.node :: "ent"]□ null ∗
              nodeptr ↦s[hashtriemap.node :: "ind"]□ ind ∗
              ▷ child_indirect ind child_path)%I.

  Definition childrenP
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp) (children_slice: slice.t)
    (children_vals: list atomic.Value.t)
    (ind: loc) (path: path) : iProp Σ :=
    "Hchildren" :: [∗ list] i ↦ val ∈ children_vals,
      let child_path := path ++ [Z.of_nat i] in
      ∃ (nodeptr: loc),
        "Hown_child" :: own_Value (slice.elem_ref_f children_slice atomic.Value i) (DfracOwn q)
          (interface.mk (ptrT.id hashtriemap.node.id) #nodeptr) ∗
        "Hchild" :: childP child_indirect γ q nodeptr path child_path.

  (* split 50/50 between an invariant and the mutex to allow for lock-free reads *)
  (* we always have read permission on any indirect, but only can write if we acquire the lock *)
  (* the only things ever modified are atomic values (atomic pointers), everything else is □ ownership *)
  Definition indirect_F
    (γ: ghost_names)
    (indirect: loc -d> (list Z) -d> iProp Σ)
    : loc -d> (list Z) -d> iProp Σ :=
    λ ind path,
      (∃ (children_vals: list atomic.Value.t) children_slice,
          "#Hown_children" :: ind ↦s[hashtriemap.indirect :: "children"]□ children_slice ∗
          "#Hchildren_slice" :: children_slice ↦*□ children_vals ∗
          "%Hchildren_len" :: ⌜length children_vals = 16%nat⌝ ∗
          (* "#Hmutex" :: ind ↦s[hashtriemap.indirect :: "mu"]□ mutex ∗ *)
          "#Hind_inv" :: inv (indN) ((childrenP indirect γ (1/2) children_slice children_vals ind path)) ∗
          "#Hind_mutex" :: is_Mutex (struct.field_ref_f hashtriemap.indirect "mu" ind) (
              ∃ (dead: bool),
                "Hdead" ∷ own_Bool (struct.field_ref_f hashtriemap.indirect "dead" ind) (DfracOwn 1) dead ∗
                "Hmu_inv" ∷ ((* ⌜¬ dead⌝ -∗  *)childrenP indirect γ (1/2) children_slice children_vals ind path)))%I.

  (* Prove contractiveness *)
  Global Instance indirect_F_contractive γ : Contractive (indirect_F γ).
  Proof.
    rewrite /indirect_F.
    intros n f g Hfg ind path.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    have H : ((childrenP f γ (1 / 2) a0 a ind path) ≡{n}≡ (childrenP g γ (1 / 2) a0 a ind path)).
    { unfold childrenP. repeat f_equiv. unfold childP. solve_contractive. }
    repeat f_equiv; exact H.
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

  (* Abstract map state seen by clients. *)
  Definition own_ht_map (γ: ghost_names) (m: gmap K V) : iProp Σ :=
    ghost_var γ.(user_name) (DfracOwn (1/2)) m.

  Definition map_state (γ: ghost_names) (user_map: gmap K V) (hm: hash_map) : iProp Σ :=
    "Hauth_map" :: map_ctx γ.(map_name) 1 hm ∗
    "Huser_map" :: ghost_var γ.(user_name) (DfracOwn (1/2)) user_map ∗
    "%Hflat" :: ⌜user_map = flatten hm⌝ ∗
    (* bucket correctness - if a key exists, then its in the correct bucket *)
    "%Hbuckets" :: (⌜∀ h sub k, hm !! h = Some sub →
                               uint.Z (hash_key k) = h →
                               flatten hm !! k = sub !! k⌝) ∗
    "%Hbuckets_rev" ∷ (⌜∀ h sub k v,
                         hm !! h = Some sub →
                         sub !! k = Some v →
                         uint.Z (hash_key k) = h⌝).

  Definition own_root
    (γ: ghost_names) (ht: loc) (rooti: loc) : iProp Σ :=
    "Hown_root" ∷ (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) ↦ᵥ
      (interface.mk (ptrT.id hashtriemap.indirect.id) #rooti) ∗
    "#Hroot_indirect" ∷ indirect γ rooti [].

  Definition ht_inv
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    inv mapN (
        "Hroot" ∷ (∃ root, "Hroot" ∷ own_root γ ht root) ∗
        "Hmap" ∷ (∃ user_map hm, "Hmap" ∷ map_state γ user_map hm)
      ).

  (* Public predicate exposed to clients. *)
  Definition is_hashtriemap
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    ("#Hseed" :: ∃ (seed: w64), ht ↦s[hashtriemap.HashTrieMap :: "seed"]□ seed) ∗
    "#His_map" :: ht_inv γ ht.

  Definition ht_au_mask : coPset :=
    ⊤ ∖ ↑mapN ∖ ↑indN ∖ ↑entryN.

  (* Helper for Load return values. *)
  Definition ht_load_ret (m: gmap K V) (key: K) : val :=
    (match m !! key with
    | Some v => (#v, #true)
    | None => (#(default_val V), #false)
    end)%V.

  (* designed to be split between an invariant and a mutex, so that reading can be done outside of the critical section and writing can only be done inside *)
  Definition init_tok `{!ghost_varG Σ bool} (γ: ghost_names) (b: bool) : iProp Σ :=
    ghost_var γ.(init_name) (DfracOwn (1/2)) b.

  Definition init_status_done
    (γ: ghost_names) (ht: loc) (b: bool) : iProp Σ :=
    (if b then is_hashtriemap γ ht else True%I).

  Definition init_status_inv
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      own_Uint32 (struct.field_ref_f hashtriemap.HashTrieMap "inited" ht) 1
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
                ht ↦s[hashtriemap.HashTrieMap :: "seed"] seed) ∗
            own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) 1 interface.nil
           )%I.

  Definition init_mu `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    is_Mutex (struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht)
      (init_mu_inv ht γ).

  Definition hashtriemap_init
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    "#Hinit" :: init_status ht γ ∗
    "#Hinit_mu" :: init_mu ht γ.

  Lemma hashtriemap_pre_auth_init
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool} :
    ⊢ |==> ∃ γ,
      init_tok γ false ∗ init_tok γ false.
  Proof.
    iMod (ghost_var_alloc (false)) as (init_γ) "[Hinit1 Hinit2]".
    iMod (ghost_var_alloc (∅ : gmap K V)) as (map_γ) "Hmap".
    iMod (ghost_var_alloc (∅ : gmap K V)) as (user_γ) "[Huser1 Huser2]".
    iModIntro.
    iExists (mkNames map_γ init_γ user_γ).
    iFrame.
  Qed.

  Lemma hashtriemap_zero_init
    `{!mapG Σ Z (gmap K V), !mapG Σ K V, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
    (ht: loc) E (P: gmap w64 w64 → iProp Σ) :
    ht ↦ default_val hashtriemap.HashTrieMap.t ={E}=∗
    ∃ γ, hashtriemap_init ht γ.
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
    simpl.
    iDestruct (Value_unfold with "Hv") as "Hroot".

    iMod (inv_alloc init_statusN _ (init_status_inv ht γ) with "[Htok1 Hinited]") as "#Hinit".
    {
      iNext.
      iExists false.
      iFrame.
      done.
    }
    set (m := struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht).

    iMod (init_Mutex (init_mu_inv ht γ) E m with "HinitMu [Htok2 Hseed Hroot]") as "Hmutex".
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

  Lemma own_path_lookup h path γ q f :
    h ∈ path_to_domain path →
    own_path γ q path f -∗
    ptsto_mut γ h q (f h) ∗ (ptsto_mut γ h q (f h) -∗ own_path γ q path f).
  Proof.
    iIntros (Hdom) "Hpath".
    Local Transparent own_path.
    Local Transparent own_domain.
    unfold own_path, own_domain.
    iDestruct (big_sepL_elem_of_acc with "Hpath") as "[Hptsto Hclose]"; [exact Hdom|].
    iSplitL "Hptsto".
    - iExact "Hptsto".
    - iIntros "Hptsto".
      iApply "Hclose".
      iExact "Hptsto".
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

  Lemma own_path_update_key key value γ hm path f :
    let h  := uint.Z (hash_key key) in
    let f' := (λ h', if decide (h' = h) then <[key:=value]>(f h) else f h') in
    let hm' := <[h := f' h]> hm in
    belongs_to_path path h →
    "Hctx" ∷ map_ctx γ.(map_name) 1 hm -∗
    "Hpath" ∷ own_path γ.(map_name) 1 path f ==∗
    "Hctx" ∷ map_ctx γ.(map_name) 1 hm' ∗
    "Hpath" ∷ own_path γ.(map_name) 1 path f'.
  Proof.
    intros ? ? ? Hbelongs.
    iIntros "? ?".
    iNamed.
    rewrite /named.
    subst hm'.
    have Hdom : h ∈ path_to_domain path
                  by apply (path_to_domain_elem _ _);
      [apply full_domain_elem|exact Hbelongs].
    unfold own_path, own_domain.
    set (dom := path_to_domain path) in *.
    have Hnodup : NoDup dom by apply dom_no_dup.
    iInduction dom as [|h' dom] "IH".
    { rewrite elem_of_nil in Hdom. done. }
    apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    simpl.
    iDestruct "Hpath" as "[Hh Hpath]".
    rewrite elem_of_cons in Hdom.
    destruct Hdom as [Heq | Hdom].
    - subst h'.
      (* h not in domain, so cant use IH *)
      iClear "IH".
      iMod (map_update h (f h) (f' h) with "Hctx Hh") as "[Hctx Hh]".
      iModIntro.
      iFrame "Hctx".
      iFrame.
      subst f'.
      simpl.
      iApply (big_sepL_mono with "Hpath").
      iIntros (i y Hy) "Hy".
      rewrite decide_False; [iFrame|].
      intro Heq.
      subst.
      apply Hnotin.
      apply (list_elem_of_lookup_2 _ _ _ Hy).
    - iSpecialize ("IH" $! Hdom Hnodup with "Hctx Hpath").
      iMod "IH".
      iModIntro.
      iDestruct "IH" as "(Hctx & Hpath)".
      iFrame "Hctx".
      iFrame.
      subst f'.
      simpl.
      have Hneq : h' ≠ h by intros Heq; subst h'; exact (Hnotin Hdom).
      rewrite (decide_False _ _ Hneq).
      iFrame.
  Qed.

  Lemma hm_lookup {h path γ m hm fn q} :
    h ∈ path_to_domain path →
    map_state γ m hm -∗
    own_path γ.(map_name) q path fn -∗
    ⌜hm !! h = Some (fn h)⌝.
  Proof.
    iIntros (Hdom) "Hmap_state Hown_path".
    iNamed "Hmap_state".
    iDestruct (own_path_lookup h _ _ _ _ Hdom with "Hown_path") as "[Hptsto Hptsto_close]".
    iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
    done.
  Qed.

  Lemma user_map_lookup {h path γ m hm fn q k} :
    h ∈ path_to_domain path →
    h = uint.Z (hash_key k) →
    map_state γ m hm -∗
    own_path γ.(map_name) q path fn -∗
    ⌜m !! k = (fn h) !! k⌝.
  Proof.
    iIntros (Hdom Hh) "Hmap_state Hown_path".
    iDestruct (hm_lookup Hdom with "Hmap_state Hown_path") as %Hhm.
    iNamed "Hmap_state".
    rewrite Hflat.
    iPureIntro.
    apply (Hbuckets h (fn h) k); auto.
  Qed.

  Lemma map_state_agree {γ m m2 hm} :
    map_state γ m hm -∗ own_ht_map γ m2 -∗ ⌜m = m2⌝.
  Proof.
    iIntros "Hmap_state Huser_map2".
    iNamed "Hmap_state".
    iDestruct (ghost_var_agree with "Huser_map Huser_map2") as %Hx.
    done.
  Qed.

  Lemma map_state_update {γ path hm user_map user_map2 f} key value :
    let h  := uint.Z (hash_key key) in
    let f' := (λ h', if decide (h' = h) then <[key:=value]>(f h) else f h') in
    let um' := <[key:=value]> user_map in
    let hm' := <[h := (<[key:=value]>) (f h)]> hm in
    belongs_to_path path h →
    "Hmap" ∷ map_state γ user_map hm ∗
    "Huser_map2" ∷ own_ht_map γ user_map2 ∗
    "Hpath" ∷ own_path γ.(map_name) 1 path f ==∗
    "Hmap" ∷ map_state γ um' hm' ∗
    "Huser_map2" ∷ own_ht_map γ um' ∗
    "Hpath" ∷ own_path γ.(map_name) 1 path f'.
  Proof.
    intros.
    rename H into Hbelongs.
    iIntros "Hx".
    iNamed "Hx".
    iNamed "Hmap".

    have Hdom : h ∈ path_to_domain path by apply (in_domain _ (hash_key key)).
    iDestruct (own_path_lookup h _ _ _ _ Hdom with "Hpath") as "[Hptsto Hptsto_close]".
    iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
    iDestruct ("Hptsto_close" with "Hptsto") as "Hpath".

    iMod (ghost_var_update_halves (<[key:=value]> user_map) with "Huser_map Huser_map2") as "[Huser_map Huser_map2]".
    iMod (own_path_update_key key value _ _ _ _ Hbelongs with "Hauth_map Hpath") as "(Hauth_map & Hpath)".
    subst h.
    set (h := uint.Z (hash_key key)) in *.
    iNamed.

    iEval (rewrite decide_True) in "Hctx".
    set (old := f h) in *.

    (* have Hhm' : hm' = (<[h := <[key:=value]> old]> hm). *)
    (* { *)
    (*   apply map_eq; intro h'. *)
    (*   destruct (decide (h' = h)) as [->|Hneq]. *)
    (*   - rewrite lookup_insert. rewrite decide_True; [|reflexivity]. *)
    (*     rewrite lookup_insert. rewrite decide_True; [|reflexivity]. *)
    (*     subst f'. *)
    (*     simpl. *)
    (*     rewrite decide_True; [|reflexivity]. *)
    (*     reflexivity. *)
    (*   - rewrite lookup_insert_ne; [|done]. *)
    (*     rewrite lookup_insert_ne; [|done]. *)
    (*     reflexivity. *)
    (* } *)

    (* iEval (rewrite -Hhm') in "Hctx". *)
    iFrame.

    iPureIntro.

    (* clear Hhm'. *)

    assert (Hum' : (um' = flatten hm')).
    {
      subst f'.
      subst um' hm'.
      symmetry.
      subst user_map.
      (* rewrite decide_True; [|reflexivity]. *)
      apply (flatten_update_update hm h key value old).
      - exact Hlookup.
      - reflexivity.
      - intros.
        eapply Hbuckets_rev.
        + exact H.
        + exact H0.
    }

    split; [exact Hum'|].
    split.
    {
      intros h0 sub k Hhm' Hhash.
      rewrite -Hum'.
      subst um' hm'.
      subst f'.
      destruct (decide (h0 = h)) as [->|Hneq].
      - rewrite lookup_insert in Hhm'.
        rewrite decide_True in Hhm'; [|reflexivity].
        (* rewrite decide_True in Hhm'; [|reflexivity]. *)
        inversion Hhm'; subst sub; clear Hhm'.
        destruct (decide (k = key)) as [->|Hk].
        + rewrite lookup_insert. rewrite lookup_insert.
          rewrite decide_True; [|reflexivity].
          rewrite decide_True; [|reflexivity].
          done.
        + rewrite lookup_insert_ne; [|done].
          have Hnone_k : user_map !! k = old !! k.
          {
            rewrite Hflat.
            apply (Hbuckets h); auto.
          }
          rewrite Hnone_k.
          rewrite lookup_insert_ne; [|done].
          done.
      - rewrite lookup_insert_ne in Hhm'; [|done].
        destruct (decide (k = key)) as [->|Hk].
        + exfalso. apply Hneq.
          subst h. rewrite Hhash.
          done.
        + rewrite lookup_insert_ne; [|done].
          rewrite Hflat.
          eapply Hbuckets; eauto.
    }
    {
      subst f'.
      subst hm'.
      simpl in *.
      (* rewrite decide_True in Hum'; [|reflexivity]. *)
      (* rewrite decide_True; [|reflexivity]. *)
      intros.
      destruct (decide (h0 = h)) as [->|Hneq].
      - rewrite lookup_insert in H.
        rewrite decide_True in H; [|done].
        inversion H; subst sub; clear H.
        destruct (decide (k = key)) as [->|Hk].
        + done.
        + rewrite lookup_insert_ne in H0; [|done].
          apply (Hbuckets_rev h old k v); auto.
      - rewrite lookup_insert_ne in H; [|done].
        eapply Hbuckets_rev; eauto.
    }
  Qed.

End model.
