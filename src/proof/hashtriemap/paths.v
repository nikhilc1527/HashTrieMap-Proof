From Perennial Require Import base.
From Perennial.Helpers Require Import Automation Integers.
From Stdlib Require Import ZArith.
From stdpp Require Import prelude gmap list fin_maps.

From stdpp Require Import ssreflect.

Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.

Section model.

  Definition nibble : Type := Z.
  Definition nibble_list : list nibble :=
    seqZ 0 16.
  Definition path : Type := list nibble.
  Definition domain : Type := list Z.

  Definition full_domain : domain :=
    seqZ 0 (2^64).

  (* otherwise typeclass checking tries to expand it *)
  #[global] Opaque full_domain.

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

  (* (* TODO: replace all the 4's with hashtriemap.nChildrenLog2, 16 with hashtriemap.nChildren *) *)


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
    rewrite Z.shiftr_div_pow2; try word.
    rewrite Z.shiftl_mul_pow2; try word.
    rewrite Z.shiftl_mul_pow2; try word.
    set (b := 2 ^ s).
    have Hbne : b > 0.
    { unfold b. word. }

    split.
    - intro H.
      rewrite (Z.div_mod u b); [|lia].
      rewrite H.
      split; [word|].
      have Hmod : 0 <= u mod b < b by apply Z.mod_pos_bound; lia.
      lia.
    - intros [Hlo Hhi].
      symmetry.
      apply (Z.div_unique u b pp (u - pp*b)); [lia|].
      have : 0 <= u - pp*b < b by lia.
      lia.
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
      rewrite -Z.pow_add_r; [|word|word].
      replace (4 + (sh p - 4)) with (sh p) by lia.
      reflexivity.
    }
    lia.
  Qed.

  Lemma interval_consecutive (p : path) (n : Z) :
    4 ≤ sh p ->
    hi (p ++ [n]) = lo (p ++ [n+1]).
  Proof.
    intros Hsh_nonneg.
    repeat unfold hi, lo in *.
    repeat rewrite path_to_prefix_snoc.
    repeat rewrite sh_snoc.
    replace (path_to_prefix p ≪ 4 + n + 1) with (path_to_prefix p ≪ 4 + (n + 1)) by lia.
    reflexivity.
  Qed.

  Lemma full_domain_elem (k : w64) :
    uint.Z k ∈ full_domain.
  Proof.
    #[local] Transparent full_domain.
    apply elem_of_seqZ; word.
  Qed.

  Lemma path_to_domain_elem (p : path) (k : Z) :
    k ∈ full_domain →
    k ∈ path_to_domain p ↔ belongs_to_path p k.
  Proof.
    intro Hk.
    unfold path_to_domain, belongs_to_path.
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
      apply shiftr_eq_iff_interval; [|lia|word].
      unfold sh.
      word.
    }
    set (n := Z.land (k ≫ (s - 4)) (Z.ones 4)).
    exists n.
    split.
    - (* show 0 ≤ n < 16 *)
      unfold n.
      set (x := k ≫ (s - 4)).
      replace (Z.land x (Z.ones 4)) with (x mod 2^4); last first.
      { rewrite Z.land_ones; lia. }
      apply Z.mod_pos_bound.
      lia.
    - (* show belongs_to_path (p ++ [n]) k *)
      unfold belongs_to_path.
      have Hs : 4 ≤ sh p.
      {
        unfold sh.
        lia.
      }
      replace (sh (p ++ [n])) with (s - 4) by (rewrite sh_snoc; lia).
      rewrite path_to_prefix_snoc.
      set (x := k ≫ (s-4)).
      assert (Hxmod : x mod 16 = n).
      {
        subst x n. change 16 with (2^4).
        rewrite Z.land_ones; lia.
      }
      assert (Hxdiv : x / 16 = pp).
      {
        subst x.
        rewrite Z.shiftr_div_pow2; [|lia].
        rewrite Z.shiftr_div_pow2 in Hbelong; [|lia].
        rewrite Z.pow_sub_r; try word.
        rewrite -Hbelong.
        change (2^4) with 16.
        set (x := 2^s).
        have Hxge16 : (16 ≤ x).
        {
          unfold x, s.
          change (16 ≤ 2 ^ sh p) with (2 ^ 4 ≤ 2 ^ (sh p)).
          apply Z.pow_le_mono_r; lia.
        }
        rewrite Z.div_div; [|word|lia].
        have Hx : x mod 16 = 0.
        {
          unfold x.
          have Ht : s mod 4 = 0 by (unfold s, sh; word).
          have Hdiv : Z.divide 4 s.
          { apply Z.mod_divide; lia. }
          destruct Hdiv as [y Hy].
          replace (y * 4) with (4 * y) in Hy by lia.
          rewrite Hy.
          rewrite Z.pow_mul_r; [|lia|lia].
          change (2^4) with 16.
          have Hypos : 1 ≤ y by lia.
          have Hdiv : Z.divide 16 (16 ^ y).
          {
            exists (16 ^ (y - 1)).
            replace (16 ^ (y - 1) * 16) with (16 * 16 ^ (y - 1)) by lia.
            rewrite Z.pow_pred_r; lia.
          }
          rewrite Z.mod_divide; [|lia].
          exact Hdiv.
        }
        replace (x / 16 * 16) with (x) by word.
        reflexivity.
      }
      have Hx : x = pp * 16 + n.
      {
        rewrite (Z.div_mod x 16); lia.
      }
      change 16 with (2^4) in Hx.
      rewrite -Z.shiftl_mul_pow2 in Hx; [|lia].
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
    lia.
  Qed.

  Lemma next_nibble_extend
    (p: path) (k: Z) (n: Z) :
    0 ≤ k →
    length p < 16 →
    belongs_to_path p k →
    n = Z.land (k ≫ (sh p - 4)) 15 →
    belongs_to_path (p ++ [n]) k.
  Proof.
    intros Hk Hlen Hbelong Hn.
    unfold belongs_to_path.
    rewrite sh_snoc.
    rewrite path_to_prefix_snoc.
    set x := k ≫ (sh p - 4).
    have Hx : x = (x / 16) * 16 + (x mod 16).
    { rewrite (Z.div_mod x 16); [word|lia]. }

    have Hdiv : x ≫ 4 = path_to_prefix p.
    {
      unfold x.
      replace ((k ≫ (sh p - 4)) ≫ 4) with (k ≫ sh p).
      - exact Hbelong.
      - symmetry.
        rewrite Z.shiftr_shiftr; [|lia].
        replace (sh p - 4 + 4) with (sh p) by lia.
        reflexivity.
    }
    have Hmod : x mod 16 = n.
    {
      subst n.
      change 15 with (Z.ones 4).
      symmetry.
      rewrite Z.land_ones; [|lia].
      reflexivity.
    }

    rewrite Hx.
    rewrite Hmod.
    have Hdiv' : x `div` 16 = path_to_prefix p.
    {
      change 16 with (2^4).
      rewrite <- Z.shiftr_div_pow2; [|lia].
      rewrite Hdiv.
      reflexivity.
    }
    rewrite Hdiv'.
    rewrite Z.shiftl_mul_pow2; [|lia].
    lia.
  Qed.

  (* Lemma path_to_domain_split (p : path) : *)
  (*   length p < 16 ->            (* length p < (sizeof hashT) / nChildrenLog2 *) *)
  (*   path_to_domain p = *)
  (*   concat (map (λ n, path_to_domain (p ++ [n])) nibble_list). *)
  (* Proof. *)
  (*   intro Hlen. *)
  (*   apply list_eq. intros. *)
  (*   apply option_eq; intro k. *)
  (*   split; intro H. *)
  (*   - (* → *) *)
  (*     apply list_elem_of_lookup_2 in H. *)
  (*     rewrite list_elem_of_filter in H. *)
  (*     destruct H as [Hbelong Hfull]. *)
  (*     (* Hfull: k ∈ full_domain *) *)
  (*     rewrite elem_of_seqZ in Hfull. *)
  (*     have Hk_nonneg : 0 ≤ k := proj1 Hfull. *)
  (*     destruct (next_nibble_exists p k) as [x [Hnrange Hbelongn]]; *)
  (*       try done. *)
  (*     set (l := concat (map (λ n : nibble, path_to_domain (p ++ [n])) nibble_list)). *)
  (* Admitted. *)

End model.
