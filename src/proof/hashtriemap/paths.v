From Perennial Require Import base.
From Perennial.Helpers Require Import Automation Integers.
From stdpp Require Import prelude gmap list fin_maps.

From stdpp Require Import ssreflect.

(* From Stdlib Require Import ZArith List. *)

Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.
Lemma z_eq (x : Z) : 0 ≤ x → Z.of_nat (Z.to_nat x) = x.
Proof. word. Qed.

Section model.
  Definition nibble : Type := Z.
  Definition nibble_list : list nibble :=
    seqZ 0 16.
  Definition path : Type := list nibble.
  Definition domain : Type := list Z.
  Definition valid_path (p : path) : Prop :=
    Forall (λ n, 0 ≤ n < 16) p.

  Definition full_domain : domain :=
    seqZ 0 (2^64).

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
    filter
      (belongs_to_path p)
      (full_domain).

  #[global] Opaque full_domain.
  #[local]  Transparent full_domain.
  #[global] Opaque path_to_domain.
  #[local]  Transparent path_to_domain.

  Lemma full_domain_elem_seq (k : Z) :
    0 ≤ k < 2^64 ↔
    k ∈ full_domain.
  Proof.
    intros.
    rewrite elem_of_seqZ; lia.
  Qed.

  Lemma dom_no_dup p : NoDup (path_to_domain p).
  Proof.
    unfold path_to_domain.
    apply NoDup_filter.
    unfold full_domain.
    apply NoDup_seqZ.
  Qed.

  Lemma full_domain_elem (k : w64) :
    uint.Z k ∈ full_domain.
  Proof.
    apply elem_of_seqZ; word.
  Qed.

  Lemma in_domain {p h} (k: w64) :
    h = uint.Z k →
    belongs_to_path p h ↔ h ∈ path_to_domain p.
  Proof.
    intros.
    unfold path_to_domain.
    rewrite list_elem_of_filter.
    split.
    - intros.
      split; [exact H0|].
      apply elem_of_seqZ; word.
    - intros [Hbelong Hfull].
      exact Hbelong.
  Qed.

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

  Lemma valid_path_snoc p n :
    valid_path (p ++ [n]) ↔ valid_path p ∧ 0 ≤ n < 16.
  Proof.
    rewrite /valid_path Forall_app /=.
    split.
    - intros [Hp Hn]. inversion Hn; subst. split; [exact Hp|assumption].
    - intros [Hp Hn]. split; [exact Hp|constructor; [exact Hn|constructor]].
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
    belongs_to_path p u ↔ (lo p ≤ u < hi p).
  Proof.
    intros Hsh_nonneg Hu_nonneg.
    repeat unfold belongs_to_path, lo, hi in *.
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

  Lemma path_to_prefix_bounds p :
    valid_path p →
    0 ≤ path_to_prefix p < 2 ^ (4 * length p).
  Proof.
    induction p as [|n p IH] using rev_ind; intros Hvalid.
    - unfold path_to_prefix; simpl. split.
      + lia.
      + change (2 ^ (4 * 0)) with 1. lia.
    - rewrite valid_path_snoc in Hvalid.
      destruct Hvalid as [Hvalid Hn].
      rewrite path_to_prefix_snoc.
      destruct IH as [IHlo IHhi]; [done|].
      destruct Hn as [Hnlo Hnhi].
      replace ((path_to_prefix p) ≪ 4) with (path_to_prefix p * 2 ^ 4).
      2: {
        symmetry.
        apply Z.shiftl_mul_pow2.
        lia.
      }
      split.
      +
        lia.
      + replace (4 * length (p ++ [n])) with (4 * length p + 4)%Z by (rewrite app_length /=; lia).
        rewrite Z.pow_add_r; try lia.
  Qed.

  Lemma lo_nonneg p :
    valid_path p →
    length p ≤ 16 →
    0 ≤ lo p.
  Proof.
    intros Hvalid Hlen.
    unfold lo.
    destruct (path_to_prefix_bounds p Hvalid) as [Hlo _].
    rewrite Z.shiftl_mul_pow2.
    2: { unfold sh. lia. }
    lia.
  Qed.

  Lemma hi_eq_lo_plus_span p :
    length p ≤ 16 →
    hi p = lo p + 2 ^ sh p.
  Proof.
    intros Hlen.
    unfold hi, lo.
    rewrite Z.shiftl_mul_pow2.
    2: { unfold sh. lia. }
    rewrite Z.shiftl_mul_pow2.
    2: { unfold sh. lia. }
    ring.
  Qed.

  Lemma hi_le_full p :
    valid_path p →
    length p ≤ 16 →
    hi p ≤ 2 ^ 64.
  Proof.
    intros Hvalid Hlen.
    unfold hi.
    destruct (path_to_prefix_bounds p Hvalid) as [_ Hhi].
    replace (64) with (4 * length p + sh p)%Z by (unfold sh; lia).
    rewrite Z.mul_comm.
    unfold sh.
    rewrite Z.pow_add_r; [|lia|lia].
    rewrite Z.shiftl_mul_pow2; [|lia].
    apply Zmult_le_compat_r; [|lia].
    rewrite Z.mul_comm.
    lia.
  Qed.

  Lemma filter_nil_of_Forall_not {A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list A) :
    Forall (λ x, ¬ P x) l →
    filter P l = [].
  Proof.
    intros Hall. induction Hall as [|x l Hnot Hall IH]; simpl.
    - done.
    - rewrite filter_cons_False; [done|exact Hnot].
  Qed.

  Lemma filter_id_of_Forall {A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list A) :
    Forall P l →
    filter P l = l.
  Proof.
    intros Hall. induction Hall as [|x l Hpx Hall IH]; simpl.
    - done.
    - rewrite filter_cons_True; [by f_equal|exact Hpx].
  Qed.

  Lemma domain_to_seq p :
    valid_path p ->
    length p ≤ 16 ->
    path_to_domain p = seqZ (lo p) (2 ^ sh p).
  Proof.
    intros Hvalid Hlen.
    unfold path_to_domain.
    unfold full_domain.
    replace (2 ^ 64) with (lo p + (2 ^ 64 - lo p)) by lia.
    rewrite (seqZ_app 0 (lo p) (2 ^ 64 - lo p)).
    2: { apply lo_nonneg; assumption. }
    2: {
      pose proof (hi_eq_lo_plus_span p Hlen).
      pose proof (hi_le_full p Hvalid Hlen).
      assert (0 ≤ 2 ^ sh p) by (apply Z.pow_nonneg; unfold sh; lia).
      lia.
    }
    replace (2 ^ 64 - lo p) with (2 ^ sh p + (2 ^ 64 - hi p)).
    2: {
      rewrite (hi_eq_lo_plus_span p Hlen).
      lia.
    }
    rewrite (seqZ_app (lo p) (2 ^ sh p) (2 ^ 64 - hi p)).
    2: { unfold sh. lia. }
    2: {
      pose proof (hi_le_full p Hvalid Hlen).
      lia.
    }
    rewrite !filter_app.
    rewrite (filter_nil_of_Forall_not (belongs_to_path p) (seqZ 0 (lo p))).
    2: {
      rewrite Forall_forall.
      intros x Hx Hbel.
      apply shiftr_eq_iff_interval in Hbel; unfold sh; [|lia|].
      2: { rewrite elem_of_seqZ in Hx. lia. }
      rewrite elem_of_seqZ in Hx.
      lia.
    }
    rewrite app_nil_l.
    rewrite (filter_id_of_Forall (belongs_to_path p) (seqZ (lo p) (2 ^ sh p))).
    2: {
      rewrite Forall_forall.
      intros x Hx.
      pose proof (lo_nonneg p Hvalid Hlen) as Hlo_nonneg.
      rewrite elem_of_seqZ in Hx.
      apply shiftr_eq_iff_interval; unfold sh; [lia|lia|].
      rewrite (hi_eq_lo_plus_span p Hlen).
      lia.
    }
    rewrite -hi_eq_lo_plus_span; [|lia].
    rewrite (filter_nil_of_Forall_not (belongs_to_path p) (seqZ (hi p) (2 ^ 64 - hi p))).
    2: {
      rewrite Forall_forall.
      intros x Hx Hbel.
      pose proof (lo_nonneg p Hvalid Hlen) as Hlo_nonneg.
      pose proof (hi_eq_lo_plus_span p Hlen) as Hhi_eq.
      assert (0 ≤ hi p) by (assert (0 ≤ 2 ^ sh p) by (apply Z.pow_nonneg; unfold sh; lia); lia).
      rewrite elem_of_seqZ in Hx.
      apply shiftr_eq_iff_interval in Hbel; unfold sh; lia.
    }
    rewrite app_nil_r.
    reflexivity.
  Qed.

  #[global] Opaque full_domain.

  Lemma path_to_domain_lookup p k :
    valid_path p →
    length p ≤ 16 →
    k ∈ path_to_domain p →
    (path_to_domain p) !! (Z.to_nat (k - lo p)) = Some k.
  Proof.
    intros Hvalid Hlen Hk.
    rewrite (domain_to_seq p Hvalid Hlen).
    apply lookup_seqZ.
    pose proof (path_to_prefix_bounds p Hvalid) as [Hlo Hhi].
    unfold path_to_domain in *.
    rewrite list_elem_of_filter in Hk.
    destruct Hk as [Hbelong Hfull].
    rewrite -full_domain_elem_seq in Hfull.
    rewrite shiftr_eq_iff_interval in Hbelong; [|unfold sh; lia|lia].
    rewrite z_eq; [|lia].
    split; [lia|].
    destruct Hbelong as [Hlo' Hhi'].
    rewrite Z.lt_sub_lt_add_r.
    rewrite Z.add_comm.
    rewrite -hi_eq_lo_plus_span; lia.
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
    unfold lo, hi in *.
    set (s := sh p) in *.
    set (pp := path_to_prefix p) in *.
    have Hinterval : pp ≪ s ≤ k < (pp + 1) ≪ s.
    {
      apply shiftr_eq_iff_interval in Hbelong; unfold sh; [|lia|lia].
      unfold lo, hi in Hbelong.
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
      unfold belongs_to_path in *.
      assert (Hxdiv : x / 16 = pp).
      {
        subst x.
        rewrite Z.shiftr_div_pow2; [|lia].
        rewrite Z.shiftr_div_pow2 in Hbelong; [|lia].
        rewrite Z.pow_sub_r; try word.
        subst s.
        set (s := sh p) in *.
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
        subst x s pp.
        exact Hbelong.
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

    Lemma list_elem_split_nodup {A} `{EqDecision A} (l : list A) (x : A) :
    NoDup l ->
    x ∈ l ->
    ∃ l1 l2,
      l = l1 ++ [x] ++ l2 ∧
      x ∉ l1 ∧
      x ∉ l2.
  Proof.
    intros Hnodup Hel.
    induction Hnodup as [|y l Hy_notin Hnodup IH].
    - inversion Hel.
    - simpl in Hel.
      apply elem_of_cons in Hel.
      destruct Hel as [->|Hel].
      + exists [], l. simpl. repeat split; auto. apply not_elem_of_nil.
      + destruct (IH Hel) as (l1 & l2 & -> & Hnot1 & Hnot2).
        specialize (IH Hel).
        destruct IH as (l3 & l4 & H).
        exists (y :: l1), l2.
        repeat split; simpl; auto.
        rewrite not_elem_of_cons.
        split.
        * intros ?; subst; exact (Hy_notin Hel).
        * exact Hnot1.
  Qed.

  Lemma path_to_domain_split p h :
    h ∈ path_to_domain p ->
    ∃ l1 l2,
      path_to_domain p = l1 ++ [h] ++ l2 ∧
      h ∉ l1 ∧
      h ∉ l2.
  Proof.
    intros Hin.
    eapply list_elem_split_nodup.
    - apply dom_no_dup.
    - exact Hin.
  Qed.

  Lemma path_to_domain_split_exact p h :
    valid_path p ->
    length p <= 16 ->
    h ∈ path_to_domain p ->
    path_to_domain p =
    seqZ (lo p) (h - lo p) ++ [h] ++ seqZ (h + 1) (hi p - h - 1).
  Proof.
    intros Hvalid Hlen Hbelong.
    pose proof (domain_to_seq p Hvalid Hlen) as Hseq.
    rewrite Hseq in Hbelong.
    apply elem_of_seqZ in Hbelong.
    rewrite Hseq.
    rewrite hi_eq_lo_plus_span; [|lia].
    set (x := h - lo p).
    set (s := 2 ^ sh p).
    set (l := lo p).
    replace (l + s - h - 1) with (s - x - 1) by lia.
    replace (s) with (x + (s - x)) at 1 by lia.
    rewrite seqZ_app; [|lia|lia].
    replace (l + x) with h by lia.
    rewrite (seqZ_cons h (s - x)); [|lia].
    auto.
  Qed.

End model.
