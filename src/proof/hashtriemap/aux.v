(* Things that should be in perennial but arent supported yet *)

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
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap list fin_maps.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.

From Perennial.goose_lang.lib Require Export atomic.impl.

Section aux.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
    `{!globalsGS Σ} {go_ctx: GoContext}.

  Parameter atomic_value_model : atomic.Value.t → option loc → Prop.
  Parameter own_Value : loc -> dfrac -> option val -> iProp Σ.

  (* Using in place of perennial's, since perennial doesnt have std library proofs for atomic Values yet *)
  Lemma wp_Value__Store (u: loc) (v: val) (Φ : val → iProp Σ) :
    is_pkg_init atomic -∗
                          (|={⊤,∅}=> ▷ ∃ old : option val,
                                         own_Value u (DfracOwn 1) old ∗
                                           (own_Value u (DfracOwn 1) (Some v) ={∅,⊤}=∗ Φ (# ())))
    -∗ WP # (method_callv (ptrT.id atomic.Value.id) "Store" (# u)) (v)
       {{ vret, Φ vret }}.
  Proof. Admitted.

  #[global] Instance LoadUint32_Atomic (l:loc) : Atomic StronglyAtomic (atomic.LoadUint32 #l).
  Proof. apply _. Qed.
  
End aux.
