/-
# Size of `D_n` at the small primes and at `p = 2` (PROOF_BETA §4, "Size", instance I3)

With `n = 480(m+1)`, `𝒩 = 3040(m+1)+3`, `Λ_p = ⌊log_p 𝒩⌋`,
`G = 179/10`, `Z = 10n + 6`:

* `Esmall_sub_le`: for odd `p` with `p² ≤ 𝒩`,
  `E_p - G v_p(n!) ≤ 29/(p-1) + 131 (Λ_p + 1)`, in the form
  `(p-1)(E_p - G v_p(n!)) ≤ 29 + 131 (p-1)(Λ_p+1)`;
* `small_primes_sum_le`:
  `Σ_{3 ≤ p ≤ √𝒩, p prime} (E_p - G v_p(n!)) log p ≤ 312 ⌊√𝒩⌋ log 𝒩`
  (so this part is `O(√n log n) = o(n)`);
* `E2_sub_le`: `E_2 - G v_2(n!) ≤ 2Z + 28 + 123 (⌊log_2 n⌋ + 1) = 20 n + 40 + 123(⌊log_2 n⌋+1)`.

The proof is PROOF_BETA's: each zero run is a product of consecutive odd integers (valuation
`≥ v_p` of a factorial quotient), each pole product is a product of consecutive integers (valuation
`≤` a factorial quotient), and the `n/(p-1)` terms cancel exactly because
`Σ_j m_j #block_j - Z = Gn + 29`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Arith.Ep
import BetaIrrational.Arith.Legendre
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedSectionVars false

set_option maxRecDepth 8192

namespace BetaIrr.I3.Arith

open Finset BetaIrr.Arith

/-! ### List helpers -/

lemma list_sum_map_neg {ι : Type*} (l : List ι) (f : ι → ℤ) :
    (l.map (fun b => -f b)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_bound {ι : Type*} (l : List ι) (w X Y : ι → ℤ) (c : ℤ) (hw : ∀ b ∈ l, 0 ≤ w b)
    (h : ∀ b ∈ l, c * X b ≤ Y b) :
    c * (l.map (fun b => w b * X b)).sum ≤ (l.map (fun b => w b * Y b)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
      (fun b hb => h b (List.mem_cons_of_mem a hb))
    have h3 := hw a List.mem_cons_self
    nlinarith

lemma card_blockSet (m : ℕ) (b : ℕ × ℕ) (hb : b ∈ blocks) :
    ((#(blockSet m b) : ℕ) : ℤ) = 480 * ((m : ℤ) + 1) - 6 * b.1 * ((m : ℤ) + 1) + 1 := by
  have hb1 : b.1 ≤ 46 := blocks_fst_le b hb
  unfold blockSet nOf
  rw [Nat.card_Icc]
  have h27 := Nat.mul_le_mul_right (m + 1) (show 3 * b.1 ≤ 138 by omega)
  have hX : ((3 * b.1 * (m + 1) : ℕ) : ℤ) = 3 * (b.1 : ℤ) * ((m : ℤ) + 1) := by push_cast; ring
  generalize 3 * b.1 * (m + 1) = X at h27 hX ⊢
  have key : ((480 * (m + 1) - X + 1 - X : ℕ) : ℤ) = 480 * ((m : ℤ) + 1) + 1 - 2 * (X : ℤ) := by
    omega
  rw [key, hX]
  ring

lemma blocks_weighted_card (m : ℕ) (C : ℤ) :
    (blocks.map (fun b => (b.2 : ℤ) * (((#(blockSet m b) : ℕ) : ℤ) + C))).sum
      = 13392 * ((m : ℤ) + 1) + 35 + 35 * C := by
  rw [List.map_congr_left (fun b hb => by rw [card_blockSet m b hb])]
  simp [blocks]
  ring

/-! ### Pole products -/

section Poles

variable {p : ℕ} [hp : Fact p.Prime]

/-- `(p-1) Σ_{k' ∈ [a,b], k' ≠ k} v_p(k'-k) ≤ #[a,b] + 2(p-1)(⌊log_p N⌋+1)` for `a, k ≤ N`. -/
theorem pole_sum_le {a b k N : ℕ} (ha : a ≤ N) (hk : k ≤ N) :
    ((p - 1 : ℕ) : ℤ) * ∑ k' ∈ (Icc a b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ)
      ≤ ((#(Icc a b) : ℕ) : ℤ) + 2 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p N : ℤ) + 1) := by
  rw [← sum_filter_add_sum_filter_not ((Icc a b).erase k) (fun k' => k < k')]
  have hU : ((Icc a b).erase k).filter (fun k' => k < k') = Icc (max a (k + 1)) b := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc]; omega
  have hL : ((Icc a b).erase k).filter (fun k' => ¬ k < k') = Ico a (min (b + 1) k) := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc, mem_Ico]; omega
  rw [hU, hL]
  have hU' : ∑ k' ∈ Icc (max a (k + 1)) b, (padicValInt p ((k' : ℤ) - k) : ℤ)
      = ((∑ d ∈ Icc (max a (k + 1) - k) (b - k), padicValNat p d : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun k' => k' - k) (fun d => d + k) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc] at hx; omega
    · intro x hx; simp only [mem_Icc] at hx; omega
    · intro x hx
      simp only [mem_Icc] at hx
      congr 1; unfold padicValInt; congr 1; omega
  have hL' : ∑ k' ∈ Ico a (min (b + 1) k), (padicValInt p ((k' : ℤ) - k) : ℤ)
      = ((∑ d ∈ Icc (k - min (b + 1) k + 1) (k - a), padicValNat p d : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun k' => k - k') (fun d => k - d) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, mem_Ico] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, mem_Ico] at hx ⊢; omega
    · intro x hx; simp only [mem_Ico] at hx; omega
    · intro x hx; simp only [mem_Icc] at hx; omega
    · intro x hx
      simp only [mem_Ico] at hx
      congr 1; unfold padicValInt; congr 1; omega
  rw [hU', hL', mul_add]
  have h1 := sub_one_mul_sum_Icc_le' (p := p) (A := max a (k + 1) - k) (B := b - k) (N := N)
    (by omega) (by omega)
  have h2 := sub_one_mul_sum_Icc_le' (p := p) (A := k - min (b + 1) k + 1) (B := k - a) (N := N)
    (by omega) (by omega)
  have hc : ((#(Icc (max a (k + 1) - k) (b - k)) : ℕ) : ℤ)
      + ((#(Icc (k - min (b + 1) k + 1) (k - a)) : ℕ) : ℤ) ≤ ((#(Icc a b) : ℕ) : ℤ) := by
    simp only [Nat.card_Icc]; omega
  linarith

end Poles

/-! ### Zero products -/

section Zeros

variable {p : ℕ} [hp : Fact p.Prime]

set_option maxHeartbeats 2000000 in
theorem zero_sum_ge (hp2 : p ≠ 2) (m k : ℕ) (hk : k ≤ nOf m) :
    (1600 * ((m : ℤ) + 1) + 2) - 2 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1)
      ≤ ((p - 1 : ℕ) : ℤ) * ∑ l ∈ zeroSet m, (padicValInt p (wl k l) : ℤ) := by
  have hk' : k ≤ 480 * (m + 1) := hk
  rw [← sum_filter_add_sum_filter_not (zeroSet m) (fun l => -(k : ℤ) ≤ l)]
  have hP : ∑ l ∈ (zeroSet m).filter (fun l => -(k : ℤ) ≤ l), (padicValInt p (wl k l) : ℤ)
      = ((∑ j ∈ range (k + 560 * (m + 1) + 1), padicValNat p (2 * j + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun l => (l + k).toNat) (fun j => (j : ℤ) - k) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [zeroSet, mem_filter, mem_Icc, mem_range] at hx ⊢; omega
    · intro x hx; simp only [zeroSet, mem_filter, mem_Icc, mem_range] at hx ⊢; omega
    · intro x hx; simp only [zeroSet, mem_filter, mem_Icc] at hx; omega
    · intro x hx; simp only [mem_range] at hx; omega
    · intro x hx
      simp only [zeroSet, mem_filter, mem_Icc] at hx
      congr 1; unfold padicValInt wl; congr 1; omega
  have hN : ∑ l ∈ (zeroSet m).filter (fun l => ¬ -(k : ℤ) ≤ l), (padicValInt p (wl k l) : ℤ)
      = ((∑ j ∈ range (1040 * (m + 1) + 1 - k), padicValNat p (2 * j + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun l => (-(k : ℤ) - 1 - l).toNat) (fun j => -(k : ℤ) - 1 - j)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [zeroSet, mem_filter, mem_Icc, mem_range] at hx ⊢; omega
    · intro x hx
      simp only [zeroSet, mem_filter, mem_Icc, mem_range] at hx ⊢; omega
    · intro x hx; simp only [zeroSet, mem_filter, mem_Icc] at hx; omega
    · intro x hx; simp only [mem_range] at hx; omega
    · intro x hx
      simp only [zeroSet, mem_filter, mem_Icc] at hx
      congr 1; unfold padicValInt wl; congr 1; omega
  rw [hP, hN, mul_add]
  have h1 := sub_one_mul_oddSum_ge (p := p) hp2 (k + 560 * (m + 1) + 1)
  have h2 := sub_one_mul_oddSum_ge (p := p) hp2 (1040 * (m + 1) + 1 - k)
  have hl1 : (Nat.log p (2 * (k + 560 * (m + 1) + 1)) : ℤ) ≤ Nat.log p (NN m) := by
    exact_mod_cast Nat.log_mono_right (by unfold NN; omega)
  have hl2 : (Nat.log p (2 * (1040 * (m + 1) + 1 - k)) : ℤ) ≤ Nat.log p (NN m) := by
    exact_mod_cast Nat.log_mono_right (by unfold NN; omega)
  have hp1 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by positivity
  have hA : ((k + 560 * (m + 1) + 1 : ℕ) : ℤ) + ((1040 * (m + 1) + 1 - k : ℕ) : ℤ)
      = 1600 * ((m : ℤ) + 1) + 2 := by omega
  nlinarith

end Zeros

/-! ### Small odd primes -/

section Small

variable {p : ℕ} [hp : Fact p.Prime]

theorem neg_nuSmall_le (hp2 : p ≠ 2) (m k : ℕ) (hk : k ≤ nOf m) :
    ((p - 1 : ℕ) : ℤ) * (-nuSmall m p k)
      ≤ 8592 * ((m : ℤ) + 1) + 29 + 76 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1) := by
  have hnu : nuSmall m p k = 3 * ∑ l ∈ zeroSet m, (padicValInt p (wl k l) : ℤ)
      - (blocks.map (fun b => (b.2 : ℤ) *
          ∑ k' ∈ (blockSet m b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ))).sum := by
    unfold nuSmall etot
    simp only [sum_neg_distrib, mul_neg, list_sum_map_neg, ← mul_sum]
    ring
  rw [hnu]
  have hc0 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by positivity
  have hZ := zero_sum_ge (p := p) hp2 m k hk
  have hPl := list_bound blocks (fun b => (b.2 : ℤ))
    (fun b => ∑ k' ∈ (blockSet m b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ))
    (fun b => ((#(blockSet m b) : ℕ) : ℤ)
      + 2 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1)) ((p - 1 : ℕ) : ℤ)
    (fun b _ => by positivity)
    (fun b hb => by
      have := pole_sum_le (p := p) (a := 3 * b.1 * (m + 1)) (b := nOf m - 3 * b.1 * (m + 1))
        (k := k) (N := NN m) (by
          have hb1 : b.1 ≤ 46 := blocks_fst_le b hb
          have := Nat.mul_le_mul_right (m + 1) (show 3 * b.1 ≤ 138 by omega)
          unfold NN; nlinarith) (by have := nOf_lt_NN m; omega)
      exact this)
  rw [blocks_weighted_card] at hPl
  generalize ((p - 1 : ℕ) : ℤ) = c at *
  generalize (Nat.log p (NN m) : ℤ) = Λ at *
  generalize ∑ l ∈ zeroSet m, (padicValInt p (wl k l) : ℤ) = ZS at *
  generalize (blocks.map (fun b => (b.2 : ℤ) *
          ∑ k' ∈ (blockSet m b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ))).sum = PS at *
  nlinarith

theorem Esmall_sub_le (hp2 : p ≠ 2) (m : ℕ) :
    ((p - 1 : ℕ) : ℚ) * ((Esmall m p : ℚ) - (G : ℚ) * (padicValNat p (nOf m).factorial : ℚ))
      ≤ 29 + 131 * ((p - 1 : ℕ) : ℚ) * ((Nat.log p (NN m) : ℚ) + 1) := by
  -- the sup over `k`
  have hsup : ((p - 1 : ℕ) : ℤ) * (range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nuSmall m p k)
      ≤ 8592 * ((m : ℤ) + 1) + 29 + 76 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1) := by
    obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one (fun k => -nuSmall m p k)
    rw [hkeq]
    exact neg_nuSmall_le hp2 m k (Nat.lt_succ_iff.mp (mem_range.mp hk))
  have hleg := legendre_lower (p := p) (nOf m)
  have hlogn : Nat.log p (nOf m) ≤ Nat.log p (NN m) := Nat.log_mono_right (nOf_lt_NN m).le
  have hEs : (Esmall m p : ℚ) = (((range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nuSmall m p k) : ℤ) : ℚ) + 37 * ((Nat.log p (NN m) : ℕ) : ℚ) := by
    unfold Esmall; push_cast; ring
  rw [hEs]
  have hn : nOf m = 480 * (m + 1) := rfl
  generalize padicValNat p (nOf m).factorial = V at *
  generalize (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nuSmall m p k) = S at *
  generalize Nat.log p (nOf m) = Λn at *
  generalize Nat.log p (NN m) = Λ at *
  generalize p - 1 = c at *
  rw [hn] at hleg
  have hsupQ : (c : ℚ) * (S : ℚ) ≤ 8592 * ((m : ℚ) + 1) + 29 + 76 * (c : ℚ) * ((Λ : ℚ) + 1) := by
    exact_mod_cast hsup
  have hlegQ : 480 * ((m : ℚ) + 1) - (c : ℚ) * ((Λn : ℚ) + 1) ≤ (c : ℚ) * (V : ℚ) := by
    have h := (Int.cast_le (R := ℚ)).mpr hleg
    push_cast at h
    linarith
  have hlognQ : (Λn : ℚ) ≤ (Λ : ℚ) := by exact_mod_cast hlogn
  have hc0 : (0 : ℚ) ≤ (c : ℚ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hlognQ hc0
  simp only [G]
  nlinarith

/-- Pointwise: `E_p - G v_p(n!) ≤ 156 (Λ_p + 1)` for odd `p` with `p² ≤ 𝒩`. -/
theorem Ep_sub_le_small (hp2 : p ≠ 2) (m : ℕ) (hN : p ^ 2 ≤ NN m) :
    (Ep m p : ℚ) - (G : ℚ) * (padicValNat p (nOf m).factorial : ℚ)
      ≤ 156 * ((Nat.log p (NN m) : ℚ) + 1) := by
  have hpn : ¬ nOf m < p := by
    intro h
    have h1 : nOf m * nOf m < p * p := Nat.mul_self_lt_mul_self h
    unfold nOf NN at *
    nlinarith
  have hE : Ep m p = Esmall m p := by
    simp [Ep, hp2, hpn, show ¬ NN m < p ^ 2 by omega]
  rw [hE]
  have h := Esmall_sub_le (p := p) hp2 m
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  have hc : (2 : ℚ) ≤ ((p - 1 : ℕ) : ℚ) := by
    have : 2 ≤ p - 1 := by omega
    exact_mod_cast this
  have hΛ : (0 : ℚ) ≤ (Nat.log p (NN m) : ℚ) := by positivity
  set X := (Esmall m p : ℚ) - (G : ℚ) * (padicValNat p (nOf m).factorial : ℚ)
  by_contra hcon
  push Not at hcon
  nlinarith

end Small

/-- **Size at the small odd primes.**
`Σ_{3 ≤ p ≤ √𝒩, p prime} (E_p - G v_p(n!)) log p ≤ 312 ⌊√𝒩⌋ log 𝒩`. -/
theorem small_primes_sum_le (m : ℕ) :
    ∑ p ∈ (Icc 3 (Nat.sqrt (NN m))).filter Nat.Prime,
        ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p
      ≤ 312 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m) := by
  have hNpos : (0 : ℝ) < NN m := by unfold NN; positivity
  have hterm : ∀ p ∈ (Icc 3 (Nat.sqrt (NN m))).filter Nat.Prime,
      ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p
        ≤ 312 * Real.log (NN m) := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    have hpI' := mem_Icc.mp hpI
    have : Fact p.Prime := ⟨hpP⟩
    have hp2 : p ≠ 2 := by omega
    have hpN : p ^ 2 ≤ NN m := Nat.le_sqrt'.mp hpI'.2
    have h := Ep_sub_le_small (p := p) hp2 m hpN
    have hR : ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ))
        ≤ 156 * ((Nat.log p (NN m) : ℝ) + 1) := by exact_mod_cast h
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have hpNN : p ≤ NN m := le_trans (Nat.le_self_pow (by norm_num) p) hpN
    have hlogpN : Real.log p ≤ Real.log (NN m) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hpNN)
    -- `Λ log p = log p^Λ ≤ log 𝒩`
    have hpow : p ^ Nat.log p (NN m) ≤ NN m := Nat.pow_log_le_self p (by unfold NN; omega)
    have hΛlog : (Nat.log p (NN m) : ℝ) * Real.log p ≤ Real.log (NN m) := by
      rw [← Real.log_pow]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    calc ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p
        ≤ 156 * ((Nat.log p (NN m) : ℝ) + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hR hlogp
      _ = 156 * ((Nat.log p (NN m) : ℝ) * Real.log p + Real.log p) := by ring
      _ ≤ 156 * (Real.log (NN m) + Real.log (NN m)) := by gcongr
      _ = 312 * Real.log (NN m) := by ring
  have hcard : (#((Icc 3 (Nat.sqrt (NN m))).filter Nat.Prime) : ℝ) ≤ Nat.sqrt (NN m) := by
    have h1 := card_filter_le (Icc 3 (Nat.sqrt (NN m))) Nat.Prime
    rw [Nat.card_Icc] at h1
    exact_mod_cast h1.trans (by omega)
  have hlogN : 0 ≤ Real.log (NN m) := Real.log_nonneg (by unfold NN; norm_cast; omega)
  calc _ ≤ ∑ p ∈ (Icc 3 (Nat.sqrt (NN m))).filter Nat.Prime, 312 * Real.log (NN m) :=
        sum_le_sum hterm
    _ = (#((Icc 3 (Nat.sqrt (NN m))).filter Nat.Prime) : ℝ) * (312 * Real.log (NN m)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt (NN m) : ℝ) * (312 * Real.log (NN m)) := by gcongr
    _ = 312 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m) := by ring

/-! ### `p = 2` -/

theorem neg_nu2_le (m k : ℕ) (hk : k ≤ nOf m) :
    -nu2 m k ≤ 18192 * ((m : ℤ) + 1) + 40 + 70 * ((Nat.log 2 (nOf m) : ℤ) + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnu : nu2 m k = 1 - 3 * ((#(zeroSet m) : ℕ) : ℤ)
      - (blocks.map (fun b => (b.2 : ℤ) *
          ∑ k' ∈ (blockSet m b).erase k, (padicValInt 2 ((k' : ℤ) - k) : ℤ))).sum := by
    unfold nu2 etot
    rw [sum_const, nsmul_eq_mul]
    simp only [sum_neg_distrib, mul_neg, list_sum_map_neg]
    ring
  rw [hnu]
  have hPl := list_bound blocks (fun b => (b.2 : ℤ))
    (fun b => ∑ k' ∈ (blockSet m b).erase k, (padicValInt 2 ((k' : ℤ) - k) : ℤ))
    (fun b => ((#(blockSet m b) : ℕ) : ℤ) + 2 * ((2 - 1 : ℕ) : ℤ) * ((Nat.log 2 (nOf m) : ℤ) + 1))
    ((2 - 1 : ℕ) : ℤ) (fun b _ => by positivity)
    (fun b hb => pole_sum_le (p := 2) (a := 3 * b.1 * (m + 1)) (b := nOf m - 3 * b.1 * (m + 1))
        (k := k) (N := nOf m) (by
          have hb1 : b.1 ≤ 46 := blocks_fst_le b hb
          have := Nat.mul_le_mul_right (m + 1) (show 3 * b.1 ≤ 138 by omega)
          unfold nOf; nlinarith) hk)
  rw [blocks_weighted_card] at hPl
  have hcard : ((#(zeroSet m) : ℕ) : ℤ) = 1600 * ((m : ℤ) + 1) + 2 := by
    unfold zeroSet; rw [Int.card_Icc]; omega
  rw [hcard]
  have h21 : ((2 - 1 : ℕ) : ℤ) = 1 := rfl
  rw [h21] at hPl
  generalize (Nat.log 2 (nOf m) : ℤ) = Λ at *
  generalize (blocks.map (fun b => (b.2 : ℤ) *
          ∑ k' ∈ (blockSet m b).erase k, (padicValInt 2 ((k' : ℤ) - k) : ℤ))).sum = PS at *
  linarith

/-- **Size at `p = 2`.** `E_2 - G v_2(n!) ≤ 2Z + 28 + 123(⌊log_2 n⌋ + 1)` with `2Z = 20n + 12`. -/
theorem E2_sub_le (m : ℕ) :
    (E2 m : ℚ) - (G : ℚ) * (padicValNat 2 (nOf m).factorial : ℚ)
      ≤ 20 * (nOf m : ℚ) + 40 + 123 * ((Nat.log 2 (nOf m) : ℚ) + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nu2 m k)
      ≤ 18192 * ((m : ℤ) + 1) + 40 + 70 * ((Nat.log 2 (nOf m) : ℤ) + 1) := by
    obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one (fun k => -nu2 m k)
    rw [hkeq]
    exact neg_nu2_le m k (Nat.lt_succ_iff.mp (mem_range.mp hk))
  have hleg := legendre_lower (p := 2) (nOf m)
  have hE : (E2 m : ℚ) = (((range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nu2 m k) : ℤ) : ℚ) + 35 * ((Nat.log 2 (nOf m) : ℕ) : ℚ) := by
    unfold E2; push_cast; ring
  rw [hE]
  have hn : nOf m = 480 * (m + 1) := rfl
  have h21 : ((2 - 1 : ℕ) : ℤ) = 1 := rfl
  rw [h21] at hleg
  generalize padicValNat 2 (nOf m).factorial = V at *
  generalize (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nu2 m k) = S at *
  generalize Nat.log 2 (nOf m) = Λ at *
  rw [hn] at hleg ⊢
  have hsupQ : (S : ℚ) ≤ 18192 * ((m : ℚ) + 1) + 40 + 70 * ((Λ : ℚ) + 1) := by
    exact_mod_cast hsup
  have hlegQ : 480 * ((m : ℚ) + 1) - ((Λ : ℚ) + 1) ≤ (V : ℚ) := by
    have h := (Int.cast_le (R := ℚ)).mpr hleg
    push_cast at h
    linarith
  have hΛ0 : (0 : ℚ) ≤ (Λ : ℚ) := by positivity
  push_cast
  simp only [G]
  linarith

end BetaIrr.I3.Arith
