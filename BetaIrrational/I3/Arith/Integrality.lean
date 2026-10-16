/-
# Lemma 4 for instance I3: `D_n ρ_n, D_n τ_i ∈ ℤ` (PROOF_BETA §4, μ_in = 3)


For each prime `p` we show `v_p(τ_i) ≥ -E_p` and `v_p(ρ) ≥ -E_p`, in four regimes:
* `p = 2`: `a_bound_two` (slope `λ = ⌊log_2 n⌋`);
* odd `p > n`: `a_int` (Lemma A(a)), and Lemma C for `ρ`;
* odd `p`, `𝒩 < p²` (`√𝒩 < p ≤ n`): `a_bound_sharp` (Lemma A(b), slope 1);
* odd `p`, `p² ≤ 𝒩`: `a_bound_small` (Lemma A(c), slope `λ = ⌊log_p 𝒩⌋`).

Main theorems:
* `int_tau (m i) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).tau i` (unconditional);
* `int_rho (m) (hR2 : ∀ l : ℤ, -n ≤ l → l ≤ -1 → (pf m).R2 l = 0) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).rho`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Arith.Ep

set_option linter.unusedSectionVars false

namespace BetaIrr.I3.Arith

open Finset BetaIrr.Arith
open BetaIrr.PFData (Bq)

variable {p : ℕ} [hp : Fact p.Prime]

theorem vge_two' : vge p 0 (2 : ℚ) := by simpa using vge_nat (p := p) 2

theorem padicValRat_two_two : padicValRat 2 (2 : ℚ) = 1 := by
  have := padicValRat.self (p := 2) (by norm_num)
  simpa using this

lemma odd_natAbs_lt (m m' k : ℕ) (hk : k ≤ nOf m) (hm' : m' < k) :
    ((2 * m' + 1 : ℕ) : ℤ).natAbs < NN m := by
  unfold NN; unfold nOf at hk; omega

lemma cast_odd (m' : ℕ) : (2 * (m' : ℚ) + 1) = (((2 * m' + 1 : ℕ) : ℤ) : ℚ) := by push_cast; ring

/-! ### Regime: odd `p`, `𝒩 < p²` -/

theorem a_bound_sharp (m : ℕ) (hp2 : p ≠ 2) (hN : NN m < p ^ 2) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (eSharp m p k - ((Bk m k : ℤ) - i)) (a m i k) := by
  have h := vge_a (p := p) m i k 1 (if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0)
    (fun l => if (p : ℤ) ∣ wl k l then 1 else 0)
    (fun k' => -(if (p : ℤ) ∣ (k' : ℤ) - k then 1 else 0))
    (by rw [e_cast]; exact vge_ind_int _)
    (vge_mono vge_two' (by split_ifs <;> norm_num))
    (fun l _ => ⟨by rw [u_eq]; exact vge_div_two hp2 (vge_neg (vge_ind_int _)),
      by split_ifs <;> norm_num⟩)
    (fun k' hk' hne => by
      have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
      have hlt : ((k' : ℤ) - k).natAbs < p ^ 2 := by
        have := d_natAbs_le m k k' hk hk'; have := nOf_lt_NN m; omega
      have h1 := padicValRat_int_le_ind (p := p) hd0 hlt
      rw [d_cast]
      refine ⟨by linarith, h1.trans (by split_ifs <;> norm_num)⟩)
  rw [one_mul] at h
  exact h

theorem bounds_sharp (m : ℕ) (hp2 : p ≠ 2) (hN : NN m < p ^ 2) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (-Esharp m p) (a m i k * 2 ^ (i + 2)) ∧
      vge p (-Esharp m p) (a m i k * 2 ^ (i + 2) * Bq (i + 2) k) := by
  have hA := a_bound_sharp m hp2 hN i k hk
  have hE : (Bk m k : ℤ) + 2 - eSharp m p k ≤ Esharp m p :=
    le_sup' (fun k => (Bk m k : ℤ) + 2 - eSharp m p k) (mem_range.mpr (by omega))
  have hB := vge_Bq (p := p) (i + 2) k 1 (fun m' hm' => by
    rw [cast_odd]
    have hlt : ((2 * m' + 1 : ℕ) : ℤ).natAbs < p ^ (1 + 1) := by
      have := odd_natAbs_lt m m' k hk hm'; rw [show 1 + 1 = 2 from rfl]; omega
    exact_mod_cast padicValRat_int_le (by omega) hlt)
  have h2 := vge_two_pow (p := p) (i + 2)
  refine ⟨vge_mono (vge_mul hA h2) ?_, vge_mono (vge_mul (vge_mul hA h2) hB) ?_⟩
  · push_cast; linarith
  · push_cast; linarith

/-! ### Regime: odd `p`, `p² ≤ 𝒩` -/

lemma NN_lt_pow_log (m : ℕ) : NN m < p ^ (Nat.log p (NN m) + 1) :=
  Nat.lt_pow_succ_log_self hp.out.one_lt _

theorem a_bound_small (m : ℕ) (hp2 : p ≠ 2) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (nuSmall m p k - (Nat.log p (NN m) : ℤ) * ((Bk m k : ℤ) - i)) (a m i k) := by
  have hlog := NN_lt_pow_log (p := p) m
  have h := vge_a (p := p) m i k (Nat.log p (NN m) : ℤ) 0
    (fun l => (padicValInt p (wl k l) : ℤ))
    (fun k' => -(padicValInt p ((k' : ℤ) - k) : ℤ))
    (by rw [e_cast]; exact vge_int _)
    (vge_mono vge_two' (by omega))
    (fun l hl => by
      refine ⟨?_, ?_⟩
      · rw [u_eq]
        refine vge_div_two hp2 (vge_neg ?_)
        intro _; rw [padicValRat.of_int]
      · have := padicValRat_int_le (p := p) (wl_ne_zero k l)
          (e := Nat.log p (NN m)) ((wl_natAbs_lt m k hk l hl).trans hlog)
        rw [padicValRat.of_int] at this
        exact this)
    (fun k' hk' hne => by
      have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
      have hlt : ((k' : ℤ) - k).natAbs < p ^ (Nat.log p (NN m) + 1) := by
        have := d_natAbs_le m k k' hk hk'; have := nOf_lt_NN m; omega
      have h1 := padicValRat_int_le (p := p) hd0 hlt
      rw [d_cast]
      refine ⟨?_, h1⟩
      rw [padicValRat.of_int])
  exact h

theorem bounds_small (m : ℕ) (hp2 : p ≠ 2) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (-Esmall m p) (a m i k * 2 ^ (i + 2)) ∧
      vge p (-Esmall m p) (a m i k * 2 ^ (i + 2) * Bq (i + 2) k) := by
  have hlog := NN_lt_pow_log (p := p) m
  set lam : ℤ := (Nat.log p (NN m) : ℤ) with hlam
  have hA := a_bound_small m hp2 i k hk
  have hE : -nuSmall m p k ≤ (range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nuSmall m p k) :=
    le_sup' (fun k => -nuSmall m p k) (mem_range.mpr (by omega))
  have hB := vge_Bq (p := p) (i + 2) k lam (fun m' hm' => by
    rw [cast_odd]
    have hlt : ((2 * m' + 1 : ℕ) : ℤ).natAbs < p ^ (Nat.log p (NN m) + 1) := by
      have := odd_natAbs_lt m m' k hk hm'; omega
    exact_mod_cast padicValRat_int_le (by omega) hlt)
  have h2 := vge_two_pow (p := p) (i + 2)
  have hl0 : 0 ≤ lam := by positivity
  have hBk : (Bk m k : ℤ) ≤ 35 := by exact_mod_cast Bk_le m k
  have hi : (0 : ℤ) ≤ i := by positivity
  unfold Esmall
  refine ⟨vge_mono (vge_mul hA h2) ?_, vge_mono (vge_mul (vge_mul hA h2) hB) ?_⟩
  · push_cast; nlinarith
  · push_cast; nlinarith

/-! ### Regime: `p = 2` -/

theorem a_bound_two (m i k : ℕ) (hk : k ≤ nOf m) :
    vge 2 (nu2 m k - (Nat.log 2 (nOf m) : ℤ) * ((Bk m k : ℤ) - i)) (a m i k) := by
  have hlog : nOf m < 2 ^ (Nat.log 2 (nOf m) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h := vge_a (p := 2) m i k (Nat.log 2 (nOf m) : ℤ) 1
    (fun _ => -1)
    (fun k' => -(padicValInt 2 ((k' : ℤ) - k) : ℤ))
    (by
      rw [e_cast]
      refine vge_int_dvd ?_
      unfold nOf; push_cast; omega)
    (by
      refine vge_mono (vge_self (p := 2) (x := 2)) ?_
      rw [padicValRat_two_two]; omega)
    (fun l _ => by
      refine ⟨?_, by omega⟩
      rw [u_eq]
      simpa using vge_div_two_two (vge_neg (vge_int (p := 2) (wl k l))))
    (fun k' hk' hne => by
      have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
      have hlt : ((k' : ℤ) - k).natAbs < 2 ^ (Nat.log 2 (nOf m) + 1) := by
        have := d_natAbs_le m k k' hk hk'; omega
      have h1 := padicValRat_int_le (p := 2) hd0 hlt
      rw [d_cast]
      refine ⟨?_, h1⟩
      rw [padicValRat.of_int])
  exact h

theorem bounds_two (m i k : ℕ) (hk : k ≤ nOf m) :
    vge 2 (-E2 m) (a m i k * 2 ^ (i + 2)) ∧
      vge 2 (-E2 m) (a m i k * 2 ^ (i + 2) * Bq (i + 2) k) := by
  set lam : ℤ := (Nat.log 2 (nOf m) : ℤ) with hlam
  have hA := a_bound_two m i k hk
  have hE : -nu2 m k ≤ (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nu2 m k) :=
    le_sup' (fun k => -nu2 m k) (mem_range.mpr (by omega))
  have hB := vge_Bq (p := 2) (i + 2) k 0 (fun m' _ => by
    rw [cast_odd, padicValRat_int_eq_zero (by push_cast; omega)])
  have h2 : vge 2 ((i + 2 : ℕ) * 1) ((2 : ℚ) ^ (i + 2)) := by
    have := vge_pow (vge_self (p := 2) (x := 2)) (i + 2)
    rwa [padicValRat_two_two] at this
  have hl0 : 0 ≤ lam := by positivity
  have hBk : (Bk m k : ℤ) ≤ 35 := by exact_mod_cast Bk_le m k
  have hi : (0 : ℤ) ≤ i := by positivity
  unfold E2
  refine ⟨vge_mono (vge_mul hA h2) ?_, vge_mono (vge_mul (vge_mul hA h2) hB) ?_⟩
  · push_cast; nlinarith
  · push_cast; nlinarith

/-! ### Regime: odd `p > n` (Lemma A(a)) -/

theorem a_int (m : ℕ) (hp2 : p ≠ 2) (hpn : nOf m < p) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p 0 (a m i k) := by
  have h := vge_a (p := p) m i k 0 0 (fun _ => 0) (fun _ => 0)
    (by rw [e_cast]; exact vge_int _)
    (by simpa using vge_two' (p := p))
    (fun l _ => ⟨by rw [u_eq]; exact vge_div_two hp2 (vge_neg (vge_int _)), le_rfl⟩)
    (fun k' hk' hne => by
      have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
      have hnd : ¬ (p : ℤ) ∣ ((k' : ℤ) - k) := by
        intro hd
        have h1 : p ∣ ((k' : ℤ) - k).natAbs := Int.natCast_dvd.mp hd
        have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hd0) h1
        have := d_natAbs_le m k k' hk hk'
        omega
      rw [d_cast, padicValRat_int_eq_zero hnd]
      simp)
  have he : etot m k 0 (fun _ => 0) (fun _ => 0) = 0 := by simp [etot]
  rw [he, zero_mul, sub_zero] at h
  exact h

/-! ### Assembly -/

lemma pf_K (m : ℕ) : (pf m).K = nOf m := rfl
lemma pf_I (m : ℕ) : (pf m).I = 35 := rfl
lemma pf_a (m : ℕ) : (pf m).a = a m := rfl

/-- The per-prime bounds for the `a`-terms in every regime except odd `p > n`. -/
theorem bounds_all (m : ℕ) (hq : ¬ (p ≠ 2 ∧ nOf m < p)) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (-Ep m p) (a m i k * 2 ^ (i + 2)) ∧
      vge p (-Ep m p) (a m i k * 2 ^ (i + 2) * Bq (i + 2) k) := by
  unfold Ep
  by_cases h2 : p = 2
  · subst h2; simpa using bounds_two m i k hk
  · have hpn : ¬ nOf m < p := fun h => hq ⟨h2, h⟩
    simp only [h2, hpn, ite_false]
    split_ifs with hN
    · exact bounds_sharp m h2 hN i k hk
    · exact bounds_small m h2 i k hk

theorem vge_tau_Ep (m i : ℕ) : vge p (-Ep m p) ((pf m).tau i) := by
  refine vge_tau (pf m) i _ (fun k hk => ?_)
  rw [pf_a]
  by_cases hq : p ≠ 2 ∧ nOf m < p
  · rw [Ep_eq_zero_of_lt hq.1 hq.2]
    simpa using vge_mul (a_int m hq.1 hq.2 i k hk) (vge_two_pow (p := p) (i + 2))
  · exact (bounds_all m hq i k hk).1

/-- `R''(-l)` of the partial-fraction data, as a rational number. -/
lemma R2_neg_nat (P : PFData) (l : ℕ) :
    P.R2 (-(l : ℝ)) = ((∑ k ∈ range (P.K + 1), Tlk P l k : ℚ) : ℝ) := by
  unfold PFData.R2 Tlk
  push_cast
  refine sum_congr rfl (fun k _ => sum_congr rfl (fun i _ => ?_))
  rw [show -(l : ℝ) + ((k : ℝ) + 1 / 2) = (k : ℝ) - l + 1 / 2 by ring]

theorem vge_rho_Ep (m : ℕ)
    (hR2 : ∀ l : ℤ, -(nOf m : ℤ) ≤ l → l ≤ -1 → (pf m).R2 (l : ℝ) = 0) :
    vge p (-Ep m p) (pf m).rho := by
  by_cases hq : p ≠ 2 ∧ nOf m < p
  · rw [Ep_eq_zero_of_lt hq.1 hq.2, neg_zero]
    refine vge_rho_of_R2_zero (pf m) hq.1 hq.2 (fun i k hk => ?_) (fun l hl => ?_)
    · rw [pf_a]; exact a_int m hq.1 hq.2 i k hk
    · have hl' := mem_Icc.mp hl
      have h := hR2 (-(l : ℤ)) (by rw [pf_K] at hl'; omega) (by omega)
      rw [show ((-(l : ℤ) : ℤ) : ℝ) = -(l : ℝ) by push_cast; ring, R2_neg_nat] at h
      exact_mod_cast h
  · refine vge_rho (pf m) _ (fun k hk i _ => ?_)
    rw [pf_a]
    exact (bounds_all m hq i k hk).2

/-- **Lemma 4 (τ part).** `D_n τ_i ∈ ℤ` for every `i`. -/
theorem int_tau (m i : ℕ) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).tau i :=
  int_of_vge_Ep m (fun q hq => by have : Fact q.Prime := ⟨hq⟩; exact vge_tau_Ep m i)

/-- **Lemma 4 (ρ part).** `D_n ρ_n ∈ ℤ`, given the triple zeros of `R_n` on `[-n, -1]` in the form
`R''(l) = 0` (used through Lemma C for the primes `n < p ≤ 2n+1`). -/
theorem int_rho (m : ℕ)
    (hR2 : ∀ l : ℤ, -(nOf m : ℤ) ≤ l → l ≤ -1 → (pf m).R2 (l : ℝ) = 0) :
    ∃ z : ℤ, (z : ℚ) = D m * (pf m).rho :=
  int_of_vge_Ep m (fun q hq => by have : Fact q.Prime := ⟨hq⟩; exact vge_rho_Ep m hR2)

end BetaIrr.I3.Arith
