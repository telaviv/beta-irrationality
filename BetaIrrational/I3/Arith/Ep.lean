/-
# Lemma 4 for instance I3 (PROOF_BETA §4, μ_in = 3): the exponents `E_p` and `D_n`

With `n = nOf m = 480(m+1)` and `𝒩 = NN m = 2(2+r)n + 3 = 3040(m+1) + 3`:

| range of `p` | `E_p` (`Ep m p`) | source |
|---|---|---|
| `p > n`, odd (incl. `n < p ≤ 2n+1`) | `0` | Lemma A(a) + Lemma C |
| odd, `√𝒩 < p ≤ n` | `max_k (B_k + 2 - c_p(k) + Σ_j m_j P_{p,j}(k))` (`Esharp`) | Lemma A(b) + Lemma B |
| odd, `p ≤ √𝒩` | `max_k (-ν_p(k)) + (S+2)⌊log_p 𝒩⌋` (`Esmall`) | Lemma A(c) + Lemma B |
| `p = 2` | `max_k (-ν_2(k)) + S⌊log_2 n⌋` (`E2`) | binomial argument at `p = 2` |

Here `S = 35`. The per-`k` exponents are all instances of `etot` (file `LemmaA.lean`):
* `eSharp`: e-factor `[p ∣ n-2k]`, zero factors `[p ∣ w_l]`, pole factors `-[p ∣ k'-k]`;
  `eSharp_eq`: `eSharp = c_p(k) - Σ_j m_j P_{p,j}(k)` with `c_p`, `P_{p,j}` as in PROOF_BETA §3.
* `nuSmall` (`ν_p(k)` for odd `p`): e-factor `0`, zero factors `v_p(w_l)`, pole factors `-v_p(k'-k)`.
  (PROOF_BETA's `ν_p` also counts `v_p(n-2k)`; dropping it only weakens the bound.)
* `nu2` (`ν_2(k)`): e-factor `1` (as `n` is even), zero factors `-1`, pole factors `-v_2(k'-k)`.

`D m = Π_{p ≤ 2n+1} p^{E_p}` (a positive rational).

Main results:
* `D_pos`;
* `int_tau`: `∃ z : ℤ, z = D m · τ_i` for every `i` (unconditional);
* `int_rho`: `∃ z : ℤ, z = D m · ρ`, assuming `R''(l) = 0` for `-n ≤ l ≤ -1` (the zero of order
  `μ_in = 3`; `pf_R2_inner_zero` in `Concrete/`).

Status: complete (no `sorry`). The `E_p` for `√𝒩 < p ≤ n` is the sharp formula of PROOF_BETA §4.
-/
import BetaIrrational.I3.Arith.LemmaA
import BetaIrrational.I3.Concrete.Blocks
import BetaIrrational.Arith.LemmaBC

set_option linter.unusedSectionVars false

namespace BetaIrr.I3.Arith

open Finset BetaIrr.Arith
open BetaIrr.PFData (Bq)

/-! ### Elementary bounds -/

section Elem

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValNat_le_of_lt {z e : ℕ} (hz : 0 < z) (h : z < p ^ (e + 1)) :
    padicValNat p z ≤ e := by
  by_contra hc
  have h1 : p ^ (e + 1) ∣ z :=
    (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
  exact absurd (Nat.le_of_dvd hz h1) (not_le.mpr h)

theorem padicValRat_int_le {z : ℤ} (hz : z ≠ 0) {e : ℕ} (h : z.natAbs < p ^ (e + 1)) :
    padicValRat p (z : ℚ) ≤ e := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValNat_le_of_lt (Int.natAbs_pos.mpr hz) h

theorem padicValRat_int_le_ind {z : ℤ} (hz : z ≠ 0) (h : z.natAbs < p ^ 2) :
    padicValRat p (z : ℚ) ≤ if (p : ℤ) ∣ z then 1 else 0 := by
  split_ifs with hd
  · exact_mod_cast padicValRat_int_le hz (e := 1) h
  · rw [padicValRat_int_eq_zero hd]

theorem vge_ind_int (z : ℤ) : vge p (if (p : ℤ) ∣ z then 1 else 0) (z : ℚ) := by
  split_ifs with hd
  · exact vge_int_dvd hd
  · exact vge_int z

theorem vge_div_two_two {x : ℚ} {b : ℤ} (h : vge 2 b x) : vge 2 (b - 1) (x / 2) := by
  intro hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    simpa using this
  rw [padicValRat.div hx0 two_ne_zero, h2]
  have := h hx0
  omega

theorem padicValRat_prod {ι : Type*} (T : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ T, f i ≠ 0) :
    padicValRat p (∏ i ∈ T, f i) = ∑ i ∈ T, padicValRat p (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a T))
      (prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem vge_two_pow (j : ℕ) : vge p 0 ((2 : ℚ) ^ j) := by
  simpa using vge_pow (vge_nat (p := p) 2) j

end Elem

lemma list_sum_map_le {ι : Type*} (l : List ι) (f g : ι → ℕ) (h : ∀ b, f b ≤ g b) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) ih

/-! ### Definitions -/

/-- `𝒩 = 2(2+r)n + 3 = 3040(m+1) + 3`. -/
def NN (m : ℕ) : ℕ := 3040 * (m + 1) + 3

/-- `w_l = 2k + 1 + 2l`, so that `u_l = -w_l/2`. -/
def wl (k : ℕ) (l : ℤ) : ℤ := 2 * k + 1 + 2 * l

lemma u_eq (k : ℕ) (l : ℤ) : -(k : ℚ) - 1 / 2 - l = -((wl k l : ℤ) : ℚ) / 2 := by
  unfold wl; push_cast; ring

lemma wl_ne_zero (k : ℕ) (l : ℤ) : wl k l ≠ 0 := by unfold wl; omega

lemma wl_natAbs_lt (m k : ℕ) (hk : k ≤ nOf m) (l : ℤ) (hl : l ∈ zeroSet m) :
    (wl k l).natAbs < NN m := by
  unfold wl NN; unfold zeroSet at hl; unfold nOf at hk
  rw [mem_Icc] at hl
  omega

lemma d_natAbs_le (m k k' : ℕ) (hk : k ≤ nOf m) (hk' : k' ≤ nOf m) :
    ((k' : ℤ) - k).natAbs ≤ nOf m := by omega

lemma nOf_lt_NN (m : ℕ) : nOf m < NN m := by unfold nOf NN; omega

lemma d_cast (k k' : ℕ) : ((k' : ℚ) - k) = (((k' : ℤ) - k : ℤ) : ℚ) := by push_cast; ring

lemma e_cast (m k : ℕ) : ((nOf m : ℚ) - 2 * k) = (((nOf m : ℤ) - 2 * k : ℤ) : ℚ) := by
  push_cast; ring

/-- `c_p(k) = Σ_l μ(l) [p ∣ w_l] + e [p ∣ n - 2k]` (here `μ = 3`, `e = 1`). -/
def cp (m p k : ℕ) : ℤ :=
  ∑ l ∈ zeroSet m, 3 * (if (p : ℤ) ∣ wl k l then 1 else 0) +
    (if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0)

/-- `P_{p,j}(k) = #{k' ∈ [a_j, b_j], k' ≠ k : p ∣ k' - k}`. -/
def Ppj (m p k : ℕ) (b : ℕ × ℕ) : ℕ :=
  (((blockSet m b).erase k).filter (fun k' : ℕ => (p : ℤ) ∣ (k' : ℤ) - k)).card

/-- The Lemma A(b) exponent at `k` (sharp range `√𝒩 < p ≤ n`). -/
def eSharp (m p k : ℕ) : ℤ :=
  etot m k (if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0)
    (fun l => if (p : ℤ) ∣ wl k l then 1 else 0)
    (fun k' => -(if (p : ℤ) ∣ (k' : ℤ) - k then 1 else 0))

lemma eSharp_eq (m p k : ℕ) :
    eSharp m p k = cp m p k - (blocks.map (fun b => (b.2 : ℤ) * Ppj m p k b)).sum := by
  unfold eSharp etot cp Ppj
  have h : ∀ b : ℕ × ℕ, (b.2 : ℤ) * ∑ k' ∈ (blockSet m b).erase k,
      -(if (p : ℤ) ∣ (k' : ℤ) - k then 1 else 0)
      = -((b.2 : ℤ) * ((((blockSet m b).erase k).filter
          (fun k' : ℕ => (p : ℤ) ∣ (k' : ℤ) - k)).card : ℤ)) := by
    intro b
    rw [sum_neg_distrib, Finset.sum_boole]
    ring
  simp_rw [h]
  have hneg : ∀ l : List (ℕ × ℕ), ∀ f : ℕ × ℕ → ℤ,
      (l.map (fun b => -f b)).sum = -(l.map f).sum := by
    intro l f; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hneg]
  ring

/-- `ν_p(k)` for odd `p` (Lemma A(c) exponent). -/
def nuSmall (m p k : ℕ) : ℤ :=
  etot m k 0 (fun l => (padicValInt p (wl k l) : ℤ)) (fun k' => -(padicValInt p ((k' : ℤ) - k) : ℤ))

/-- `ν_2(k)`. -/
def nu2 (m k : ℕ) : ℤ :=
  etot m k 1 (fun _ => -1) (fun k' => -(padicValInt 2 ((k' : ℤ) - k) : ℤ))

/-- `E_p` for `√𝒩 < p ≤ n`: `max_k (B_k + 2 - c_p(k) + Σ_j m_j P_{p,j}(k))`. -/
def Esharp (m p : ℕ) : ℤ :=
  (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => (Bk m k : ℤ) + 2 - eSharp m p k)

/-- `E_p` for odd `p ≤ √𝒩`: `max_k (-ν_p(k)) + (S+2) ⌊log_p 𝒩⌋`. -/
def Esmall (m p : ℕ) : ℤ :=
  (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nuSmall m p k) +
    37 * (Nat.log p (NN m) : ℤ)

/-- `E_2 = max_k (-ν_2(k)) + S ⌊log_2 n⌋`. -/
def E2 (m : ℕ) : ℤ :=
  (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nu2 m k) +
    35 * (Nat.log 2 (nOf m) : ℤ)

/-- The exponent `E_p` of PROOF_BETA §4 (`μ_in = 3`). -/
def Ep (m p : ℕ) : ℤ :=
  if p = 2 then E2 m
  else if nOf m < p then 0
  else if NN m < p ^ 2 then Esharp m p
  else Esmall m p

lemma Esharp_eq (m p : ℕ) : Esharp m p = (range (nOf m + 1)).sup' nonempty_range_add_one
    (fun k => (Bk m k : ℤ) + 2 - cp m p k + (blocks.map (fun b => (b.2 : ℤ) * Ppj m p k b)).sum) := by
  unfold Esharp
  have hf : (fun k => (Bk m k : ℤ) + 2 - eSharp m p k) = (fun k => (Bk m k : ℤ) + 2 - cp m p k
      + (blocks.map (fun b => (b.2 : ℤ) * Ppj m p k b)).sum) :=
    funext fun k => by rw [eSharp_eq]; ring
  rw [hf]

/-- `D_n = Π_{p ≤ 2n+1} p^{E_p}`. -/
noncomputable def D (m : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * nOf m + 2)).filter Nat.Prime, (p : ℚ) ^ (Ep m p)

/-! ### `D` -/

theorem D_pos (m : ℕ) : 0 < D m := by
  unfold D
  refine prod_pos (fun p hp => zpow_pos ?_ _)
  exact_mod_cast (mem_filter.mp hp).2.pos

theorem Ep_eq_zero_of_lt {m p : ℕ} (hp2 : p ≠ 2) (h : nOf m < p) : Ep m p = 0 := by
  simp [Ep, hp2, h]

theorem padicValRat_D (m q : ℕ) [hq : Fact q.Prime] : padicValRat q (D m) = Ep m q := by
  unfold D
  rw [padicValRat_prod _ _ (fun p hp => zpow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.ne_zero))]
  have hv : ∀ p ∈ (range (2 * nOf m + 2)).filter Nat.Prime,
      padicValRat q ((p : ℚ) ^ Ep m p) = if p = q then Ep m q else 0 := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    rw [padicValRat.zpow, padicValRat.of_nat]
    split_ifs with hpq
    · subst hpq; simp [padicValNat_self]
    · have : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp').mp h).symm
      simp [padicValNat.eq_zero_of_not_dvd this]
  rw [sum_congr rfl hv, sum_ite_eq']
  split_ifs with hmem
  · rfl
  · have hq2 : q ≠ 2 := by
      rintro rfl; apply hmem; simp [Nat.prime_two, nOf]
    have : nOf m < q := by
      by_contra hc
      apply hmem
      simp only [mem_filter, mem_range]
      exact ⟨by omega, hq.out⟩
    rw [Ep_eq_zero_of_lt hq2 this]

/-- Integrality from per-prime bounds. -/
theorem int_of_vge_Ep (m : ℕ) {x : ℚ} (h : ∀ q : ℕ, q.Prime → vge q (-Ep m q) x) :
    ∃ z : ℤ, (z : ℚ) = D m * x := by
  refine int_of_forall_vge (fun q hq => ?_)
  have : Fact q.Prime := ⟨hq⟩
  have hD : vge q (Ep m q) (D m) := fun _ => (padicValRat_D m q).ge
  simpa using vge_mul hD (h q hq)

end BetaIrr.I3.Arith
