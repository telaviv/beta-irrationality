/-
# Lemma A for instance I3 (PROOF_BETA §3): valuations of the Taylor coefficients `a_{i,k}`

For the data of `I3/Concrete/Data.lean`.

`fSeries m k = (C(n-2k) + 2X) · Π_l (C u_l + X)^3 · Π_j (Π_{k'≠k} (C(k'-k) + X)⁻¹)^{m_j}`.

`psge_fSeries` is the binomial argument with free per-factor exponents: if each zero factor gets
an exponent `eZ l ≤ λ` with `v_p(u_l) ≥ eZ l`, each pole factor an exponent
`eP k' ≤ -v_p(k'-k)` with `v_p(k'-k) ≤ λ`, and the e-factor an exponent `eE` with
`v_p(n-2k) ≥ eE` (or `n = 2k`) and `v_p(2) ≥ eE - λ`, then
`v_p([X^M] f_k) ≥ eE + 3 Σ_l eZ l + Σ_j m_j Σ_{k'} eP k' - λ M`.

`vge_a` turns this into the bound on `a_{i,k} = [X^{B_k - i}] f_k`. The regimes of Lemma A(a),
(b), (c) and the `p = 2` case are instances (file `Ep.lean`).

Status: complete (no `sorry`).
-/
import BetaIrrational.Arith.PSVal
import BetaIrrational.I3.Concrete.Data

set_option linter.unusedSectionVars false

namespace BetaIrr.I3.Arith

open Finset PowerSeries BetaIrr.Arith

variable {p : ℕ} [hp : Fact p.Prime]

/-- The block of `b = (k, m_b)`: `[3 k (m+1), n - 3 k (m+1)]`. -/
def blockSet (m : ℕ) (b : ℕ × ℕ) : Finset ℕ := Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))

/-- The zero indices `l ∈ [-1040(m+1)-1, 560(m+1)]`. -/
def zeroSet (m : ℕ) : Finset ℤ := Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))

lemma mem_blockSet_le {m k' : ℕ} {b : ℕ × ℕ} (h : k' ∈ blockSet m b) : k' ≤ nOf m := by
  simp only [blockSet, mem_Icc] at h; omega

/-- The total exponent of the binomial argument. -/
def etot (m k : ℕ) (eE : ℤ) (eZ : ℤ → ℤ) (eP : ℕ → ℤ) : ℤ :=
  eE + ∑ l ∈ zeroSet m, 3 * eZ l +
    (blocks.map (fun b => (b.2 : ℤ) * ∑ k' ∈ (blockSet m b).erase k, eP k')).sum

/-- **Lemma A (binomial argument), general form.** -/
theorem psge_fSeries (m k : ℕ) (lam eE : ℤ) (eZ : ℤ → ℤ) (eP : ℕ → ℤ)
    (hE1 : vge p eE ((nOf m : ℚ) - 2 * k)) (hE2 : vge p (eE - lam) 2)
    (hZ : ∀ l ∈ zeroSet m, vge p (eZ l) (-(k : ℚ) - 1 / 2 - l) ∧ eZ l ≤ lam)
    (hP : ∀ k' ≤ nOf m, k' ≠ k →
      eP k' ≤ -padicValRat p ((k' : ℚ) - k) ∧ padicValRat p ((k' : ℚ) - k) ≤ lam) :
    psge p (etot m k eE eZ eP) lam (fSeries m k) := by
  unfold fSeries numSeries denSeries etot
  refine psge_mul (psge_mul ?_ ?_) ?_
  · have h2 : (2 : PowerSeries ℚ) = C 2 := (map_ofNat C 2).symm
    rw [h2]
    exact psge_lin hE1 hE2
  · refine psge_prod _ _ _ lam (fun l hl => ?_)
    have h := psge_pow (psge_lin (p := p) (lam := lam) (c := 1) (hZ l hl).1
      (by intro _; simp; linarith [(hZ l hl).2])) 3
    simp only [map_one, one_mul] at h
    simpa using h
  · refine psge_listProd blocks _ _ lam (fun b _ => ?_)
    have h := psge_pow (psge_prod (p := p) ((blockSet m b).erase k) _ eP lam (fun k' hk' => by
      have hk'1 : k' ≠ k := ne_of_mem_erase hk'
      have hk'2 : k' ≤ nOf m := mem_blockSet_le (mem_of_mem_erase hk')
      have hd : ((k' : ℚ) - k) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hk'1)
      exact psge_inv hd (hP k' hk'2 hk'1).1 (hP k' hk'2 hk'1).2)) b.2
    exact h

/-- **Lemma A, coefficient form.** `v_p(a_{i,k}) ≥ etot - λ (B_k - i)`. -/
theorem vge_a (m i k : ℕ) (lam eE : ℤ) (eZ : ℤ → ℤ) (eP : ℕ → ℤ)
    (hE1 : vge p eE ((nOf m : ℚ) - 2 * k)) (hE2 : vge p (eE - lam) 2)
    (hZ : ∀ l ∈ zeroSet m, vge p (eZ l) (-(k : ℚ) - 1 / 2 - l) ∧ eZ l ≤ lam)
    (hP : ∀ k' ≤ nOf m, k' ≠ k →
      eP k' ≤ -padicValRat p ((k' : ℚ) - k) ∧ padicValRat p ((k' : ℚ) - k) ≤ lam) :
    vge p (etot m k eE eZ eP - lam * ((Bk m k : ℤ) - i)) (a m i k) := by
  unfold a
  split_ifs with hi
  · have := psge_fSeries m k lam eE eZ eP hE1 hE2 hZ hP (Bk m k - i)
    have hc : ((Bk m k - i : ℕ) : ℤ) = (Bk m k : ℤ) - i := Nat.cast_sub hi.2
    rw [hc] at this
    exact this
  · exact vge_zero _

end BetaIrr.I3.Arith
