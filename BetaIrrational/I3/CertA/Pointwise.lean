/-
# Lemma 5 (pointwise part) for instance I3


`PROOF_BETA.md` §3 (definitions of `c_p(k)`, `P_{p,j}(k)`) and §5.1 (Claim).

For `n = nOf m = 480(m+1)`, every odd `p ≤ n` (in particular every prime `√𝒩 < p ≤ n`) and every
`k` with `B_k ≥ 1`:

  `(B_k + 2 - c_p(k) + Σ_j m_j P_{p,j}(k)) - G ⌊n/p⌋ ≤ e*(n/p)`.

Here
* `c_p(k) = 3 · #{l ∈ [-1040(m+1)-1, 560(m+1)] : p ∣ 2k+1+2l}` (the zero run `[-(1+r)n-1, rn]`,
  multiplicity 3; the `e`-term of §3 is omitted, it only increases `c_p(k)`),
* `P_{p,j}(k) = #{k' ∈ [a_j, b_j], k' ≠ k : p ∣ k' - k}`, `a_j = 3 d_j (m+1) = δ_j n`, `b_j = n - a_j`.

Proof: `B_k = S(k/p)`, `P_{p,j}(k) = P_j(k/p)` exactly (`Pfun_eq`), `c_p(k) ≥ c(k/p)` (`cfun_le_cp`),
so the left side is `≤ f(n/p, k/p) ≤ e*(n/p)` (`f_le_eStar`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.CertA.Sound
import BetaIrrational.I3.Concrete.Data

namespace BetaIrr.I3.CertA

open Finset

/-! ## Definitions (PROOF_BETA §3) -/

/-- `c_p(k)`: the zero run `l ∈ [-(1+r)n-1, rn] = [-1040(m+1)-1, 560(m+1)]` has multiplicity 3, and
`w_l = 2k+1+2l`. -/
def cp (m p k : ℕ) : ℕ :=
  3 * #{l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)) |
    (p : ℤ) ∣ 2 * (k : ℤ) + 1 + 2 * l}

/-- `P_{p,j}(k) = #{k' ∈ [a_j, b_j], k' ≠ k : p ∣ k' - k}` for the block with `δ_j = d/160`. -/
def Ppj (m p d k : ℕ) : ℕ :=
  #{k' ∈ (Icc ((3 * d * (m + 1) : ℕ) : ℤ) ((nOf m - 3 * d * (m + 1) : ℕ) : ℤ)).erase (k : ℤ) |
    (p : ℤ) ∣ k' - k}

/-! ## Floors of `N/p` -/

/-- `⌊N/p⌋` as a rational floor. -/
def flp (p : ℕ) (N : ℤ) : ℤ := ⌊(N : ℚ) / ((p : ℤ) : ℚ)⌋

section flp
variable {p : ℕ} (hp : 0 < p)
include hp

lemma flp_bounds (N : ℤ) : flp p N * p ≤ N ∧ N < (flp p N + 1) * p := by
  have hp' : (0 : ℚ) < ((p : ℤ) : ℚ) := by exact_mod_cast hp
  have h1 := Int.floor_le ((N : ℚ) / ((p : ℤ) : ℚ))
  have h2 := Int.lt_floor_add_one ((N : ℚ) / ((p : ℤ) : ℚ))
  rw [le_div_iff₀ hp'] at h1
  rw [div_lt_iff₀ hp'] at h2
  unfold flp
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

lemma flp_eq (N a : ℤ) (h1 : a * p ≤ N) (h2 : N < (a + 1) * p) : flp p N = a :=
  floor_div_eq N p a (by exact_mod_cast hp) h1 h2

lemma flp_neg_succ (N : ℤ) : flp p (-N - 1) = -flp p N - 1 := by
  obtain ⟨h1, h2⟩ := flp_bounds hp N
  apply flp_eq hp <;> nlinarith

lemma flp_neg (N : ℤ) : flp p (-N) = -flp p N - (if (p : ℤ) ∣ N then 0 else 1) := by
  obtain ⟨h1, h2⟩ := flp_bounds hp N
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have hc : flp p (p * c) = c := flp_eq hp _ _ (by nlinarith) (by nlinarith)
    rw [hc]
    apply flp_eq hp <;> nlinarith
  · have hne : flp p N * p ≠ N := fun h => hd (Dvd.intro_left _ h)
    have hlt : flp p N * p < N := lt_of_le_of_ne h1 hne
    apply flp_eq hp <;> nlinarith

lemma flp_pred (N : ℤ) : flp p (N - 1) = flp p N - (if (p : ℤ) ∣ N then 1 else 0) := by
  obtain ⟨h1, h2⟩ := flp_bounds hp N
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have hc : flp p (p * c) = c := flp_eq hp _ _ (by nlinarith) (by nlinarith)
    rw [hc]
    apply flp_eq hp <;> nlinarith
  · have hne : flp p N * p ≠ N := fun h => hd (Dvd.intro_left _ h)
    have hlt : flp p N * p < N := lt_of_le_of_ne h1 hne
    apply flp_eq hp <;> nlinarith

lemma fract_div_eq_zero (N : ℤ) : Int.fract ((N : ℚ) / ((p : ℤ) : ℚ)) = 0 ↔ (p : ℤ) ∣ N := by
  have hp' : ((p : ℤ) : ℚ) ≠ 0 := by have : (0 : ℚ) < ((p : ℤ) : ℚ) := by exact_mod_cast hp
                                     exact this.ne'
  rw [Int.fract_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : (N : ℚ) = (p : ℤ) * z := by rw [hz]; field_simp
    exact_mod_cast this
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    push_cast
    field_simp

/-- Multiples of `p` among `k' - c`, `k' ∈ [a, b]`. -/
lemma card_Icc_dvd (a b c : ℤ) (hab : a ≤ b) :
    (#{k' ∈ Icc a b | (p : ℤ) ∣ k' - c} : ℤ) = flp p (b - c) - flp p (a - 1 - c) := by
  have hbij : #{k' ∈ Icc a b | (p : ℤ) ∣ k' - c} = #{t ∈ Ioc (a - 1 - c) (b - c) | (p : ℤ) ∣ t} := by
    apply Finset.card_nbij' (fun k' => k' - c) (fun t => t + c)
    · intro k' hk'
      simp only [coe_filter, Set.mem_setOf_eq, mem_Icc, mem_Ioc] at hk' ⊢
      exact ⟨⟨by omega, by omega⟩, hk'.2⟩
    · intro t ht
      simp only [coe_filter, Set.mem_setOf_eq, mem_Icc, mem_Ioc] at ht ⊢
      exact ⟨⟨by omega, by omega⟩, by simpa using ht.2⟩
    · intro k' _; simp
    · intro t _; simp
  rw [hbij, Int.Ioc_filter_dvd_card _ _ (by exact_mod_cast hp : (0 : ℤ) < p)]
  have hmono : flp p (a - 1 - c) ≤ flp p (b - c) := by
    unfold flp
    apply Int.floor_le_floor
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (by omega : a - 1 - c ≤ b - c)
  unfold flp at hmono ⊢
  push_cast at hmono ⊢
  omega

/-- `P_{p,j}(k)` in closed form. -/
lemma card_block (A B k : ℤ) (hAB : A ≤ B) :
    (#{k' ∈ (Icc A B).erase k | (p : ℤ) ∣ k' - k} : ℤ) =
      flp p (B - k) - flp p (A - 1 - k) - (if A ≤ k ∧ k ≤ B then 1 else 0) := by
  rw [Finset.filter_erase]
  split_ifs with hk
  · rw [Finset.card_erase_of_mem (by simp [hk])]
    have hpos : 0 < #{k' ∈ Icc A B | (p : ℤ) ∣ k' - k} :=
      Finset.card_pos.2 ⟨k, by simp [hk]⟩
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hpos.ne')]
    rw [card_Icc_dvd hp A B k hAB]
  · rw [Finset.erase_eq_of_notMem (by simp; omega), card_Icc_dvd hp A B k hAB]
    ring

/-- The §5.1 formula for `P_j` at `x = n/p`, `y = k/p` equals the count `P_{p,j}(k)`. -/
lemma Pgen_eq (A B k : ℕ) (hAB : A ≤ B) :
    (if (A : ℚ) / p ≤ (k : ℚ) / p ∧ (k : ℚ) / p ≤ (B : ℚ) / p then
        ⌊(k : ℚ) / p - (A : ℚ) / p⌋ + ⌊(B : ℚ) / p - (k : ℚ) / p⌋
      else if (k : ℚ) / p < (A : ℚ) / p then
        ⌊(B : ℚ) / p - (k : ℚ) / p⌋ - ⌊(A : ℚ) / p - (k : ℚ) / p⌋ +
          (if Int.fract ((A : ℚ) / p - (k : ℚ) / p) = 0 then 1 else 0)
      else
        ⌊(k : ℚ) / p - (A : ℚ) / p⌋ - ⌊(k : ℚ) / p - (B : ℚ) / p⌋ +
          (if Int.fract ((k : ℚ) / p - (B : ℚ) / p) = 0 then 1 else 0)) =
      (#{k' ∈ (Icc (A : ℤ) (B : ℤ)).erase (k : ℤ) | (p : ℤ) ∣ k' - k} : ℤ) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hsub : ∀ a b : ℕ, (a : ℚ) / p - (b : ℚ) / p = (((a : ℤ) - b : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    intro a b; push_cast; ring
  have hle : ∀ a b : ℕ, (a : ℚ) / p ≤ (b : ℚ) / p ↔ a ≤ b := by
    intro a b; rw [div_le_div_iff_of_pos_right hp']; exact Nat.cast_le
  have hlt : ∀ a b : ℕ, (a : ℚ) / p < (b : ℚ) / p ↔ a < b := by
    intro a b; rw [div_lt_div_iff_of_pos_right hp']; exact Nat.cast_lt
  rw [card_block hp A B k (by exact_mod_cast hAB)]
  have hf : ∀ N : ℤ, ⌊(N : ℚ) / ((p : ℤ) : ℚ)⌋ = flp p N := fun _ => rfl
  simp only [hsub, hle, hlt, fract_div_eq_zero hp, hf]
  have e1 : flp p ((A : ℤ) - 1 - k) = -flp p ((k : ℤ) - A) - 1 := by
    rw [show (A : ℤ) - 1 - k = -((k : ℤ) - A) - 1 by ring]; exact flp_neg_succ hp _
  have e2 : flp p ((A : ℤ) - 1 - k) =
      flp p ((A : ℤ) - k) - (if (p : ℤ) ∣ (A : ℤ) - k then 1 else 0) := by
    rw [show (A : ℤ) - 1 - k = ((A : ℤ) - k) - 1 by ring]; exact flp_pred hp _
  have e3 : flp p ((B : ℤ) - k) =
      -flp p ((k : ℤ) - B) - (if (p : ℤ) ∣ (k : ℤ) - B then 0 else 1) := by
    rw [show (B : ℤ) - k = -((k : ℤ) - B) by ring]; exact flp_neg hp _
  by_cases hin : A ≤ k ∧ k ≤ B
  · have hin' : (A : ℤ) ≤ k ∧ (k : ℤ) ≤ B := by omega
    rw [if_pos hin, if_pos hin', e1]; ring
  · have hin' : ¬((A : ℤ) ≤ k ∧ (k : ℤ) ≤ B) := by omega
    rw [if_neg hin, if_neg hin']
    by_cases hkA : k < A
    · rw [if_pos hkA, e2]; ring
    · rw [if_neg hkA, e1, e3]; split_ifs <;> ring

end flp


/-! ## The three ingredients at `x = n/p`, `y = k/p` -/

lemma blocks_d_le : ∀ b ∈ blocks, b.1 ≤ 46 := by decide

lemma dlt_mul_x (m p d : ℕ) :
    dlt d * ((nOf m : ℚ) / p) = ((3 * d * (m + 1) : ℕ) : ℚ) / p := by
  unfold dlt nOf; push_cast; ring

lemma one_sub_dlt_mul_x (m p d : ℕ) (hd : d ≤ 160) :
    (1 - dlt d) * ((nOf m : ℚ) / p) = ((nOf m - 3 * d * (m + 1) : ℕ) : ℚ) / p := by
  have h : 3 * d * (m + 1) ≤ nOf m := by unfold nOf; nlinarith
  rw [Nat.cast_sub h]
  unfold dlt nOf; push_cast; ring

/-- `B_k = S(k/p)` exactly. -/
lemma Sfun_eq_Bk (m p k : ℕ) (hp : 0 < p) : Sfun ((nOf m : ℚ) / p) ((k : ℚ) / p) = Bk m k := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hle : ∀ a b : ℕ, (a : ℚ) / p ≤ (b : ℚ) / p ↔ a ≤ b := by
    intro a b; rw [div_le_div_iff_of_pos_right hp']; exact Nat.cast_le
  unfold Sfun Bk
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [dlt_mul_x, one_sub_dlt_mul_x m p b.1 (by have := blocks_d_le b hb; omega)]
  simp only [hle]

/-- `P_{p,j}(k) = P_j(k/p)` exactly (including the out-of-block indicator terms). -/
lemma Pfun_eq_Ppj (m p d k : ℕ) (hp : 0 < p) (hd : d ≤ 46) :
    Pfun d ((nOf m : ℚ) / p) ((k : ℚ) / p) = Ppj m p d k := by
  unfold Pfun Ppj
  rw [dlt_mul_x, one_sub_dlt_mul_x m p d (by omega)]
  have h1 : 3 * d * (m + 1) ≤ 138 * (m + 1) := Nat.mul_le_mul_right _ (by omega)
  exact Pgen_eq hp _ _ _ (by unfold nOf; omega)

/-- `c(k/p) ≤ c_p(k)` (for odd `p`): each odd `o` with `o p ∈ (2k - 2(1+r)n, 2k + 2rn]` gives the
zero `l = (op - 2k - 1)/2` of the run with `p ∣ 2k + 1 + 2l`. -/
lemma cfun_le_cp (m p k : ℕ) (hp : Odd p) : cfun ((nOf m : ℚ) / p) ((k : ℚ) / p) ≤ cp m p k := by
  have hp0 : 0 < p := hp.pos
  have hp' : (0 : ℚ) < ((p : ℤ) : ℚ) := by exact_mod_cast hp0
  have hpZ : Odd (p : ℤ) := by exact_mod_cast hp
  unfold cfun cp
  apply Nat.mul_le_mul_left
  unfold oddCount
  have hu : 2 * ((k : ℚ) / p) + 2 * (-(1 + rr)) * ((nOf m : ℚ) / p) =
      ((2 * (k : ℤ) - 2080 * ((m : ℤ) + 1) : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    have : (p : ℚ) ≠ 0 := by positivity
    unfold rr nOf; push_cast; field_simp; ring
  have hv : 2 * ((k : ℚ) / p) + 2 * rr * ((nOf m : ℚ) / p) =
      ((2 * (k : ℤ) + 1120 * ((m : ℤ) + 1) : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    have : (p : ℚ) ≠ 0 := by positivity
    unfold rr nOf; push_cast; field_simp; ring
  rw [hu, hv]
  refine Finset.card_le_card_of_injOn (fun o : ℤ => (o * (p : ℤ) - 2 * (k : ℤ) - 1) / 2) ?_ ?_
  · intro o ho
    simp only [coe_filter, Set.mem_setOf_eq, mem_Ioc, mem_Icc] at ho ⊢
    obtain ⟨⟨h1, h2⟩, hodd⟩ := ho
    have h1' := Int.floor_lt.1 h1
    have h2' := Int.le_floor.1 h2
    rw [div_lt_iff₀ hp'] at h1'
    rw [le_div_iff₀ hp'] at h2'
    have h1z : 2 * (k : ℤ) - 2080 * ((m : ℤ) + 1) < o * p := by exact_mod_cast h1'
    have h2z : o * p ≤ 2 * (k : ℤ) + 1120 * ((m : ℤ) + 1) := by exact_mod_cast h2'
    have hw : (o * p) % 2 = 1 := Int.odd_iff.1 (hodd.mul hpZ)
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have he : 2 * (k : ℤ) + 1 + 2 * ((o * p - 2 * k - 1) / 2) = o * p := by omega
    rw [he]
    exact Dvd.intro_left o rfl
  · intro o1 ho1 o2 ho2 heq
    simp only [coe_filter, Set.mem_setOf_eq, mem_Ioc] at ho1 ho2
    have hw1 : (o1 * p) % 2 = 1 := Int.odd_iff.1 (ho1.2.mul hpZ)
    have hw2 : (o2 * p) % 2 = 1 := Int.odd_iff.1 (ho2.2.mul hpZ)
    simp only at heq
    have : o1 * p = o2 * p := by omega
    exact mul_right_cancel₀ (by exact_mod_cast hp0.ne' : (p : ℤ) ≠ 0) this

/-- `B_k ≥ 1` forces `k ≤ n`. -/
lemma le_nOf_of_Bk (m k : ℕ) (hk : 1 ≤ Bk m k) : k ≤ nOf m := by
  by_contra h
  push_neg at h
  have : Bk m k = 0 := by
    unfold Bk
    apply List.sum_eq_zero
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    rw [if_neg]
    omega
  omega

/-! ## Lemma 5, pointwise part -/

/-- **PROOF_BETA §5.1 Claim (pointwise part) for I3.** For `n = 480(m+1)`, odd `p ≤ n` and `k` with
`B_k ≥ 1`: `(B_k + 2 - c_p(k) + Σ_j m_j P_{p,j}(k)) - G ⌊n/p⌋ ≤ e*(n/p)`. -/
theorem pointwise_le_eStar (m p k : ℕ) (hp : Odd p) (hpn : p ≤ nOf m) (hk : 1 ≤ Bk m k) :
    ((Bk m k : ℚ) + 2 - (cp m p k : ℚ) +
      (((blocks.map fun b => (b.2 : ℤ) * (Ppj m p b.1 k : ℤ)).sum : ℤ) : ℚ)) -
      G * ⌊(nOf m : ℚ) / p⌋ ≤ eStar ((nOf m : ℚ) / p) := by
  have hp0 : 0 < p := hp.pos
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp0
  have hkn : k ≤ nOf m := le_nOf_of_Bk m k hk
  have hx1 : 1 ≤ (nOf m : ℚ) / p := by
    rw [le_div_iff₀ hp', one_mul]; exact_mod_cast hpn
  have hy0 : 0 ≤ (k : ℚ) / p := by positivity
  have hyx : (k : ℚ) / p ≤ (nOf m : ℚ) / p :=
    div_le_div_of_nonneg_right (by exact_mod_cast hkn) hp'.le
  refine le_trans ?_ (f_le_eStar _ _ hx1 hy0 hyx)
  unfold f
  rw [if_pos hx1, Sfun_eq_Bk m p k hp0]
  have hP : (blocks.map fun b => (b.2 : ℤ) * Pfun b.1 ((nOf m : ℚ) / p) ((k : ℚ) / p)) =
      (blocks.map fun b => (b.2 : ℤ) * (Ppj m p b.1 k : ℤ)) :=
    List.map_congr_left (fun b hb => by rw [Pfun_eq_Ppj m p b.1 k hp0 (blocks_d_le b hb)])
  rw [hP]
  have hc : (cfun ((nOf m : ℚ) / p) ((k : ℚ) / p) : ℚ) ≤ cp m p k := by
    exact_mod_cast cfun_le_cp m p k hp
  linarith

/-- The same for primes `p > 2` (in particular every prime `√𝒩 < p ≤ n` once `n ≥ 1`). -/
theorem pointwise_le_eStar_prime (m p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ nOf m)
    (hk : 1 ≤ Bk m k) :
    ((Bk m k : ℚ) + 2 - (cp m p k : ℚ) +
      (((blocks.map fun b => (b.2 : ℤ) * (Ppj m p b.1 k : ℤ)).sum : ℤ) : ℚ)) -
      G * ⌊(nOf m : ℚ) / p⌋ ≤ eStar ((nOf m : ℚ) / p) :=
  pointwise_le_eStar m p k (hp.odd_of_ne_two hp2) hpn hk

end BetaIrr.I3.CertA
