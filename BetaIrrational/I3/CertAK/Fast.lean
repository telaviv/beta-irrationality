/-
# The A-certificate for I3: a fast form of `e*` for kernel evaluation

`eStarInt x` (`I3/CertAK/Defs.lean`) is a max of `phiAt pre q1 q2 k ri right` over candidates
`(o, k, right)`. The value of `phiAt` does **not** depend on `k`: each block contributes
`m (1 + Fa - Cb)` in all three cases of `blockVal` (`blockVal_closed`), and
`Fa - Cb = flAt k ri qa - clAt k ri right qb` is independent of `k`, as is the `c`-term.
Since the threshold `k = 0` is always valid for `x ≥ 1`, `eStarInt x` is the max over the offsets
`o` and `right ∈ {false, true}` of one closed-form value each (`eStarInt_eq_F`).

The closed form `phiN` uses only `ℕ` comparisons and additions on the residues `r`, plus one
integer constant `K` per `x`, so that `decide +kernel` evaluates it quickly (the kernel has
GMP-backed `Nat` operations but none for `Int`).

Main results: `eStarInt_eq_F`, `eStar_eq_F`, `termUnits_eq_F`.
-/
import BetaIrrational.I3.CertA.Defs

namespace BetaIrr.I3.CertA

/-! ## The closed form -/

/-- `m e_b`, where `e_b ∈ {0, 1}` is the `clAt` correction of the right block end. -/
def ebN (ri rb : ℕ) (right : Bool) (m : ℕ) : ℕ :=
  if right then m else if ri = rb then 0 else m

/-- Reference implementation of `gAcc` (used only by the compiler, e.g. for `#eval`). -/
def gAccImpl (ri : ℕ) (right : Bool) : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ × ℕ
  | [], p, n => (p, n)
  | e :: l, p, n => gAccImpl ri right l (p + if ri < e.2.2 then e.1 else 0)
      (n + ((if ri < e.2.1 then e.1 else 0) + ebN ri e.2.2 right e.1))

/-- One pass over the block residues `(m, r_a, r_b)`, accumulating
`p + Σ m [ri < r_b]` and `n + Σ m ([ri < r_a] + e_b)`. Written with `List.rec` and the
`Nat` primitives so that the kernel evaluates it quickly. -/
@[implemented_by gAccImpl]
noncomputable def gAcc (ri : ℕ) (right : Bool) (l : List (ℕ × ℕ × ℕ)) : ℕ → ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ × ℕ) (fun p n => (p, n))
    (fun e _ ih p n => ih (Nat.add p (cond (Nat.blt ri e.2.2) e.1 0))
      (Nat.add n (Nat.add (cond (Nat.blt ri e.2.1) e.1 0)
        (cond right e.1 (cond (Nat.beq ri e.2.2) 0 e.1))))) l

/-- `phiAt` in closed form: `K + Σ m [ri < r_b] + 3 [ri < r_1] - Σ m ([ri < r_a] + e_b)
- 3 [ri < r_2]`. -/
def phiN (K : ℤ) (rs : List (ℕ × ℕ × ℕ)) (r1 r2 ri : ℕ) (right : Bool) : ℤ :=
  let g := gAcc ri right rs (cond (Nat.blt ri r1) 3 0) (cond (Nat.blt ri r2) 3 0)
  K + (g.1 : ℤ) - (g.2 : ℤ)

/-- The `x`-dependent integer constant of `phiN`. -/
def Kof (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) : ℤ :=
  (pre.map fun e => e.1 * (1 + e.2.2.1 - e.2.1.1)).sum + 2 + 3 * (q1.1 - q2.1)

/-- The residue data `(m, r_a, r_b)` of the blocks, as natural numbers. -/
def rsOf (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) : List (ℕ × ℕ × ℕ) :=
  pre.map fun e => (e.1.toNat, e.2.1.2.toNat, e.2.2.2.toNat)

/-- Fast `eStarInt` (equal to it for `x ≥ 1`, `eStarInt_eq_F`). -/
def eStarIntF (x : ℚ) : ℤ :=
  let P := x.num
  let Q : ℤ := x.den
  let pre := preOf P Q
  let q1 := qrOf P Q c1Off
  let q2 := qrOf P Q c2Off
  let K := Kof pre q1 q2
  let rs := rsOf pre
  let r1 := q1.2.toNat
  let r2 := q2.2.toNat
  offsets.foldl (fun acc o =>
      let ri := (qrOf P Q o).2.toNat
      max (max acc (phiN K rs r1 r2 ri false)) (phiN K rs r1 r2 ri true))
    (phiN K rs r1 r2 0 false)

/-- Fast `eStar`. -/
def eStarF (x : ℚ) : ℚ := if 1 ≤ x then (eStarIntF x : ℚ) - G * ⌊x⌋ else 0

/-- Fast `termUnits`. -/
def termUnitsF (a b : ℚ) : ℤ := ⌈eStarF ((a + b) / 2) * (1 / a - 1 / b) * 2 ^ 96⌉

/-! ## `phiAt` does not depend on `k` -/

lemma blockVal_closed (m Fa Ca Fb Cb : ℤ) (ha : Ca = Fa ∨ Ca = Fa + 1)
    (hb : Cb = Fb ∨ Cb = Fb + 1) : blockVal m Fa Ca Fb Cb = m * (1 + Fa - Cb) := by
  unfold blockVal
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> split_ifs <;>
    first | ring1 | (exfalso; omega)

lemma clAt_cases (k ri : ℤ) (right : Bool) (ql : ℤ × ℤ) :
    clAt k ri right ql = flAt k ri ql ∨ clAt k ri right ql = flAt k ri ql + 1 := by
  unfold clAt; split_ifs <;> simp

lemma phiAt_closed (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (k ri : ℤ)
    (right : Bool) :
    phiAt pre q1 q2 k ri right =
      (pre.map fun e => e.1 * (1 + flAt k ri e.2.1 - clAt k ri right e.2.2)).sum + 2
        - 3 * (flAt k ri q1 - flAt k ri q2) := by
  unfold phiAt
  congr 3
  apply List.map_congr_left
  intro e _
  exact blockVal_closed _ _ _ _ _ (clAt_cases _ _ _ _) (clAt_cases _ _ _ _)

/-! ## The closed form `phiN` -/

lemma gAcc_spec (ri : ℕ) (right : Bool) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (p n : ℕ), gAcc ri right l p n =
      (p + (l.map fun e => if ri < e.2.2 then e.1 else 0).sum,
       n + (l.map fun e => (if ri < e.2.1 then e.1 else 0) + ebN ri e.2.2 right e.1).sum)
  | [], p, n => by simp [gAcc]
  | e :: l, p, n => by
    have ih := gAcc_spec ri right l
    change gAcc ri right l _ _ = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq, Nat.add_eq, Bool.cond_eq_ite,
      Nat.blt_eq, Nat.beq_eq, ebN]
    constructor <;> split_ifs <;> omega

/-- The contribution of one block, in the `ℕ` form. -/
lemma block_term (k ri : ℤ) (right : Bool) (e : ℤ × (ℤ × ℤ) × (ℤ × ℤ)) (hm : 0 ≤ e.1)
    (ha : 0 ≤ e.2.1.2) (hb : 0 ≤ e.2.2.2) (hri : 0 ≤ ri) :
    e.1 * (1 + flAt k ri e.2.1 - clAt k ri right e.2.2) =
      e.1 * (1 + e.2.2.1 - e.2.1.1) +
        ((if ri.toNat < e.2.2.2.toNat then e.1.toNat else 0 : ℕ) : ℤ) -
        (((if ri.toNat < e.2.1.2.toNat then e.1.toNat else 0) +
          ebN ri.toNat e.2.2.2.toNat right e.1.toNat : ℕ) : ℤ) := by
  obtain ⟨m, ⟨qa, ra⟩, ⟨qb, rb⟩⟩ := e
  simp only at hm ha hb ⊢
  lift m to ℕ using hm
  lift ra to ℕ using ha
  lift rb to ℕ using hb
  lift ri to ℕ using hri
  simp only [flAt, clAt, ebN, Int.toNat_natCast, Nat.cast_lt, Nat.cast_inj]
  cases right <;> split_ifs <;> push_cast <;> ring

lemma sum_block_terms (k ri : ℤ) (right : Bool) (hri : 0 ≤ ri) :
    ∀ (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))),
      (∀ e ∈ pre, 0 ≤ e.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.2) →
      (pre.map fun e => e.1 * (1 + flAt k ri e.2.1 - clAt k ri right e.2.2)).sum =
        (pre.map fun e => e.1 * (1 + e.2.2.1 - e.2.1.1)).sum +
          (((rsOf pre).map fun e => if ri.toNat < e.2.2 then e.1 else 0).sum : ℕ) -
          (((rsOf pre).map fun e =>
            (if ri.toNat < e.2.1 then e.1 else 0) + ebN ri.toNat e.2.2 right e.1).sum : ℕ)
  | [], _ => by simp [rsOf]
  | e :: pre, h => by
    have ih := sum_block_terms k ri right hri pre (fun e he => h e (List.mem_cons_of_mem _ he))
    have he := h e List.mem_cons_self
    have hb := block_term k ri right e he.1 he.2.1 he.2.2 hri
    simp only [rsOf] at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    push_cast at ih hb ⊢
    rw [hb, ih]
    ring

lemma phiAt_eq_phiN (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (k ri : ℤ)
    (right : Bool) (hpre : ∀ e ∈ pre, 0 ≤ e.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.2)
    (h1 : 0 ≤ q1.2) (h2 : 0 ≤ q2.2) (hri : 0 ≤ ri) :
    phiAt pre q1 q2 k ri right =
      phiN (Kof pre q1 q2) (rsOf pre) q1.2.toNat q2.2.toNat ri.toNat right := by
  rw [phiAt_closed, sum_block_terms k ri right hri pre hpre]
  simp only [phiN, gAcc_spec, Kof, Bool.cond_eq_ite, Nat.blt_eq]
  obtain ⟨a1, r1⟩ := q1
  obtain ⟨a2, r2⟩ := q2
  simp only at h1 h2 ⊢
  lift r1 to ℕ using h1
  lift r2 to ℕ using h2
  lift ri to ℕ using hri
  simp only [flAt, Int.toNat_natCast, Nat.cast_lt]
  split_ifs <;> push_cast <;> ring

/-! ## The folds over thresholds collapse -/

lemma phiAt_indep (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (k ri : ℤ)
    (right : Bool) : phiAt pre q1 q2 k ri right = phiAt pre q1 q2 0 ri right := by
  rw [phiAt_closed, phiAt_closed]
  have h1 : ∀ ql : ℤ × ℤ, flAt k ri ql = k + flAt 0 ri ql := fun ql => by
    unfold flAt; ring
  have h2 : ∀ ql : ℤ × ℤ, clAt k ri right ql = k + clAt 0 ri right ql := fun ql => by
    unfold clAt; rw [h1]; split_ifs <;> ring
  have h3 : ∀ e : ℤ × (ℤ × ℤ) × (ℤ × ℤ),
      e.1 * (1 + (k + flAt 0 ri e.2.1) - (k + clAt 0 ri right e.2.2)) =
        e.1 * (1 + flAt 0 ri e.2.1 - clAt 0 ri right e.2.2) := fun e => by ring
  simp only [h1, h2, h3]
  ring

lemma foldl_candStep_const (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ)
    (qX rX ri : ℤ) (right : Bool) :
    ∀ (l : List ℤ) (acc : ℤ), phiAt pre q1 q2 0 ri right ≤ acc →
      l.foldl (candStep pre q1 q2 qX rX ri right) acc = acc
  | [], _, _ => rfl
  | k :: l, acc, h => by
    rw [List.foldl_cons]
    have : candStep pre q1 q2 qX rX ri right acc k = acc := by
      unfold candStep
      rw [phiAt_indep]
      split_ifs
      · exact max_eq_left h
      · rfl
    rw [this]
    exact foldl_candStep_const pre q1 q2 qX rX ri right l acc h

lemma foldl_thresholds (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ)
    (qX rX ri : ℤ) (right : Bool) (hqX : 0 < qX) (acc : ℤ) :
    (thresholds pre ri right).foldl (candStep pre q1 q2 qX rX ri right) acc =
      max acc (phiAt pre q1 q2 0 ri right) := by
  have hv : valid qX rX ri 0 right = true := by
    unfold valid; simp [hqX]
  change List.foldl _ (candStep pre q1 q2 qX rX ri right acc 0) _ = _
  have h0 : candStep pre q1 q2 qX rX ri right acc 0 = max acc (phiAt pre q1 q2 0 ri right) := by
    unfold candStep; rw [hv]; rfl
  rw [h0]
  exact foldl_candStep_const _ _ _ _ _ _ _ _ _ (le_max_right _ _)

/-! ## `eStarInt = eStarIntF` for `x ≥ 1` -/

lemma qrOf_snd_nonneg (P Q : ℤ) (hQ : 0 < Q) (o : ℤ × ℤ) : 0 ≤ (qrOf P Q o).2 := by
  unfold qrOf
  exact Int.emod_nonneg _ (by omega)

lemma preOf_nonneg (P Q : ℤ) (hQ : 0 < Q) :
    ∀ e ∈ preOf P Q, 0 ≤ e.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.2 := by
  intro e he
  unfold preOf at he
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 he
  exact ⟨by positivity, qrOf_snd_nonneg P Q hQ _, qrOf_snd_nonneg P Q hQ _⟩

lemma num_div_den_pos (x : ℚ) (hx : 1 ≤ x) : 0 < x.num / (x.den : ℤ) := by
  have hd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  have hle : (x.den : ℤ) ≤ x.num := by
    have h := x.num_div_den
    have hdq : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
    have : (x.den : ℚ) ≤ x.num := by
      rw [← h] at hx
      rwa [le_div_iff₀ hdq, one_mul] at hx
    exact_mod_cast this
  exact lt_of_lt_of_le one_pos (Int.le_ediv_of_mul_le hd (by simpa using hle))

theorem eStarInt_eq_F (x : ℚ) (hx : 1 ≤ x) : eStarInt x = eStarIntF x := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  have hqX := num_div_den_pos x hx
  have hpre := preOf_nonneg x.num x.den hQ
  have h1 := qrOf_snd_nonneg x.num x.den hQ c1Off
  have h2 := qrOf_snd_nonneg x.num x.den hQ c2Off
  unfold eStarInt eStarIntF
  simp only
  rw [phiAt_eq_phiN _ _ _ _ _ _ hpre h1 h2 le_rfl]
  apply List.foldl_ext
  intro acc o _
  rw [foldl_thresholds _ _ _ _ _ _ _ hqX, foldl_thresholds _ _ _ _ _ _ _ hqX,
    phiAt_eq_phiN _ _ _ _ _ _ hpre h1 h2 (qrOf_snd_nonneg _ _ hQ o),
    phiAt_eq_phiN _ _ _ _ _ _ hpre h1 h2 (qrOf_snd_nonneg _ _ hQ o)]

theorem eStar_eq_F (x : ℚ) : eStar x = eStarF x := by
  unfold eStar eStarF
  split_ifs with h
  · rw [eStarInt_eq_F x h]
  · rfl

theorem termUnits_eq_F : termUnits = termUnitsF := by
  funext a b
  unfold termUnits termUnitsF
  rw [eStar_eq_F]

end BetaIrr.I3.CertA
