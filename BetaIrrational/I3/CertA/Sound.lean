/-
# The A-certificate for instance I3: soundness of the computable `e*`

The scaling is `M = 960 Q`.

`PROOF_BETA.md` §5.1. We prove that the computable `eStar x` of `I3/CertA/Defs.lean`
bounds `f x y` for every `0 ≤ y ≤ x` (`x ≥ 1`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.CertA.Defs

namespace BetaIrr.I3.CertA

open Finset

/-! ## Floor/ceiling bookkeeping -/

lemma floor_eq_ceil_iff_fract (z : ℚ) : ⌊z⌋ = ⌈z⌉ ↔ Int.fract z = 0 := by
  rw [Int.fract_eq_zero_iff]
  constructor
  · intro h
    have h1 := Int.floor_le z
    have h2 := Int.le_ceil z
    rw [← h] at h2
    exact ⟨⌊z⌋, le_antisymm h1 h2⟩
  · rintro ⟨n, rfl⟩
    simp

lemma floor_eq_ceil_iff_fract_neg (z : ℚ) : ⌊z⌋ = ⌈z⌉ ↔ Int.fract (-z) = 0 := by
  rw [← floor_eq_ceil_iff_fract, Int.floor_neg, Int.ceil_neg]
  omega

lemma offVal_aOff (x : ℚ) (d : ℕ) : offVal x (aOff d) = dlt d * x := by
  simp only [offVal, aOff, dlt]; push_cast; ring

lemma offVal_bOff (x : ℚ) (d : ℕ) : offVal x (bOff d) = (1 - dlt d) * x := by
  simp only [offVal, bOff, dlt]; push_cast; ring

/-- One block: `blockVal` of the floor data is `m [in block] + m P_j`. -/
lemma blockVal_eq (m d : ℕ) (x y : ℚ) :
    blockVal m ⌊y - offVal x (aOff d)⌋ ⌈y - offVal x (aOff d)⌉ ⌊y - offVal x (bOff d)⌋
        ⌈y - offVal x (bOff d)⌉ =
      ((if dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x then m else 0 : ℕ) : ℤ) + m * Pfun d x y := by
  unfold blockVal Pfun
  rw [offVal_aOff, offVal_bOff]
  set a := dlt d * x
  set b := (1 - dlt d) * x
  have h1 : 0 ≤ ⌊y - a⌋ ↔ a ≤ y := by rw [Int.floor_nonneg, sub_nonneg]
  have h2 : ⌈y - b⌉ ≤ 0 ↔ y ≤ b := by
    rw [Int.ceil_le]; simp
  have h3 : ⌊y - a⌋ < 0 ↔ y < a := by
    rw [Int.floor_lt]; simp
  have h4 : ⌊b - y⌋ = -⌈y - b⌉ := by rw [show b - y = -(y - b) by ring, Int.floor_neg]
  have h5 : ⌊a - y⌋ = -⌈y - a⌉ := by rw [show a - y = -(y - a) by ring, Int.floor_neg]
  have h6 : ⌊y - a⌋ = ⌈y - a⌉ ↔ Int.fract (a - y) = 0 := by
    rw [floor_eq_ceil_iff_fract_neg, neg_sub]
  have h7 : ⌊y - b⌋ = ⌈y - b⌉ ↔ Int.fract (y - b) = 0 := floor_eq_ceil_iff_fract _
  simp only [h1, h2, h3, h4, h5, h6, h7]
  split_ifs <;> push_cast <;> ring

/-- The number of odd integers in `(u, v]`. -/
lemma oddCount_eq (u v : ℚ) (h : u ≤ v) :
    (oddCount u v : ℤ) = ⌊(v + 1) / 2⌋ - ⌊(u + 1) / 2⌋ := by
  have hfl : ∀ w : ℚ, ⌊(w + 1) / 2⌋ = ⌊((⌊w⌋ : ℚ) - 1) / 2⌋ + 1 := by
    intro w
    have e1 : ⌊(w + 1) / 2⌋ = (⌊w⌋ + 1) / 2 := by
      have := Int.floor_div_natCast (w + 1) 2
      push_cast at this
      rw [this, Int.floor_add_one]
    have e2 : ⌊((⌊w⌋ : ℚ) - 1) / 2⌋ = (⌊w⌋ - 1) / 2 := by
      have := Int.floor_div_natCast (((⌊w⌋ - 1 : ℤ)) : ℚ) 2
      push_cast at this
      rw [this, ← Int.cast_one, ← Int.cast_sub, Int.floor_intCast]
    rw [e1, e2]
    omega
  have hcard : oddCount u v = #{z ∈ Ioc ⌊u⌋ ⌊v⌋ | z ≡ 1 [ZMOD 2]} := by
    unfold oddCount
    congr 1
    apply Finset.filter_congr
    intro z _
    simp [Int.odd_iff, Int.ModEq]
  rw [hcard, Int.Ioc_filter_modEq_card _ _ (by norm_num : (0 : ℤ) < 2)]
  push_cast
  rw [hfl v, hfl u]
  have hm : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_le_floor h
  have hm2 : ⌊((⌊u⌋ : ℚ) - 1) / 2⌋ ≤ ⌊((⌊v⌋ : ℚ) - 1) / 2⌋ := by
    apply Int.floor_le_floor
    have : (⌊u⌋ : ℚ) ≤ ⌊v⌋ := by exact_mod_cast hm
    linarith
  omega

lemma offVal_c1 (x : ℚ) : offVal x c1Off = -rr * x - 1 / 2 := by
  simp only [offVal, c1Off, rr]; push_cast; ring

lemma offVal_c2 (x : ℚ) : offVal x c2Off = (1 + rr) * x - 1 / 2 := by
  simp only [offVal, c2Off, rr]; push_cast; ring

lemma cfun_eq (x y : ℚ) (hx : 0 ≤ x) :
    (cfun x y : ℤ) = 3 * (⌊y - offVal x c1Off⌋ - ⌊y - offVal x c2Off⌋) := by
  unfold cfun
  push_cast
  rw [oddCount_eq _ _ (by unfold rr; nlinarith), offVal_c1, offVal_c2]
  congr 2
  · congr 1; ring
  · congr 1; ring

lemma Sfun_cast (x y : ℚ) :
    (Sfun x y : ℤ) = (blocks.map fun b =>
      ((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)).sum := by
  unfold Sfun
  rw [Nat.cast_list_sum, List.map_map]
  rfl

/-- **The floor-data form of `f`.** -/
lemma f_eq_Phi (x y : ℚ) (hx : 1 ≤ x) :
    f x y = (Phi (fun o => ⌊y - offVal x o⌋) (fun o => ⌈y - offVal x o⌉) : ℚ) - G * ⌊x⌋ := by
  unfold f Phi
  rw [if_pos hx]
  have hsum : (blocks.map fun b => blockVal b.2 ⌊y - offVal x (aOff b.1)⌋ ⌈y - offVal x (aOff b.1)⌉
      ⌊y - offVal x (bOff b.1)⌋ ⌈y - offVal x (bOff b.1)⌉).sum =
      (Sfun x y : ℤ) + (blocks.map fun b => (b.2 : ℤ) * Pfun b.1 x y).sum := by
    rw [Sfun_cast, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro b _
    exact blockVal_eq b.2 b.1 x y
  have hc := cfun_eq x y (by linarith)
  have hS : ((Sfun x y : ℤ) : ℚ) = (Sfun x y : ℚ) := by norm_cast
  have hc' : ((cfun x y : ℤ) : ℚ) = (cfun x y : ℚ) := by norm_cast
  push_cast [hsum]
  rw [← hc', hc]
  push_cast
  ring


/-! ## Integer scaling -/

lemma floor_div_eq (N M a : ℤ) (hM : 0 < M) (h1 : a * M ≤ N) (h2 : N < (a + 1) * M) :
    ⌊(N : ℚ) / M⌋ = a := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  rw [Int.floor_eq_iff, le_div_iff₀ hM', div_lt_iff₀ hM']
  constructor <;> exact_mod_cast (by linarith)

lemma ceil_div_eq (N M a : ℤ) (hM : 0 < M) (h1 : (a - 1) * M < N) (h2 : N ≤ a * M) :
    ⌈(N : ℚ) / M⌉ = a := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  rw [Int.ceil_eq_iff, lt_div_iff₀ hM', div_le_iff₀ hM']
  constructor <;> exact_mod_cast (by linarith)

/-- `x = P/Q`, `M = 960 Q`: the scaled offset. -/
lemma offVal_scaled (x : ℚ) (o : ℤ × ℤ) :
    offVal x o = ((2 * o.1 * x.num + 480 * o.2 * (x.den : ℤ) : ℤ) : ℚ) / ((960 * (x.den : ℤ) : ℤ) : ℚ) := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = x.num / x.den := (Rat.num_div_den x).symm
  unfold offVal
  conv_lhs => rw [hx]
  push_cast
  field_simp
  ring

lemma qrOf_spec (P Q : ℤ) (hQ : 0 < Q) (o : ℤ × ℤ) :
    2 * o.1 * P + 480 * o.2 * Q = (qrOf P Q o).1 * (960 * Q) + (qrOf P Q o).2 ∧
      0 ≤ (qrOf P Q o).2 ∧ (qrOf P Q o).2 < 960 * Q := by
  unfold qrOf
  simp only
  refine ⟨?_, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have := Int.emod_add_ediv_mul (2 * o.1 * P + 480 * o.2 * Q) (960 * Q)
  linarith

/-- The candidate point `y = k + r_i / M`. -/
def candY (x : ℚ) (k ri : ℤ) : ℚ := (k : ℚ) + (ri : ℚ) / ((960 * (x.den : ℤ) : ℤ) : ℚ)

lemma candY_sub (x : ℚ) (k ri : ℤ) (o : ℤ × ℤ) :
    candY x k ri - offVal x o =
      (((k - (qrOf x.num x.den o).1) * (960 * (x.den : ℤ)) + ri - (qrOf x.num x.den o).2 : ℤ) : ℚ)
        / ((960 * (x.den : ℤ) : ℤ) : ℚ) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨h1, -, -⟩ := qrOf_spec x.num x.den hQ o
  have hM : ((960 * (x.den : ℤ) : ℤ) : ℚ) ≠ 0 := by
    have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
    push_cast; positivity
  rw [offVal_scaled, h1, candY]
  field_simp
  push_cast
  ring

lemma floor_candY (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 960 * x.den) (o : ℤ × ℤ) :
    ⌊candY x k ri - offVal x o⌋ = flAt k ri (qrOf x.num x.den o) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  rw [candY_sub, flAt]
  set q := (qrOf x.num x.den o).1
  set r := (qrOf x.num x.den o).2
  rcases lt_or_ge ri r with h | h
  · rw [if_pos h]
    apply floor_div_eq _ _ _ (by omega) <;> nlinarith
  · rw [if_neg (not_lt.2 h)]
    apply floor_div_eq _ _ _ (by omega) <;> nlinarith

lemma ceil_candY (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 960 * x.den) (o : ℤ × ℤ) :
    ⌈candY x k ri - offVal x o⌉ = clAt k ri false (qrOf x.num x.den o) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  rw [candY_sub, clAt, flAt]
  set q := (qrOf x.num x.den o).1
  set r := (qrOf x.num x.den o).2
  simp only [Bool.false_eq_true, if_false]
  rcases lt_trichotomy ri r with h | h | h
  · rw [if_pos h, if_neg (ne_of_lt h)]
    apply ceil_div_eq _ _ _ (by omega) <;> nlinarith
  · rw [if_neg (by omega), if_pos h]
    apply ceil_div_eq _ _ _ (by omega) <;> nlinarith
  · rw [if_neg (not_lt.2 h.le), if_neg (ne_of_gt h)]
    apply ceil_div_eq _ _ _ (by omega) <;> nlinarith

/-! ## `phiAt` is `Phi` at a candidate -/

lemma phiAt_eq_Phi (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 960 * x.den) (right : Bool) :
    phiAt (preOf x.num x.den) (qrOf x.num x.den c1Off) (qrOf x.num x.den c2Off) k ri right =
      Phi (fun o => ⌊candY x k ri - offVal x o⌋)
        (fun o => if right then ⌊candY x k ri - offVal x o⌋ + 1
          else ⌈candY x k ri - offVal x o⌉) := by
  unfold phiAt Phi preOf
  rw [List.map_map]
  simp only [floor_candY x k ri h0 hM]
  cases right
  · simp only [Bool.false_eq_true, if_false, ceil_candY x k ri h0 hM]
    rfl
  · simp only [if_true, clAt]
    rfl

lemma aOff_mem (b : ℕ × ℕ) (hb : b ∈ blocks) : aOff b.1 ∈ offsets :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, hb, by simp⟩))

lemma bOff_mem (b : ℕ × ℕ) (hb : b ∈ blocks) : bOff b.1 ∈ offsets :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, hb, by simp⟩))

lemma c1Off_mem : c1Off ∈ offsets := List.mem_cons_self
lemma c2Off_mem : c2Off ∈ offsets := List.mem_cons_of_mem _ List.mem_cons_self

lemma Phi_congr (F C F' C' : ℤ × ℤ → ℤ) (hF : ∀ o ∈ offsets, F o = F' o)
    (hC : ∀ o ∈ offsets, C o = C' o) : Phi F C = Phi F' C' := by
  unfold Phi
  rw [hF _ c1Off_mem, hF _ c2Off_mem]
  congr 3
  apply List.map_congr_left
  intro b hb
  rw [hF _ (aOff_mem b hb), hC _ (aOff_mem b hb), hF _ (bOff_mem b hb), hC _ (bOff_mem b hb)]

/-! ## Folds -/

section Fold
variable {α : Type*}

lemma foldl_step_ge (step : ℤ → α → ℤ) (hstep : ∀ acc a, acc ≤ step acc a) :
    ∀ (l : List α) (init : ℤ), init ≤ l.foldl step init
  | [], _ => le_rfl
  | a :: l, init => (hstep init a).trans (foldl_step_ge step hstep l _)

lemma foldl_mem_ge (step : ℤ → α → ℤ) (hstep : ∀ acc a, acc ≤ step acc a) (v : ℤ) (a₀ : α)
    (hv : ∀ acc, v ≤ step acc a₀) :
    ∀ (l : List α) (init : ℤ), a₀ ∈ l → v ≤ l.foldl step init
  | [], _, h => by simp at h
  | a :: l, init, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (hv init).trans (foldl_step_ge step hstep l _)
    · exact foldl_mem_ge step hstep v a₀ hv l _ h

end Fold

lemma candStep_ge (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (qX rX ri : ℤ)
    (right : Bool) (acc k : ℤ) : acc ≤ candStep pre q1 q2 qX rX ri right acc k := by
  unfold candStep; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma candStep_val (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (qX rX ri : ℤ)
    (right : Bool) (k : ℤ) (hv : valid qX rX ri k right = true) (acc : ℤ) :
    phiAt pre q1 q2 k ri right ≤ candStep pre q1 q2 qX rX ri right acc k := by
  unfold candStep; rw [if_pos hv]; exact le_max_right _ _

lemma le_eStarInt (x : ℚ) (o : ℤ × ℤ) (ho : o ∈ offsets) (right : Bool) (t : ℤ)
    (ht : t ∈ thresholds (preOf x.num x.den) (qrOf x.num x.den o).2 right)
    (hv : valid (x.num / x.den) (960 * (x.num % x.den)) (qrOf x.num x.den o).2 t right = true) :
    phiAt (preOf x.num x.den) (qrOf x.num x.den c1Off) (qrOf x.num x.den c2Off) t
      (qrOf x.num x.den o).2 right ≤ eStarInt x := by
  unfold eStarInt
  dsimp only
  apply foldl_mem_ge _ _ _ o _ offsets _ ho
  · intro acc o'
    exact (foldl_step_ge _ (candStep_ge _ _ _ _ _ _ _) _ _).trans
      (foldl_step_ge _ (candStep_ge _ _ _ _ _ _ _) _ _)
  · intro acc
    cases right
    · exact (foldl_mem_ge _ (candStep_ge _ _ _ _ _ _ _) _ t (candStep_val _ _ _ _ _ _ _ t hv)
        _ _ ht).trans (foldl_step_ge _ (candStep_ge _ _ _ _ _ _ _) _ _)
    · exact foldl_mem_ge _ (candStep_ge _ _ _ _ _ _ _) _ t (candStep_val _ _ _ _ _ _ _ t hv)
        _ _ ht

/-! ## Thresholds -/

lemma valid_mono (qX rX ri k t : ℤ) (right : Bool) (hv : valid qX rX ri k right = true)
    (ht0 : 0 ≤ t) (htk : t ≤ k) : valid qX rX ri t right = true := by
  unfold valid at *
  cases right <;> simp at hv ⊢ <;> omega

lemma blockVal_shift (m α β ca cb t k : ℤ) (hα : α ≤ t ↔ α ≤ k)
    (hβ : β - cb + 1 ≤ t ↔ β - cb + 1 ≤ k) :
    blockVal m (t - α) (t - α + ca) (t - β) (t - β + cb) =
      blockVal m (k - α) (k - α + ca) (k - β) (k - β + cb) := by
  unfold blockVal
  have e1 : (0 ≤ t - α ∧ t - β + cb ≤ 0) ↔ (0 ≤ k - α ∧ k - β + cb ≤ 0) := by omega
  have e2 : t - α < 0 ↔ k - α < 0 := by omega
  have e3 : t - α = t - α + ca ↔ k - α = k - α + ca := by omega
  have e4 : t - β = t - β + cb ↔ k - β = k - β + cb := by omega
  simp only [e1, e2, e3, e4]
  split_ifs <;> ring

lemma phiAt_threshold (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (ri : ℤ)
    (right : Bool) (t k : ℤ) (h : ∀ u ∈ thresholds pre ri right, u ≤ t ↔ u ≤ k) :
    phiAt pre q1 q2 t ri right = phiAt pre q1 q2 k ri right := by
  unfold phiAt
  have hmap : (pre.map fun e => blockVal e.1 (flAt t ri e.2.1) (clAt t ri right e.2.1)
      (flAt t ri e.2.2) (clAt t ri right e.2.2)) =
      (pre.map fun e => blockVal e.1 (flAt k ri e.2.1) (clAt k ri right e.2.1)
      (flAt k ri e.2.2) (clAt k ri right e.2.2)) := by
    apply List.map_congr_left
    intro e he
    have hmem : ∀ u ∈ [e.2.1.1 + (if ri < e.2.1.2 then 1 else 0),
        e.2.2.1 + (if ri < e.2.2.2 then 1 else 0) + 1 -
          (if right then 1 else if ri = e.2.2.2 then 0 else 1)], u ≤ t ↔ u ≤ k := by
      intro u hu
      exact h u (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨e, he, hu⟩))
    have hA := hmem _ List.mem_cons_self
    have hB := hmem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have key := blockVal_shift e.1 (e.2.1.1 + (if ri < e.2.1.2 then 1 else 0))
      (e.2.2.1 + (if ri < e.2.2.2 then 1 else 0))
      (if right then 1 else if ri = e.2.1.2 then 0 else 1)
      (if right then 1 else if ri = e.2.2.2 then 0 else 1) t k hA (by
        have : e.2.2.1 + (if ri < e.2.2.2 then 1 else 0) -
            (if right then 1 else if ri = e.2.2.2 then 0 else 1) + 1 =
          e.2.2.1 + (if ri < e.2.2.2 then 1 else 0) + 1 -
            (if right then 1 else if ri = e.2.2.2 then 0 else 1) := by ring
        rw [this]; exact hB)
    have ef : ∀ s : ℤ, ∀ ql : ℤ × ℤ, flAt s ri ql = s - (ql.1 + if ri < ql.2 then 1 else 0) := by
      intro s ql; unfold flAt; ring
    have ec : ∀ s : ℤ, ∀ ql : ℤ × ℤ, clAt s ri right ql =
        s - (ql.1 + if ri < ql.2 then 1 else 0) +
          (if right then 1 else if ri = ql.2 then 0 else 1) := by
      intro s ql; unfold clAt; rw [ef]; cases right <;> simp
    rw [ef t, ec t, ef t, ec t, ef k, ec k, ef k, ec k]
    exact key
  have hrun : flAt t ri q1 - flAt t ri q2 = flAt k ri q1 - flAt k ri q2 := by
    simp only [flAt]; ring
  rw [hmap, hrun]

lemma exists_threshold (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (qX rX ri : ℤ)
    (right : Bool) (k : ℤ) (hk : valid qX rX ri k right = true) :
    ∃ t ∈ thresholds pre ri right, valid qX rX ri t right = true ∧
      phiAt pre q1 q2 t ri right = phiAt pre q1 q2 k ri right := by
  have hk0 : 0 ≤ k := by
    unfold valid at hk; simp at hk; exact hk.1
  set T := thresholds pre ri right
  have h0T : (0 : ℤ) ∈ T := List.mem_cons_self
  set Sset := T.toFinset.filter (fun u => 0 ≤ u ∧ u ≤ k)
  have hne : Sset.Nonempty := ⟨0, by simp [Sset, h0T, hk0]⟩
  obtain ⟨t, htS, hmax⟩ := Sset.exists_max_image id hne
  simp only [Sset, Finset.mem_filter, List.mem_toFinset] at htS
  obtain ⟨htT, ht0, htk⟩ := htS
  refine ⟨t, htT, valid_mono _ _ _ _ _ _ hk ht0 htk, ?_⟩
  apply phiAt_threshold
  intro u hu
  constructor
  · intro h; exact h.trans htk
  · intro h
    by_cases hu0 : 0 ≤ u
    · exact hmax u (by
        simp only [Sset, Finset.mem_filter, List.mem_toFinset]; exact ⟨hu, hu0, h⟩)
    · omega


/-! ## Validity of the candidate below `y` -/

lemma candY_eq (x : ℚ) (k ri : ℤ) :
    candY x k ri = ((k * (960 * (x.den : ℤ)) + ri : ℤ) : ℚ) / ((960 * (x.den : ℤ) : ℤ) : ℚ) := by
  have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
  unfold candY
  field_simp
  push_cast
  ring

lemma x_eq_scaled (x : ℚ) :
    x = ((960 * x.num : ℤ) : ℚ) / ((960 * (x.den : ℤ) : ℤ) : ℚ) := by
  have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
  conv_lhs => rw [← Rat.num_div_den x]
  field_simp
  push_cast
  ring

lemma valid_int (P Q M k ri : ℤ) (hQ : 0 < Q) (hMdef : M = 960 * Q) (h0 : 0 ≤ ri) (hM : ri < M)
    (hk : 0 ≤ k * M + ri) (right : Bool)
    (hle : if right then k * M + ri < 960 * P else k * M + ri ≤ 960 * P) :
    valid (P / Q) (960 * (P % Q)) ri k right = true := by
  have hPQ := Int.emod_add_ediv_mul P Q
  have hr0 : 0 ≤ P % Q := Int.emod_nonneg _ (by omega)
  have hrQ : P % Q < Q := Int.emod_lt_of_pos _ hQ
  have hX : 960 * P = (P / Q) * M + 960 * (P % Q) := by subst hMdef; linarith
  have hMpos : 0 < M := by omega
  have hle' : k * M + ri ≤ 960 * P := by cases right <;> simp at hle <;> omega
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have : (k + 1) * M ≤ 0 := by nlinarith
    nlinarith
  have hkq : k ≤ P / Q := by
    by_contra hgt
    have : (P / Q + 1) * M ≤ k * M := by
      apply mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  rcases lt_or_eq_of_le hkq with hlt | heq
  · unfold valid; simp [hk0, hlt]
  · have hfin : if right then ri < 960 * (P % Q) else ri ≤ 960 * (P % Q) := by
      rw [heq] at hle
      cases right <;> simp at hle ⊢ <;> linarith
    have hq0 : 0 ≤ P / Q := heq ▸ hk0
    unfold valid
    cases right <;> simp at hfin ⊢ <;> simp [hq0, heq, hfin]

lemma valid_of_le (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 960 * x.den)
    (hk : 0 ≤ candY x k ri) (right : Bool)
    (hle : if right then candY x k ri < x else candY x k ri ≤ x) :
    valid (x.num / x.den) (960 * (x.num % x.den)) ri k right = true := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  have hMq : (0 : ℚ) < ((960 * (x.den : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast (by omega : (0 : ℤ) < 960 * x.den)
  have hxM : x * ((960 * (x.den : ℤ) : ℤ) : ℚ) = ((960 * x.num : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  rw [candY_eq] at hk hle
  apply valid_int x.num x.den (960 * x.den) k ri hQ rfl h0 hM _ right
  · cases right
    · simp only [Bool.false_eq_true, if_false] at hle ⊢
      rw [div_le_iff₀ hMq, hxM] at hle
      exact_mod_cast hle
    · simp only [if_true] at hle ⊢
      rw [div_lt_iff₀ hMq, hxM] at hle
      exact_mod_cast hle
  · rw [le_div_iff₀ hMq, zero_mul] at hk
    exact_mod_cast hk

/-! ## Main soundness theorem -/

/-- **`e*` bounds `f`.** For `x ≥ 1` and every `0 ≤ y ≤ x`, `f(x, y) ≤ e*(x)`. -/
theorem f_le_eStar (x y : ℚ) (hx : 1 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ x) : f x y ≤ eStar x := by
  rw [f_eq_Phi x y hx, eStar, if_pos hx]
  suffices h : Phi (fun o => ⌊y - offVal x o⌋) (fun o => ⌈y - offVal x o⌉) ≤ eStarInt x by
    have : ((Phi (fun o => ⌊y - offVal x o⌋) (fun o => ⌈y - offVal x o⌉) : ℤ) : ℚ) ≤
        (eStarInt x : ℚ) := by exact_mod_cast h
    linarith
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  -- the largest breakpoint `≤ y`
  set bv : ℤ × ℤ → ℚ := fun o => offVal x o + ⌊y - offVal x o⌋ with hbv
  have hmem0 : aOff 0 ∈ offsets.toFinset := by
    rw [List.mem_toFinset]; exact aOff_mem (0, 8) (by simp [blocks])
  obtain ⟨o, ho, hmax⟩ := offsets.toFinset.exists_max_image bv ⟨aOff 0, hmem0⟩
  rw [List.mem_toFinset] at ho
  have hmax' : ∀ o' ∈ offsets, bv o' ≤ bv o := fun o' h' => hmax o' (List.mem_toFinset.2 h')
  set j := ⌊y - offVal x o⌋
  set b := bv o
  have hb_le : b ≤ y := by
    have := Int.floor_le (y - offVal x o)
    simp only [b, bv]; linarith
  have hb0 : 0 ≤ b := by
    have h1 := hmax' (aOff 0) (List.mem_toFinset.1 hmem0)
    have h2 : bv (aOff 0) = ⌊y⌋ := by
      simp only [bv, offVal_aOff, dlt]; simp
    have h3 : (0 : ℚ) ≤ ⌊y⌋ := by exact_mod_cast Int.floor_nonneg.2 hy0
    linarith
  have hFD : ∀ o' ∈ offsets, ⌊y - offVal x o'⌋ = ⌊b - offVal x o'⌋ := by
    intro o' h'
    apply le_antisymm
    · apply Int.le_floor.2
      have := hmax' o' h'
      simp only [bv] at this
      linarith
    · exact Int.floor_le_floor (by linarith)
  -- `b` as a candidate
  obtain ⟨hB, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  set ri := (qrOf x.num x.den o).2
  set k := (qrOf x.num x.den o).1 + j
  have hbc : b = candY x k ri := by
    have hMne : ((960 * (x.den : ℤ) : ℤ) : ℚ) ≠ 0 := by
      have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
      push_cast; positivity
    have h1 : offVal x o = ((qrOf x.num x.den o).1 : ℚ) + (ri : ℚ) / ((960 * (x.den : ℤ) : ℤ) : ℚ) := by
      rw [offVal_scaled, hB]
      field_simp
      push_cast
      ring
    show offVal x o + (j : ℚ) = candY x k ri
    rw [h1, candY]
    simp only [k]
    push_cast
    ring
  rcases eq_or_lt_of_le hb_le with hby | hby
  · -- `y` is itself a breakpoint
    have hy' : y = candY x k ri := hby.symm.trans hbc
    have hv := valid_of_le x k ri hr0 hrM (hbc ▸ hb0) false (by simp; rw [← hy']; exact hyx)
    obtain ⟨t, htT, htv, hteq⟩ := exists_threshold _ (qrOf x.num x.den c1Off)
      (qrOf x.num x.den c2Off) _ _ _ false k hv
    have := le_eStarInt x o ho false t htT htv
    rw [hteq, phiAt_eq_Phi x k ri hr0 hrM false] at this
    simp only [Bool.false_eq_true, if_false] at this
    rw [hy']
    exact this
  · -- `y` lies strictly right of the breakpoint `b`
    have hCD : ∀ o' ∈ offsets, ⌈y - offVal x o'⌉ = ⌊b - offVal x o'⌋ + 1 := by
      intro o' h'
      rw [← hFD o' h']
      apply (Int.ceil_eq_floor_add_one_iff_notMem _).2
      rintro ⟨n, hn⟩
      have h1 := hmax' o' h'
      have h2 : ⌊y - offVal x o'⌋ = n := by rw [← hn, Int.floor_intCast]
      simp only [bv] at h1
      rw [h2, hn] at h1
      have : b < b := lt_of_lt_of_le hby (by linarith)
      exact lt_irrefl _ this
    have hv := valid_of_le x k ri hr0 hrM (hbc ▸ hb0) true
      (by simp; rw [← hbc]; exact lt_of_lt_of_le hby hyx)
    obtain ⟨t, htT, htv, hteq⟩ := exists_threshold _ (qrOf x.num x.den c1Off)
      (qrOf x.num x.den c2Off) _ _ _ true k hv
    have := le_eStarInt x o ho true t htT htv
    rw [hteq, phiAt_eq_Phi x k ri hr0 hrM true] at this
    simp only [if_true] at this
    rw [Phi_congr _ _ (fun o => ⌊candY x k ri - offVal x o⌋)
      (fun o => ⌊candY x k ri - offVal x o⌋ + 1)
      (fun o' h' => by rw [hFD o' h', hbc]) (fun o' h' => by rw [hCD o' h', hbc])]
    exact this

end BetaIrr.I3.CertA
