# One of β(4), β(6), …, β(36) is irrational: a Lean 4 proof

This repository contains a complete, machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the following theorem.

> **Theorem.** Let β(s) = Σ_{m≥0} (−1)^m / (2m+1)^s be the Dirichlet beta function. Then at least one of the 17 numbers
> β(4), β(6), …, β(36) is irrational.

In Lean:

```lean
-- BetaIrrational/Defs.lean, BetaIrrational/Statement.lean
def dirichletBeta (s : ℕ) : ℝ := ∑' m : ℕ, (-1 : ℝ) ^ m / (2 * (m : ℝ) + 1) ^ s
def OneOfBeta4To36 : Prop := ∃ j ∈ Finset.Icc 2 18, Irrational (dirichletBeta (2 * j))

-- BetaIrrational/I3/MainUnconditional.lean
theorem BetaIrr.I3.oneOfBeta4To36 : OneOfBeta4To36
```

```
'BetaIrr.I3.oneOfBeta4To36' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof uses only Lean's three standard axioms. There is no `sorry`, no added `axiom` and no `native_decide`: every
numerical certificate is evaluated by the Lean kernel. See [TRUST.md](TRUST.md).

The namespace `I3` and the folder `BetaIrrational/I3/` name the parameter set used (the third one we tried); there is
only one instance in this repository.

## Why β(2) is excluded

β(2) is Catalan's constant G. The explicit results of this kind that we know of all include it:
- Rivoal–Zudilin (Math. Ann. 2003): one of β(2), …, β(14);
- Zudilin (2019): one of β(2), …, β(12);
- Lai–Zhou (arXiv:2103.00904): one of β(2), …, β(10).

So "one of β(2), …, β(10) is irrational" would be satisfied by G alone, if G is irrational, and would say nothing about
the higher values. The theorem here never mentions β(2): its linear forms do not involve β(2) at all.

We have not found an explicit result of this form in the literature. Our search covered the web and arXiv, but not
MathSciNet or zbMATH. Qualitatively, a statement "one of β(4), …, β(N)" for some computable N follows from Rivoal–Zudilin's
dimension bound, but no explicit N is given there. Please tell us if you know of prior work.

## Outline of the proof

The method follows the Ball–Rivoal / Rivoal–Zudilin approach. For n ∈ 480ℕ let

    R_n(t) = (2t + n + 1) · Π_{l = −(1+r)n−1}^{rn} (t − l)³  /  Π_j Π_{k = δ_j n}^{(1−δ_j) n} (t + k + ½)^{m_j}

with r = 7/6 and 28 "pole blocks" (δ_j, m_j): δ = 0 with multiplicity 8, and single blocks at δ = k/160 for
k = 1…8, 10, 12, …, 46. Put

    L_n = Σ_{t ≥ 0} (−1)^t R_n''(t).

1. **No β(2), no odd values (Lemmas 1–3).**
   - Because of the second derivative (Rivoal's trick from the ζ(5..21) paper), L_n lies in
     ℚ + ℚβ(4) + ℚβ(6) + … + ℚβ(36).
   - The β(2) coefficient vanishes, and the odd-index coefficients vanish by symmetry.
   - Files: `Expansion.lean`, `I3/Concrete/`.
2. **Denominators (Lemmas 4–5).**
   - An explicit D_n makes D_n L_n an integer linear form.
   - log D_n ≤ G log n! + n(A + 20 log 2) + o(n), where G = 179/10 and A ≤ 15.8256550.
   - A is an integral of a step function e*(x) dx/x² over the prime ranges. Its bound is an exact rational certificate
     (62,131 event intervals), checked in the kernel.
   - The prime number theorem supplies the passage from primes to the integral.
   - Files: `I3/Arith/`, `I3/CertA/`, `I3/CertAK/`, `PNT/`.
3. **Size (Lemma 6(i)).** log |L_n| ≤ −G log n! + n·V + o(n), with V = −29.76.
   - This comes from an elementary real-axis bound: max_{x ≥ r} Φ(x) = −29.76133…, certified in Lean.
   - Files: `I3/Size/`.
4. **Conclusion.**
   - Q = V + A + 20 log 2 ≈ −0.0714 < 0, so D_n L_n → 0.
   - If all of β(4), …, β(36) were rational, D_n L_n would be integers (after clearing one fixed denominator), nonzero
     infinitely often by step 5, and tending to 0: a contradiction.
   - Files: `Criterion.lean`, `Statement.lean`, `I3/Glue/`.
5. **Nonvanishing (Lemma 6(ii)).** L_n ≠ 0 for infinitely many n.
   - L_n is written as a contour integral and deformed onto a certified steepest-descent path.
   - Uniform complex Stirling and a Laplace estimate at the saddle point show that L_n is, up to a positive factor,
     Im(C·e^{i n Im Ω}) + o(1) with C ≠ 0.
   - Since sin(480·Im Ω) > 0.99 and n runs through 480ℕ, the phase cannot stay near a zero of the sine for consecutive n.
   - The saddle point, the path and all bounds along it are certified by kernel-checked interval arithmetic.
   - Files: `I3/Analytic/`, `I3/Interval/`, `Analytic/`, `Stirling/`.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get          # download prebuilt Mathlib
lake build                  # over an hour on a desktop with 16+ GB RAM; the A-certificate dominates
lake env lean Axioms.lean   # print the axioms of the main theorem and its ingredients
```

## Repository layout

| path | content |
|---|---|
| `Defs.lean`, `Statement.lean`, `Criterion.lean` | β(s), the target statement, the irrationality criterion |
| `Expansion.lean`, `Concrete/PartialFrac.lean` | Lemmas 1–3 for general partial-fraction data |
| `Assembly.lean` | the log bounds give D_n L_n → 0 |
| `PNT/` | prime number theorem (ported from PrimeNumberTheoremAnd), prime sums with step weights |
| `Stirling/` | complex Stirling and digamma bounds in sectors, with explicit constants |
| `Arith/` | p-adic valuations of power-series coefficients, Legendre's formula, Lemmas B and C |
| `Size/` | `F(y) = y log y` and discrete comparisons, logarithmic-derivative bounds |
| `Interval/` | rational interval and complex-box arithmetic, log/arctan/arg/√, Newton contraction, polyline and ray checks |
| `Analytic/` | alternating sums as contour integrals, deformation, Laplace bound, saddle assembly |
| `Fam/` | further instance-independent helpers |
| `FamilyI3.lean` | the parameters, the concrete R_n and L_n, and the assembly from the four inputs |
| `I3/Concrete`, `I3/Arith` | Lemma 3 (expansion) and Lemma 4 (denominators) for these R_n |
| `I3/CertA`, `I3/CertAK`, `I3/Glue` | Lemma 5: the A-certificate (mathematics in `CertA`, kernel computation in `CertAK`) and the PNT step |
| `I3/Size` | Lemma 6(i): the real-axis size bound |
| `I3/Analytic`, `I3/Interval` | Lemma 6(ii): contour, Stirling, Laplace, and the kernel-checked saddle certificate |
| `I3/MainCond.lean`, `I3/MainUnconditional.lean` | the final assembly |
| `scripts/` | generators for the certificate data (untrusted; see TRUST.md) |
| `Axioms.lean` | axiom audit |

Paths are relative to `BetaIrrational/`. Every Lean file starts with a docstring saying what it proves and its status.
References such as "PROOF_BETA §5" point to the sections of the informal write-up of the proof.

## Status and caveats

- The Lean kernel has checked the proof. **No human expert has yet reviewed the mathematics or the Lean code.** The
  statement definitions (see TRUST.md) are short and worth reading.
- The construction, the proofs, the parameter search, the certificate programs and the Lean formalisation were produced
  largely by AI models (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel
  check, all verification so far has been done by AI systems.
- The numerical margin is thin: Q ≈ −0.07. It is certified, not estimated.

## Acknowledgements

- `PNT/Port/` is ported from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (A. Kontorovich, T. Tao et al.), via the port in [domino14/zeta5](https://github.com/domino14/zeta5), under the
  Apache License 2.0 (see `PNT/Port/LICENSE`).
- The construction builds on:
  - T. Rivoal, Acta Arith. 103 (2002): the second-derivative trick;
  - T. Rivoal and W. Zudilin, Math. Ann. 326 (2003);
  - W. Zudilin, Abh. Math. Semin. Univ. Hambg. 89 (2019);
  - X. Lai and L. Zhou, arXiv:2103.00904.

## License

Apache License 2.0 (see [LICENSE](LICENSE)). `BetaIrrational/PNT/Port/` is derived from PrimeNumberTheoremAnd, also
Apache-2.0; its own `LICENSE` file and the provenance notes in its file headers are kept.
