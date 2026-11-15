/-
# Chenevier–Lannes, §3.4.2: the holy neighbours are Niemeier lattices

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.2, Theorem 3.4.2.10 (b), (c), p. 69, and the second proof
of (c), pp. 72–73. Printed page numbers.

Setting: $L = \mathbb{Z}^{24}$ with a Niemeier form $Q$ with roots, Coxeter number $h$, a Weyl vector $\rho \in L$ and
$v \in L$ with $\rho \cdot v \equiv 1 \bmod d$, $d \in \{h, h + 1\}$.

**Proves**, conditional on `VenkovRootSum 24` (Proposition 2.3.2) and `WeylVectorNorm` (Proposition 3.4.2.5):
- `holyNeighbor_isNiemeier`: $\mathrm{vois}_h(L; \rho)$ and $\mathrm{vois}_{h+1}(L; \rho)$ are Niemeier lattices
  (Proposition 3.1.4 via `voisLat_isEvenUnimodular`, with $q(\rho) = h(h + 1)$);
- `thm_3_4_2_10_b` (Theorem 3.4.2.10 (b)): $\mathrm{vois}_{h+1}(L; \rho) = s_\rho(\mathrm{vois}_h(L; \rho))$, so the two
  are isometric.

**Proves**, conditional moreover on `HRegularDecomposition` and `PlusOneRegularDecomposition`:
- `holyConstructions_of_prime` (Theorem 3.4.2.10 (c), second proof, for the $19$ Coxeter numbers $h$ of Table 1.1 with
  $h$ or $h + 1$ prime, `prime_coxeter_table`): both holy neighbours are Niemeier lattices without roots, i.e. the
  named statement `HolyConstructions` holds for these $L$.

Unconditional helper: `isLeechType_of_rootless` (a $d$-neighbour without vectors of norm $2$ of a Niemeier lattice is,
in a basis, of Leech type).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.NeighborUnimodular

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

/-- A lattice of $\mathbb{Q}^{24}$ given by a basis $g$, with Niemeier form $P(x) = Q(gx)$ and no $x$ with
$q(x) = 1$, is of Leech type. Unconditional. -/
theorem isLeechType_of_rootless {Q P : QuadForm ℤ 24} {g : Matrix (Fin 24) (Fin 24) ℚ}
    {N : Submodule ℤ (Fin 24 → ℚ)} (hN : imgLat g = N) (hP : ∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x))
    (hPe : IsEvenUnimodular P) (hroot : ∀ x ∈ N, Q.evalIn ℚ x ≠ 1) : IsLeechType P := by
  refine ⟨hPe, Set.eq_empty_iff_forall_notMem.mpr fun c hc => ?_⟩
  have hc1 : P.eval c = 1 := hc
  refine hroot (g *ᵥ cv c) (by rw [← hN]; exact ⟨c, rfl⟩) ?_
  rw [← hP, evalIn_cv, hc1]; norm_num

/-- **The holy neighbours are Niemeier lattices** (Chenevier–Lannes, Theorem 3.4.2.10, p. 69; Proposition 3.1.4):
**conditional** on `VenkovRootSum 24` and `WeylVectorNorm`. For $d = h$ or $d = h + 1$ and $v \in L$ with
$\rho \cdot v \equiv 1 \bmod d$, $\mathrm{vois}_d(L; \rho) = g\,\mathbb{Z}^{24}$ with $\det g \ne 0$, and its form
$P(x) = Q(gx)$ is a Niemeier lattice. -/
@[kb "chenevierlannes2019" "Thm. 3.4.2.10, p. 69 (vois_h(L; ρ), vois_{h+1}(L; ρ) are Niemeier lattices; conditional)"]
theorem holyNeighbor_isNiemeier (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24}
    (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ}
    (hρ : IsWeylVector Q (cv ρ)) {d : ℕ} (hd : d = h ∨ d = h + 1) {v : Fin 24 → ℤ}
    (hv : (d : ℤ) ∣ bZ Q ρ v - 1) :
    ∃ (g : Matrix (Fin 24) (Fin 24) ℚ) (P : QuadForm ℤ 24), g.det ≠ 0 ∧ imgLat g = voisLat Q d ρ v ∧
      (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsNiemeier P := by
  obtain ⟨hh2, hq, -, -⟩ := weyl_facts hV hN hQ hR hh hρ
  have hd1 : 1 ≤ d := by omega
  have hdq : (d : ℤ) ∣ Q.eval ρ := by
    rw [hq]
    rcases hd with rfl | rfl
    · exact dvd_mul_right _ _
    · push_cast; exact dvd_mul_left _ _
  exact voisLat_isEvenUnimodular hQ hd1 hdq hv

/-- **Theorem 3.4.2.10 (b)** (Chenevier–Lannes, p. 69): **conditional** on `VenkovRootSum 24` and `WeylVectorNorm`.
The reflection $s_\rho$ maps $\mathrm{vois}_h(L; \rho)$ onto $\mathrm{vois}_{h+1}(L; \rho)$ (Proposition 3.1.14 (b)
with $q(\rho) = h(h + 1)$); in particular the two holy neighbours are isometric (`evalIn_reflQ`). Here $v, v'$ are any
vectors with $\rho \cdot v \equiv 1 \bmod h$ and $\rho \cdot v' \equiv 1 \bmod (h + 1)$. -/
@[kb "chenevierlannes2019" "Thm. 3.4.2.10 (b), p. 69 (conditional)"]
theorem thm_3_4_2_10_b (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v v' : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) (hv' : ((h + 1 : ℕ) : ℤ) ∣ bZ Q ρ v' - 1) :
    voisLat Q (h + 1) ρ v' = (voisLat Q h ρ v).map ((reflQ Q ρ).restrictScalars ℤ) := by
  obtain ⟨hh2, hq, ⟨v₀, hv₀⟩, -⟩ := weyl_facts hV hN hQ hR hh hρ
  have hq' : Q.eval ρ = (h : ℤ) * ((h + 1 : ℕ) : ℤ) := by rw [hq]; push_cast; ring
  have h0 : ((h : ℤ) * ((h + 1 : ℕ) : ℤ)) ∣ bZ Q ρ v₀ - 1 := by rw [hv₀, sub_self]; exact dvd_zero _
  have e1 : voisLat Q (h + 1) ρ v' = voisLat Q (h + 1) ρ v₀ :=
    voisLat_congr (by omega) 0 (by simp) ⟨h, by rw [hq']; ring⟩ ⟨h, by rw [hq']; ring⟩
      (by rw [hv₀, sub_self]; exact dvd_zero _) hv'
  have e2 : voisLat Q h ρ v = voisLat Q h ρ v₀ :=
    voisLat_congr (by omega) 0 (by simp) ⟨(h + 1 : ℕ), hq'⟩ ⟨(h + 1 : ℕ), hq'⟩
      (by rw [hv₀, sub_self]; exact dvd_zero _) hv
  rw [e1, e2]
  exact voisLat_eq_map_reflQ (by omega) (by omega) hq' h0

/-- **Theorem 3.4.2.10 (c) for $19$ of the $23$ Niemeier lattices with roots** (Chenevier–Lannes, p. 69, second proof
pp. 72–73): **conditional** on `VenkovRootSum 24`, `WeylVectorNorm`, `HRegularDecomposition` and
`PlusOneRegularDecomposition`. If $h$ or $h + 1$ is prime (all Coxeter numbers of Table 1.1 except
$25, 14, 9, 8$, `prime_coxeter_table`), then for $d \in \{h, h + 1\}$ and $\rho \cdot v \equiv 1 \bmod d$,
$\mathrm{vois}_d(L; \rho)$ is, in a basis, a Niemeier lattice without roots — the conclusion of `HolyConstructions`
(c) for this $L$ (which equals the Leech lattice once `ConwayLeechUnique` is known). -/
@[kb "chenevierlannes2019" "Thm. 3.4.2.10 (c), p. 69; pp. 72–73 (h or h + 1 prime; conditional)"]
theorem holyConstructions_of_prime (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hD : HRegularDecomposition)
    (hPl : PlusOneRegularDecomposition) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty)
    {h : ℕ} (hh : coxeterNumber Q = h) (hp : h.Prime ∨ (h + 1).Prime) {ρ : Fin 24 → ℤ}
    (hρ : IsWeylVector Q (cv ρ)) {d : ℕ} (hd : d = h ∨ d = h + 1) {v : Fin 24 → ℤ}
    (hv : (d : ℤ) ∣ bZ Q ρ v - 1) :
    ∃ (g : Matrix (Fin 24) (Fin 24) ℚ) (P : QuadForm ℤ 24), g.det ≠ 0 ∧ imgLat g = voisLat Q d ρ v ∧
      (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsLeechType P := by
  obtain ⟨g, P, hg, hgN, hP, hPe⟩ := holyNeighbor_isNiemeier hV hN hQ hR hh hρ hd hv
  refine ⟨g, P, hg, hgN, hP, isLeechType_of_rootless hgN hP hPe ?_⟩
  obtain ⟨hh2, hq, ⟨v₀, hv₀⟩, -⟩ := weyl_facts hV hN hQ hR hh hρ
  have hv₀h : (h : ℤ) ∣ bZ Q ρ v₀ - 1 := by rw [hv₀, sub_self]; exact dvd_zero _
  have hless := voisLat_rootless_of_prime hV hN hD hPl hQ hR hh hp hρ hv₀h
  rcases hd with rfl | rfl
  · rwa [voisLat_congr (by omega) 0 (by simp) ⟨d + 1, hq⟩ ⟨d + 1, hq⟩ hv₀h hv]
  · rw [thm_3_4_2_10_b hV hN hQ hR hh hρ hv₀h hv]
    rintro _ ⟨x, hx, rfl⟩ h1
    have hu : Q.eval ρ ≠ 0 := by rw [hq]; positivity
    refine hless x hx ?_
    rw [← h1]
    exact (evalIn_reflQ Q hu x).symm

end QuadFormsKB.ChenevierLannes
