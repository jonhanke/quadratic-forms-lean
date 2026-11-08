/-
# Hanke 2011 (enumerating maximal definite forms): mass, proper mass and class number

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (bib key `hanke2011enumerating`), §2, p. 3, and Lemma 4.3, p. 7.

For a totally positive definite form $Q$ over a totally real number field $F$ and an integral lattice $L$:
* $\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}1/|O(M)| \le h(L)/2$ (p. 3), since $-1\in O(M)$ and $-1\ne1$, so
  $|O(M)|\ge2$ for every class (`mass_le_half_classNumber`);
* **Lemma 4.3**: $\mathrm{Mass}^+(L) = 2\,\mathrm{Mass}(L)$, where $\mathrm{Mass}^+$ is the proper mass (1), the sum of
  $1/|SO(M)|$ over the proper classes (here: the $SO$-double cosets `DC Q₀`, as in Gan–Hanke–Yu's Prop. 7.4); this is the
  composition of `Hanke2005.hankeMass_definite` and `Hanke2005.hankeMass_definite_eq_two_mul_mass` (`lemma_4_3`);
* hence $\mathrm{Mass}^+(L)\le h(L)$ (`massPlus_le_classNumber`), the first implication of (5), p. 11.

Conventions: `Lattices.mass` and `Lattices.classNumber` count classes for the full orthogonal group $O(V)$ (improper
isometries included), as the paper's $\mathrm{Cls}(Q)$, $\mathrm{Aut}(Q)$ do.
-/
import QuadFormsKB.Literature.Hanke2005.MassDefinite
import QuadFormsKB.Literature.OMeara.Sec102

open NumberField IsDedekindDomain Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### $-1$ is an automorphism of every lattice -/

/-- $-1\in O(V)(F)$. -/
theorem neg_one_mem_orthGroup (Q : QuadForm F n) : (-1 : GL (Fin n) F) ∈ orthGroup Q F := by
  rw [mem_orthGroup]
  simp

/-- The isometry $-1$ of $(F^n, Q)$. -/
def negOrth (Q : QuadForm F n) : orthGroup Q F := ⟨-1, neg_one_mem_orthGroup Q⟩

/-- $-1$ stabilizes every $\mathcal O_F$-submodule $M\subseteq F^n$: $-1\in O(M)$. -/
theorem negOrth_mem_autLat (Q : QuadForm F n) (M : Submodule (𝓞 F) (Fin n → F)) :
    negOrth Q ∈ autLat Q M := by
  rw [mem_autLat]
  ext x
  rw [mem_glImage]
  have hv : ∀ y : Fin n → F, ((negOrth Q : orthGroup Q F) : GL (Fin n) F).val *ᵥ y = -y := fun y => by
    simp [negOrth, neg_mulVec]
  simp only [hv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact M.neg_mem hy
  · intro hx
    exact ⟨-x, M.neg_mem hx, neg_neg x⟩

/-- $-1\ne1$ in $O(V)$ when $n\ge1$ (the field $F$ has characteristic $0$). -/
theorem negOrth_ne_one (Q : QuadForm F n) (hn : 1 ≤ n) : negOrth Q ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : orthGroup Q F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    ⟨0, hn⟩ ⟨0, hn⟩) h
  simp [negOrth] at h1
  have : (2 : F) = 0 := by linear_combination -h1
  exact two_ne_zero this

/-- **$|O(M)|\ge2$** for a lattice $M$ on a totally positive definite space of dimension $n\ge1$ with $Q(M)$ integral
($O(M)$ is finite, `finite_autLat`, and contains $1\ne-1$). -/
theorem two_le_card_autLat {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (hn : 1 ≤ n)
    {M : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F) (hMi : IsIntegral Q M) :
    2 ≤ Nat.card (autLat Q M) := by
  have := finite_autLat hQ hM hMi
  have hnt : Nontrivial (autLat Q M) :=
    ⟨⟨1, ⟨negOrth Q, negOrth_mem_autLat Q M⟩, fun h => negOrth_ne_one Q hn
      (congrArg Subtype.val h).symm⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr hnt

/-! ### $\mathrm{Mass}\le h/2$ -/

/-- **$\mathrm{Mass}(L)\le h(L)/2$** (Hanke 2011, §2, p. 3: "$\mathrm{Mass}(Q) := \sum 1/|\mathrm{Aut}(Q')| \le h(Q)/2$"):
for $Q$ totally positive definite over the (totally real) number field $F$, $n\ge1$, and $L$ a lattice with $Q(L)$
integral, the mass `Lattices.mass Q L` $=\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}1/|O(M)|$ is at most half the class
number $h(L)$ = `Lattices.classNumber Q L`, since every term is $\le1/2$ (`two_le_card_autLat`). -/
@[kb "hanke2011enumerating" "§2, p. 3 (Mass(Q) ≤ h(Q)/2)"]
theorem mass_le_half_classNumber {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (hn : 1 ≤ n) (L : Lat F n)
    (hLi : IsIntegral Q L.1) : mass Q L ≤ (Lattices.classNumber Q L : ℝ) / 2 := by
  classical
  have hfin := genusClasses_finite hQ L hLi
  rw [mass_eq_sum hQ L hLi, Lattices.classNumber, Set.ncard_eq_toFinset_card _ hfin, div_eq_mul_inv, mul_comm]
  have hterm : ∀ c ∈ hfin.toFinset, ((LatClass.autCard Q c : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    intro c hc
    obtain ⟨M, rfl, hM⟩ := (Set.Finite.mem_toFinset _).mp hc
    have h2 := two_le_card_autLat hQ hn M.2 (SameGenus.isIntegral Q hLi hM)
    change ((Nat.card (autLat Q M.1) : ℕ) : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹
    have h2' : (2 : ℝ) ≤ (Nat.card (autLat Q M.1) : ℝ) := by exact_mod_cast h2
    exact inv_anti₀ (by norm_num) h2'
  calc ∑ c ∈ hfin.toFinset, ((LatClass.autCard Q c : ℝ))⁻¹
      ≤ ∑ _c ∈ hfin.toFinset, (2 : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (2 : ℝ)⁻¹ * (hfin.toFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### Lemma 4.3: $\mathrm{Mass}^+ = 2\,\mathrm{Mass}$ -/

/-- **Lemma 4.3** (Hanke 2011, p. 7): for $F$ a totally real number field and $Q_0$ an $\mathcal O_F$-valued form in
$n\ge1$ variables, nondegenerate and totally positive definite over $F$, the proper mass of $L = \mathcal O_F^n$,
$$\mathrm{Mass}^+(L) = \sum_{\mathrm{Cls}^+(M)\subseteq\mathrm{Gen}(L)}\frac1{|SO(M)|}
\qquad(\text{the sum over the } SO\text{-double cosets } i\in\texttt{DC}\ Q_0,\ |SO(M_i)| = |\texttt{unitGroup}\ Q_0\ i|),$$
equals $2\,\mathrm{Mass}(L)$, $\mathrm{Mass}$ = `Lattices.mass` (classes and automorphisms for the full orthogonal group).
Composed from `Hanke2005.hankeMass_definite` and `Hanke2005.hankeMass_definite_eq_two_mul_mass` (the latter rests on
`Tamagawa.mass_SO_eq_two_mul_mass`, the paper's argument: a class is one or two proper classes, according as $O(M)$ has
an element of determinant $-1$ or not). **Unconditional.** -/
@[kb "hanke2011enumerating" "Lemma 4.3, p. 7"]
theorem lemma_4_3 [IsTotallyReal F] (hn : 1 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (2 * mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
  rw [← Hanke2005.hankeMass_definite hn Q₀ hQ hpd, Hanke2005.hankeMass_definite_eq_two_mul_mass hn Q₀ hQ hpd]

/-- **$\mathrm{Mass}^+(L)\le h(L)$** (Hanke 2011, (5), p. 11, first implication, from Lemma 4.3 and $\mathrm{Mass}\le h/2$):
with the hypotheses of `lemma_4_3`, the proper mass of $\mathcal O_F^n$ is at most its class number. -/
@[kb "hanke2011enumerating" "(5), p. 11 (h(L) ≤ B ⇒ Mass⁺(L) ≤ B); Thm. 4.2 proof, p. 7 (Mass⁺(L) ≤ h(L))"]
theorem massPlus_le_classNumber [IsTotallyReal F] (hn : 1 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ ≤
      (Lattices.classNumber (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n) : ℝ≥0∞) := by
  rw [lemma_4_3 hn Q₀ hQ hpd]
  have hLi := HilbertModular.isIntegral_stdLat Q₀
  have h := mass_le_half_classNumber hpd hn (stdLat F n) hLi
  have h2 : 2 * mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n) ≤
      (Lattices.classNumber (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n) : ℝ) := by linarith
  calc ENNReal.ofReal (2 * mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n))
      ≤ ENNReal.ofReal (Lattices.classNumber (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n) : ℝ) := ENNReal.ofReal_le_ofReal h2
    _ = _ := ENNReal.ofReal_natCast _

end QuadFormsKB.Hanke2011Enumerating
