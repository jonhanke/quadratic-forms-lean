/-
# Cassels, Chapter 5, §§2–3: Blichfeldt and Minkowski

**Setting.** Euclidean space $\mathbb R^n$ is `Fin n → ℝ` with Lebesgue measure `volume`; $\mathbb Z^n$ is the lattice
`stdLattice n` $= \operatorname{span}_{\mathbb Z}\{e_0, \dots, e_{n-1}\}$, and an integral point is written
`fun i => (u i : ℝ)` for `u : Fin n → ℤ`. A set $\mathcal C$ is *symmetric* (Cassels 5.d1) when $-\vec x \in \mathcal C$
for $\vec x \in \mathcal C$. Indices are $0, \dots, n-1$ (Cassels: $1, \dots, n$).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 5)
* Theorem 2.1 (Blichfeldt): `blichfeldt` (general $k$, measurable $\mathcal S$) and the case $k = 1$ (Blichfeldt's
  original theorem, as Cassels notes) for null-measurable sets, `blichfeldt_one`;
* Theorem 2.2 (Minkowski's convex body theorem): `minkowski_convex_body`;
* Theorem 2.3 (the version for the subgroup $\Lambda$ of $\mathbb Z^n$ cut out by congruences): `minkowski_congruences`;
* Theorem 2.4 (Minkowski's linear forms theorem): `minkowski_linear_forms` (Cassels' statement), from the weak form
  with $\le$ in all $n$ inequalities `minkowski_linear_forms_le`;
* Ch. 6, Lemma 8.1 (small zeros, Aubry's method), as an application of Theorem 2.4: `aubry` (kept here because it
  uses the linear forms theorem of this file);
* Theorem 3.1 (Minkowski for a general lattice $\Gamma$ of determinant $d(\Gamma)$): `minkowski_basis` (lattice given by
  a basis, $d(\Gamma) = \lvert\det(b_0, \dots, b_{n-1})\rvert$) and `minkowski_lattice` (any discrete
  $\mathbb Z$-submodule spanning $\mathbb R^n$, with $d(\Gamma)$ the covolume).

**Proof notes.** All of these come from Mathlib's Blichfeldt and Minkowski theorems
(`MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd`,
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` and its compact version) together with the
covolume of a $\mathbb Z$-lattice (`ZLattice.covolume`). Theorem 2.3 is proved through Theorem 3.1 rather than through
the general case of Theorem 2.1, as in Cassels: $\Lambda$ is a lattice of index $\le m = m_0 \cdots m_{r-1}$ in
$\mathbb Z^n$ (the kernel of $\mathbb Z^n \to \prod_l \mathbb Z/m_l$), so $d(\Lambda) \le m$
(`ZLattice.covolume_div_covolume_eq_relIndex`). Theorem 2.4 uses the compact form of Minkowski's theorem on the
parallelepiped $\lvert L_j(\vec x)\rvert \le t_j$; the strict inequalities for $j \ne 0$ follow by Cassels' limiting
argument (finitely many integral points in a bounded parallelepiped, `finite_bounded`).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open MeasureTheory Module Submodule ZSpan Matrix

variable {n : ℕ}

/-- The standard lattice $\mathbb Z^n \subset \mathbb R^n$. -/
noncomputable abbrev stdLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- Membership in $\mathbb Z^n$: $\vec x \in \mathbb Z^n$ exactly when all coordinates of $\vec x$ are integers. -/
theorem mem_stdLattice {x : Fin n → ℝ} : x ∈ stdLattice n ↔ ∃ u : Fin n → ℤ, x = fun i => (u i : ℝ) := by
  rw [stdLattice, Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, eq_intCast]
  constructor
  · intro h
    choose u hu using h
    exact ⟨u, funext fun i => (hu i).symm⟩
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, rfl⟩

/-- The covolume (determinant) of $\mathbb Z^n$ is $1$. -/
theorem covolume_stdLattice : ZLattice.covolume (stdLattice n) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (stdLattice n) volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) volume)]
  have : Matrix.of ⇑(Pi.basisFun ℝ (Fin n)) = 1 := by
    ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  simp [this]

/-- **Cassels, Ch. 5, Theorem 3.1** (Minkowski, general lattice): *let $\Gamma$ be a lattice and $\mathcal C$ a convex
symmetric set in $\mathbb R^n$ with $v(\mathcal C) > 2^n d(\Gamma)$; then $\mathcal C$ contains a point of $\Gamma$ other
than $\vec 0$.* Here a lattice is a discrete $\mathbb Z$-submodule $L$ of $\mathbb R^n$ spanning $\mathbb R^n$ over
$\mathbb R$ (Cassels' 5.r1: such a subgroup has a basis), and $d(\Gamma)$ is its covolume `ZLattice.covolume L`, the
volume of a fundamental domain (equal to $\lvert\det(b_0, \dots, b_{n-1})\rvert$ for a basis, `ZLattice.covolume_eq_det`).
The volume hypothesis reads $2^n d(\Gamma) < v(\mathcal C)$ in $[0, \infty]$. -/
@[kb "cassels1978" "Ch. 5, Thm. 3.1, p. 72 (lattice as a discrete ℤ-submodule, d(Γ) its covolume)"]
theorem minkowski_lattice (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {C : Set (Fin n → ℝ)} (hsymm : ∀ x ∈ C, -x ∈ C) (hconv : Convex ℝ C)
    (hvol : ENNReal.ofReal (2 ^ n * ZLattice.covolume L) < volume C) :
    ∃ x ∈ L, x ≠ 0 ∧ x ∈ C := by
  let b := Module.Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain b volume
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hfin : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)).ne
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  have hlt : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ (Fin n → ℝ) < volume C := by
    rw [hcov, measureReal_def, mul_comm, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin] at hvol
    simpa [mul_comm] using hvol
  obtain ⟨x, hx0, hxC⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := L.toAddSubgroup) fund hsymm hconv hlt
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hxC⟩


/-- **Cassels, Ch. 5, Theorem 2.2** (Minkowski's convex body theorem): *let $\mathcal C$ be a convex symmetric set
in $\mathbb R^n$ with $v(\mathcal C) > 2^n$; then $\mathcal C$ contains a $\vec u \in \mathbb Z^n$ other than $\vec 0$.*
Here $v$ is Lebesgue measure (outer measure for a non-measurable set, which is harmless: Mathlib's theorem only needs the
inequality) and the conclusion gives $\vec u$ as a nonzero `Fin n → ℤ` whose image in $\mathbb R^n$ lies in
$\mathcal C$. -/
@[kb "cassels1978" "Ch. 5, Thm. 2.2, p. 69"]
theorem minkowski_convex_body {C : Set (Fin n → ℝ)} (hsymm : ∀ x ∈ C, -x ∈ C) (hconv : Convex ℝ C)
    (hvol : 2 ^ n < volume C) :
    ∃ u : Fin n → ℤ, u ≠ 0 ∧ (fun i => (u i : ℝ)) ∈ C := by
  obtain ⟨x, hxL, hx0, hxC⟩ := minkowski_lattice (stdLattice n) hsymm hconv
    (by rw [covolume_stdLattice, mul_one, ENNReal.ofReal_pow (by norm_num)]; simpa using hvol)
  obtain ⟨u, rfl⟩ := mem_stdLattice.1 hxL
  refine ⟨u, fun hu => hx0 ?_, hxC⟩
  funext i; simp [hu]

/-- **Cassels, Ch. 5, Theorem 2.1** (Blichfeldt), the case $k = 1$: *let $\mathcal S$ be a set in $\mathbb R^n$ with
$v(\mathcal S) > 1$; then there are two distinct points $\vec s_1, \vec s_2 \in \mathcal S$ with
$\vec s_1 - \vec s_2 \in \mathbb Z^n$.* Cassels proves the statement with $v(\mathcal S) > k$ and $k + 1$ points; the
case $k = 1$ is Blichfeldt's original theorem and the one used for Theorem 2.2. The set is assumed (null-)measurable. -/
@[kb "cassels1978" "Ch. 5, Thm. 2.1, p. 68 (the case k = 1)"]
theorem blichfeldt_one {S : Set (Fin n → ℝ)} (hS : NullMeasurableSet S) (hvol : 1 < volume S) :
    ∃ s₁ ∈ S, ∃ s₂ ∈ S, s₁ ≠ s₂ ∧ ∃ u : Fin n → ℤ, s₁ - s₂ = fun i => (u i : ℝ) := by
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume
  have hF : volume (fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
    have : Matrix.of ⇑(Pi.basisFun ℝ (Fin n)) = 1 := by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp [this]
  have : Countable (stdLattice n).toAddSubgroup := (inferInstance : Countable (stdLattice n))
  obtain ⟨x, y, hxy, hxy'⟩ := exists_pair_mem_lattice_not_disjoint_vadd fund hS (hF ▸ hvol)
  obtain ⟨z, ⟨s, hs, rfl⟩, ⟨s', hs', hzs⟩⟩ := Set.not_disjoint_iff.1 hxy'
  simp only [vadd_eq_add, AddSubgroup.vadd_def] at hzs
  have hmem : ((y : Fin n → ℝ) - x) ∈ stdLattice n := sub_mem y.2 x.2
  obtain ⟨u, hu⟩ := mem_stdLattice.1 hmem
  refine ⟨s, hs, s', hs', fun h => hxy ?_, u, ?_⟩
  · subst h; exact Subtype.ext (by simpa using hzs.symm)
  · rw [← hu]
    have : (y : Fin n → ℝ) + s' = x + s := hzs
    calc s - s' = ((x : Fin n → ℝ) + s) - x - s' := by abel
      _ = ((y : Fin n → ℝ) + s') - x - s' := by rw [this]
      _ = (y : Fin n → ℝ) - x := by abel


/-- **Cassels, Ch. 5, Theorem 2.4** (Minkowski's linear forms theorem), weak form: *let $L_j(\vec x) =
\sum_i A_{ji}x_i$ ($0 \le j < n$) be real linear forms of determinant $D = \det A \ne 0$ and let $t_j > 0$ satisfy
$t_0 t_1 \cdots t_{n-1} \ge \lvert D\rvert$; then there is $\vec a \in \mathbb Z^n$, $\vec a \ne \vec 0$, with
$\lvert L_j(\vec a)\rvert \le t_j$ for all $j$.* Cassels' statement has the strict inequalities
$\lvert L_j(\vec a)\rvert < t_j$ for $j \ne 0$ (his $j \ge 2$); this weaker conclusion is what the compact form of
Minkowski's theorem gives directly; `minkowski_linear_forms` deduces Cassels' statement. $n \ge 1$ is needed (for $n = 0$ there is no nonzero $\vec a$). -/
@[kb "cassels1978" "Ch. 5, Thm. 2.4, p. 71 (with ≤ in all inequalities)"]
theorem minkowski_linear_forms_le (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (hprod : |A.det| ≤ ∏ j, t j) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ ∀ j, |(A *ᵥ fun i => (a i : ℝ)) j| ≤ t j := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f := Matrix.toLin' A with hf
  have hdet : LinearMap.det f ≠ 0 := by rw [hf, LinearMap.det_toLin']; exact hA
  set C : Set (Fin n → ℝ) := f ⁻¹' Set.Icc (-t) t with hC
  have hsymm : ∀ x ∈ C, -x ∈ C := by
    intro x hx
    simp only [hC, Set.mem_preimage, Set.mem_Icc, map_neg] at hx ⊢
    exact ⟨neg_le_neg hx.2, by simpa using neg_le_neg hx.1⟩
  have hconv : Convex ℝ C := (convex_Icc _ _).linear_preimage f
  have hcpt : IsCompact C := by
    exact ((f.equivOfDetNeZero hdet).toContinuousLinearEquiv.toHomeomorph.isCompact_preimage).2
      isCompact_Icc
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume
  have hF : volume (fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
    have : Matrix.of ⇑(Pi.basisFun ℝ (Fin n)) = 1 := by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp [this]
  have : Countable (stdLattice n).toAddSubgroup := (inferInstance : Countable (stdLattice n))
  have : DiscreteTopology (stdLattice n).toAddSubgroup := (inferInstance : DiscreteTopology (stdLattice n))
  have hvol : volume (fundamentalDomain (Pi.basisFun ℝ (Fin n))) * 2 ^ finrank ℝ (Fin n → ℝ) ≤ volume C := by
    rw [hF, one_mul, hC, MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet, Real.volume_Icc_pi,
      hf, LinearMap.det_toLin', finrank_fin_fun]
    have hpos : 0 < |A.det| := abs_pos.2 hA
    simp only [Pi.neg_apply, sub_neg_eq_add]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by linarith [ht j]), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_inv, Finset.prod_congr rfl (fun j _ => (two_mul (t j)).symm), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_mul_eq_div, le_div_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  obtain ⟨x, hx0, hxC⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure fund hsymm hconv hcpt hvol
  obtain ⟨u, hu⟩ := mem_stdLattice.1 x.2
  refine ⟨u, fun h => hx0 (Subtype.ext ?_), fun j => ?_⟩
  · rw [hu, h]; funext i; simp
  · have := hxC
    simp only [hC, Set.mem_preimage, Set.mem_Icc, hu, hf, Matrix.toLin'_apply] at this
    exact abs_le.2 ⟨by simpa using this.1 j, this.2 j⟩


/-- The cast $\mathbb Z^n \to \mathbb R^n$ as a $\mathbb Z$-linear map. -/
noncomputable def intCastLin (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) :=
  ((Int.castAddHom ℝ).compLeft (Fin n)).toIntLinearMap

/-- The cast $\mathbb Z^n \to \mathbb R^n$, coordinatewise. -/
theorem intCastLin_apply (u : Fin n → ℤ) : intCastLin n u = fun i => (u i : ℝ) := rfl

/-- The cast $\mathbb Z^n \to \mathbb R^n$ is injective. -/
theorem intCastLin_injective : Function.Injective (intCastLin n) := by
  intro u v h
  funext i
  have := congrFun h i
  simpa [intCastLin_apply] using this

/-- $\mathbb Z^n$ is the image of the cast map. -/
theorem stdLattice_eq_map : stdLattice n = (⊤ : Submodule ℤ (Fin n → ℤ)).map (intCastLin n) := by
  ext x
  simp [mem_stdLattice, intCastLin_apply, eq_comm]

/-- The congruence map $u \mapsto (\sum_j h_{lj}u_j \bmod m_l)_l$. -/
noncomputable def congrHom {r : ℕ} (h : Fin r → Fin n → ℤ) (m : Fin r → ℕ) :
    (Fin n → ℤ) →+ ((l : Fin r) → ZMod (m l)) where
  toFun u l := ((∑ j, h l j * u j : ℤ) : ZMod (m l))
  map_zero' := by funext l; simp
  map_add' u v := by funext l; simp [mul_add, Finset.sum_add_distrib]

/-- $\vec u$ is in the kernel of the congruence map exactly when $\sum_j h_{lj}u_j \equiv 0 \pmod{m_l}$ for all $l$. -/
theorem mem_ker_congrHom {r : ℕ} (h : Fin r → Fin n → ℤ) (m : Fin r → ℕ) (u : Fin n → ℤ) :
    u ∈ (congrHom h m).ker ↔ ∀ l, (m l : ℤ) ∣ ∑ j, h l j * u j := by
  rw [AddMonoidHom.mem_ker, funext_iff]
  simp only [congrHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **Cassels, Ch. 5, Theorem 2.3**: *let $\Lambda$ be the set of $\vec u \in \mathbb Z^n$ satisfying finitely many
congruences $h_{l0}u_0 + \cdots + h_{l,n-1}u_{n-1} \equiv 0 \pmod{m_l}$ ($0 \le l < r$) with $h_{lj} \in \mathbb Z$ and
integers $m_l \ge 1$, put $m = m_0 \cdots m_{r-1}$, and let $\mathcal C$ be a convex symmetric set with
$v(\mathcal C) > 2^n m$; then $\mathcal C$ contains a $\vec u \in \Lambda$ other than $\vec 0$.* -/
@[kb "cassels1978" "Ch. 5, Thm. 2.3, p. 70"]
theorem minkowski_congruences {r : ℕ} (h : Fin r → Fin n → ℤ) (m : Fin r → ℕ) (hm : ∀ l, 0 < m l)
    {C : Set (Fin n → ℝ)} (hsymm : ∀ x ∈ C, -x ∈ C) (hconv : Convex ℝ C)
    (hvol : 2 ^ n * (∏ l, m l : ℕ) < volume C) :
    ∃ u : Fin n → ℤ, u ≠ 0 ∧ (∀ l, (m l : ℤ) ∣ ∑ j, h l j * u j) ∧ (fun i => (u i : ℝ)) ∈ C := by
  set K : Submodule ℤ (Fin n → ℤ) := AddSubgroup.toIntSubmodule (congrHom h m).ker with hK
  set A : Submodule ℤ (Fin n → ℝ) := K.map (intCastLin n) with hA
  have hAle : A ≤ stdLattice n := by
    rw [stdLattice_eq_map]; exact Submodule.map_mono le_top
  have : DiscreteTopology A :=
    DiscreteTopology.of_continuous_injective (f := Submodule.inclusion hAle) (Continuous.subtype_mk continuous_subtype_val _) (Submodule.inclusion_injective hAle)
  set M : ℕ := ∏ l, m l with hM
  have hM0 : (M : ℝ) ≠ 0 := by
    rw [hM]; exact_mod_cast (Finset.prod_pos fun l _ => hm l).ne'
  have hmemA : ∀ i : Fin n, (M : ℝ) • Pi.basisFun ℝ (Fin n) i ∈ A := by
    intro i
    refine ⟨(M : ℤ) • Pi.single i 1, ?_, ?_⟩
    · show _ ∈ (congrHom h m).ker
      rw [mem_ker_congrHom]
      intro l
      have hdiv : (m l : ℤ) ∣ (M : ℤ) := by
        rw [hM]; push_cast; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ l)
      refine Finset.dvd_sum fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hdiv _) _
    · funext k
      simp [intCastLin_apply, Pi.single_apply]
  have : IsZLattice ℝ A := by
    refine ⟨eq_top_iff.2 ?_⟩
    rw [← (Pi.basisFun ℝ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := Submodule.smul_mem (Submodule.span ℝ (A : Set (Fin n → ℝ))) (M : ℝ)⁻¹
      (Submodule.subset_span (hmemA i))
    rwa [smul_smul, inv_mul_cancel₀ hM0, one_smul] at this
  have hrel := ZLattice.covolume_div_covolume_eq_relIndex A (stdLattice n) hAle
  rw [covolume_stdLattice, div_one] at hrel
  have hidx : A.toAddSubgroup.relIndex (stdLattice n).toAddSubgroup ≤ M := by
    rw [hA, stdLattice_eq_map, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective (f := (intCastLin n : (Fin n → ℤ) →+ (Fin n → ℝ))) _ _ intCastLin_injective, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_top_right, hK, AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.index_ker]
    have hfin : Finite ((l : Fin r) → ZMod (m l)) := by
      have : ∀ l, NeZero (m l) := fun l => ⟨(hm l).ne'⟩
      infer_instance
    calc Nat.card (congrHom h m).range ≤ Nat.card ((l : Fin r) → ZMod (m l)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = M := by rw [Nat.card_pi]; simp [hM, Nat.card_zmod]
  obtain ⟨x, hxA, hx0, hxC⟩ := minkowski_lattice A hsymm hconv (by
    refine lt_of_le_of_lt ?_ hvol
    rw [hrel, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    rw [ENNReal.ofReal_natCast]; exact_mod_cast hidx)
  obtain ⟨u, hu, rfl⟩ := hxA
  refine ⟨u, fun h0 => hx0 (by rw [h0, map_zero]), (mem_ker_congrHom h m u).1 hu, hxC⟩


/-- **Cassels, Ch. 5, Theorem 3.1** (Minkowski), for the lattice $\Gamma = \mathbb Z b_0 + \cdots + \mathbb Z b_{n-1}$
with basis $b_0, \dots, b_{n-1}$ of $\mathbb R^n$ and determinant $d(\Gamma) = \lvert\det(b_0, \dots, b_{n-1})\rvert$
(Cassels' (3.1)): *if $\mathcal C$ is convex and symmetric with $v(\mathcal C) > 2^n d(\Gamma)$ then $\mathcal C$
contains a point $\sum_j u_jb_j$, $\vec u \in \mathbb Z^n - \{\vec 0\}$.* -/
@[kb "cassels1978" "Ch. 5, Thm. 3.1, p. 72"]
theorem minkowski_basis (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C : Set (Fin n → ℝ)} (hsymm : ∀ x ∈ C, -x ∈ C)
    (hconv : Convex ℝ C) (hvol : ENNReal.ofReal (2 ^ n * |(Matrix.of b).det|) < volume C) :
    ∃ x ∈ span ℤ (Set.range b), x ≠ 0 ∧ x ∈ C := by
  have hcov : ZLattice.covolume (span ℤ (Set.range b)) = |(Matrix.of b).det| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume)]
    simp
  exact minkowski_lattice (span ℤ (Set.range b)) hsymm hconv (hcov ▸ hvol)

/-- Integer vectors $\vec a$ with $\lvert(A\vec a)_k\rvert \le M$ for all $k$ form a finite set ($\det A \ne 0$). -/
private theorem finite_bounded (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (M : ℝ) :
    {a : Fin n → ℤ | ∀ k, |(A *ᵥ fun i => (a i : ℝ)) k| ≤ M}.Finite := by
  set R : ℝ := (∑ i, ∑ k, |A⁻¹ i k|) * |M| with hR
  refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_
  intro a ha
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA)
  have hai : (a i : ℝ) = (A⁻¹ *ᵥ (A *ᵥ fun i => (a i : ℝ))) i := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hb : |(a i : ℝ)| ≤ R := by
    rw [hai]
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |A⁻¹ i k * (A *ᵥ fun i => (a i : ℝ)) k| ≤ ∑ k, |A⁻¹ i k| * |M| := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((ha k).trans (le_abs_self M)) (abs_nonneg _)
      _ = (∑ k, |A⁻¹ i k|) * |M| := by rw [Finset.sum_mul]
      _ ≤ R := by
          rw [hR]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact Finset.single_le_sum (f := fun i => ∑ k, |A⁻¹ i k|)
            (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have h1 : (a i : ℝ) ≤ ⌈R⌉ := ((le_abs_self _).trans hb).trans (Int.le_ceil R)
  have h2 : -(⌈R⌉ : ℝ) ≤ a i := by
    have := (neg_abs_le (a i : ℝ)); linarith [Int.le_ceil R]
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩

/-- Theorem 2.4 with the non-strict inequality at an arbitrary index $j_0$ (see `minkowski_linear_forms`). -/
theorem minkowski_linear_forms_at (j₀ : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (hprod : |A.det| ≤ ∏ j, t j) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ |(A *ᵥ fun i => (a i : ℝ)) j₀| ≤ t j₀ ∧
      ∀ j, j ≠ j₀ → |(A *ᵥ fun i => (a i : ℝ)) j| < t j := by
  classical
  have hn : 0 < n := j₀.pos
  set L : (Fin n → ℤ) → Fin n → ℝ := fun a => A *ᵥ fun i => (a i : ℝ) with hL
  -- the points produced for a given ε
  have hε : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ a : Fin n → ℤ, a ≠ 0 ∧ |L a j₀| ≤ t j₀ * (1 + ε) ^ (n - 1) ∧
      ∀ j, j ≠ j₀ → |L a j| ≤ t j / (1 + ε) := by
    intro ε hε0 _
    set t' : Fin n → ℝ := fun j => if j = j₀ then t j₀ * (1 + ε) ^ (n - 1) else t j / (1 + ε) with ht'
    have hpos : ∀ j, 0 < t' j := fun j => by
      simp only [ht']; split_ifs
      · exact mul_pos (ht _) (pow_pos (by linarith) _)
      · exact div_pos (ht _) (by linarith)
    have hprod' : ∏ j, t' j = ∏ j, t j := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]
      have hcard : (Finset.univ.erase j₀).card = n - 1 := by simp
      have : ∏ j ∈ Finset.univ.erase j₀, t' j = (∏ j ∈ Finset.univ.erase j₀, t j) / (1 + ε) ^ (n - 1) := by
        rw [← hcard, ← Finset.prod_const, ← Finset.prod_div_distrib]
        exact Finset.prod_congr rfl fun j hj => by simp [ht', Finset.ne_of_mem_erase hj]
      rw [this]
      simp only [ht', ite_true]
      field_simp
    obtain ⟨a, ha0, ha⟩ := minkowski_linear_forms_le hn A hA t' hpos (hprod'.symm ▸ hprod)
    refine ⟨a, ha0, by simpa [ht'] using ha j₀, fun j hj => by simpa [ht', hj] using ha j⟩
  -- the finite set of candidates
  set M : ℝ := t j₀ * 2 ^ (n - 1) + ∑ j, t j with hM
  have hfin := finite_bounded A hA M
  set S : Set (Fin n → ℤ) := {a | a ≠ 0 ∧ (∀ k, |L a k| ≤ M) ∧ ∀ j, j ≠ j₀ → |L a j| < t j} with hS
  have hSfin : S.Finite := hfin.subset fun a ha => ha.2.1
  by_contra hno
  push Not at hno
  have hbig : ∀ a ∈ S, t j₀ < |L a j₀| := fun a ha => by
    by_contra h; push Not at h
    obtain ⟨j, hj, hj'⟩ := hno a ha.1 h
    exact absurd (ha.2.2 j hj) (not_lt.2 hj')
  have hsum_ge : ∀ k, t k ≤ ∑ j, t j := fun k =>
    Finset.single_le_sum (fun j _ => (ht j).le) (Finset.mem_univ k)
  -- a margin δ > 1
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : ℝ, 1 < δ ∧ ∀ a ∈ S, δ * t j₀ ≤ |L a j₀| := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨2, by norm_num, fun a ha => by rw [he] at ha; exact absurd ha (Set.notMem_empty a)⟩
    · obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image S (fun a => |L a j₀|) hSfin hne
      refine ⟨|L a₀ j₀| / t j₀, (one_lt_div (ht j₀)).2 (hbig a₀ ha₀), fun a ha => ?_⟩
      rw [div_mul_cancel₀ _ (ht j₀).ne']
      exact hmin a ha
  -- choose ε with (1 + ε)^(n-1) < δ
  have hcont : Filter.Tendsto (fun ε : ℝ => (1 + ε) ^ (n - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have : Continuous (fun ε : ℝ => (1 + ε) ^ (n - 1)) := by fun_prop
    have h := this.tendsto 0
    simp only [add_zero, one_pow] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεδ, hε01⟩ := ((hcont.eventually (gt_mem_nhds hδ1)).and
    (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  obtain ⟨a, ha0, ha1, ha2⟩ := hε ε hε01.1 hε01.2
  have h1e : (1 + ε) ^ (n - 1) ≤ 2 ^ (n - 1) := pow_le_pow_left₀ (by linarith [hε01.1]) (by linarith [hε01.2]) _
  have haS : a ∈ S := by
    refine ⟨ha0, fun k => ?_, fun j hj => ?_⟩
    · by_cases hk : k = j₀
      · rw [hk]
        refine ha1.trans ?_
        have := mul_le_mul_of_nonneg_left h1e (ht j₀).le
        linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (ht j).le]
      · refine (ha2 k hk).trans ?_
        have : t k / (1 + ε) ≤ t k := div_le_self (ht k).le (by linarith [hε01.1])
        have h2 : 0 ≤ t j₀ * 2 ^ (n - 1) := mul_nonneg (ht j₀).le (by positivity)
        linarith [hsum_ge k]
    · exact (ha2 j hj).trans_lt (div_lt_self (ht j) (by linarith [hε01.1]))
  have := hδ a haS
  have h3 : t j₀ * (1 + ε) ^ (n - 1) < δ * t j₀ := by
    rw [mul_comm δ]; exact mul_lt_mul_of_pos_left hεδ (ht j₀)
  linarith

/-- **Cassels, Ch. 5, Theorem 2.4** (Minkowski's linear forms theorem): *let $L_j(\vec x) = \sum_i A_{ji}x_i$
($0 \le j < n$) be real linear forms of determinant $D = \det A \ne 0$ and let $t_j > 0$ satisfy
$t_0 t_1 \cdots t_{n-1} \ge \lvert D\rvert$; then there is $\vec a \in \mathbb Z^n$, $\vec a \ne \vec 0$, with
$\lvert L_0(\vec a)\rvert \le t_0$ and $\lvert L_j(\vec a)\rvert < t_j$ for $j \ne 0$.* (Cassels' $L_1$ is $L_0$ here.)
Proof as Cassels': apply `minkowski_linear_forms_le` to $t_0(1+\varepsilon)^{n-1}$, $t_j/(1+\varepsilon)$ and use that only
finitely many integral points are involved. -/
@[kb "cassels1978" "Ch. 5, Thm. 2.4, p. 71"]
theorem minkowski_linear_forms (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (hprod : |A.det| ≤ ∏ j, t j) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ |(A *ᵥ fun i => (a i : ℝ)) ⟨0, hn⟩| ≤ t ⟨0, hn⟩ ∧
      ∀ j, j ≠ ⟨0, hn⟩ → |(A *ᵥ fun i => (a i : ℝ)) j| < t j :=
  minkowski_linear_forms_at ⟨0, hn⟩ A hA t ht hprod

/-- **Cassels, Ch. 5, Theorem 2.1** (Blichfeldt): *let $k$ be a positive integer and $\mathcal S \subseteq \mathbb R^n$ a
(measurable) set with $v(\mathcal S) > k$; then there are $k + 1$ distinct points $\vec s_0, \dots, \vec s_k \in \mathcal S$
with $\vec s_i - \vec s_j \in \mathbb Z^n$ for all $i, j$.* Proof as Cassels' (the integral form on p. 69): the translates
of $\mathcal S$ by $\mathbb Z^n$, restricted to the unit cube, have total volume $v(\mathcal S) > k$, so some point of
the cube lies in $k + 1$ of them. -/
@[kb "cassels1978" "Ch. 5, Thm. 2.1, p. 68"]
theorem blichfeldt {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (k : ℕ) (hvol : (k : ENNReal) < volume S) :
    ∃ s : Fin (k + 1) → (Fin n → ℝ), Function.Injective s ∧ (∀ i, s i ∈ S) ∧
      ∀ i j, ∃ u : Fin n → ℤ, s i - s j = fun l => (u l : ℝ) := by
  classical
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume
  set F := fundamentalDomain (Pi.basisFun ℝ (Fin n)) with hFdef
  have hF : volume F = 1 := by
    have : Matrix.of ⇑(Pi.basisFun ℝ (Fin n)) = 1 := by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp [hFdef, this]
  set G := (stdLattice n).toAddSubgroup
  have : Countable G := (inferInstance : Countable (stdLattice n))
  set f : (Fin n → ℝ) → ENNReal := S.indicator 1 with hf
  have hmeas : ∀ g : G, Measurable fun x => f (g +ᵥ x) := fun g =>
    (measurable_one.indicator hS).comp (measurable_const_add _)
  have htot : volume S = ∫⁻ x in F, ∑' g : G, f (g +ᵥ x) := by
    rw [← lintegral_indicator_one hS, fund.lintegral_eq_tsum'' f, lintegral_tsum]
    exact fun g => (hmeas g).aemeasurable
  obtain ⟨x, hx⟩ : ∃ x, (k : ENNReal) < ∑' g : G, f (g +ᵥ x) := by
    by_contra hno
    push Not at hno
    have : ∫⁻ x in F, ∑' g : G, f (g +ᵥ x) ≤ ∫⁻ _ in F, (k : ENNReal) := lintegral_mono fun x => hno x
    rw [setLIntegral_const, hF, mul_one, ← htot] at this
    exact absurd hvol (not_lt.2 this)
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hx
  obtain ⟨T, hT⟩ := hx
  set T' := T.filter fun g => g +ᵥ x ∈ S with hT'
  have hcard : k < T'.card := by
    have : ∑ g ∈ T, f (g +ᵥ x) = (T'.card : ENNReal) := by
      rw [hT', Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases h : g +ᵥ x ∈ S <;> simp [hf, h]
    rw [this] at hT
    exact_mod_cast hT
  set e := T'.equivFin.symm
  refine ⟨fun i => ((e (Fin.castLE hcard i) : G) : Fin n → ℝ) + x, ?_, fun i => ?_, fun i j => ?_⟩
  · intro i j hij
    have h1 : ((e (Fin.castLE hcard i) : G) : Fin n → ℝ) = ((e (Fin.castLE hcard j) : G) : Fin n → ℝ) :=
      add_right_cancel hij
    have h2 := Subtype.ext (Subtype.ext h1)
    exact Fin.castLE_injective _ (e.injective h2)
  · have := (Finset.mem_filter.1 (e (Fin.castLE hcard i)).2).2
    simpa [AddSubgroup.vadd_def, vadd_eq_add] using this
  · have hmem : ((e (Fin.castLE hcard i) : G) : Fin n → ℝ) - ((e (Fin.castLE hcard j) : G) : Fin n → ℝ) ∈
        stdLattice n := sub_mem (e (Fin.castLE hcard i) : G).2 (e (Fin.castLE hcard j) : G).2
    obtain ⟨u, hu⟩ := mem_stdLattice.1 hmem
    refine ⟨u, ?_⟩
    rw [← hu]
    funext l
    simp only [Pi.sub_apply, Pi.add_apply]
    ring

/-! ### An application: Cassels, Ch. 6, Lemma 8.1 (small zeros, Aubry's method) -/

section Aubry

variable {R : Type*} [CommRing R]

/-- $f(\vec x) = \sum_{i,j} f_{ij}x_ix_j$. -/
def qv (F : Matrix (Fin n) (Fin n) R) (x : Fin n → R) : R := ∑ i, ∑ j, F i j * x i * x j

/-- $f(\vec x, \vec y) = \sum_{i,j} f_{ij}x_iy_j$. -/
def bv (F : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) : R := ∑ i, ∑ j, F i j * x i * y j

theorem qv_comb (F : Matrix (Fin n) (Fin n) R) (hF : ∀ i j, F i j = F j i) (p q : R) (x y : Fin n → R) :
    qv F (p • x + q • y) = p ^ 2 * qv F x + 2 * p * q * bv F x y + q ^ 2 * qv F y := by
  have h : ∀ i j, F i j * (p • x + q • y) i * (p • x + q • y) j = p ^ 2 * (F i j * x i * x j) +
      p * q * (F i j * x i * y j) + p * q * (F j i * x j * y i) + q ^ 2 * (F i j * y i * y j) := by
    intro i j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hF j i]; ring
  simp only [qv, bv, h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => F j i * x j * y i)]
  ring

theorem bv_comb (F : Matrix (Fin n) (Fin n) R) (p q : R) (x y z : Fin n → R) :
    bv F x (p • y + q • z) = p * bv F x y + q * bv F x z := by
  simp only [bv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bv_self (F : Matrix (Fin n) (Fin n) R) (x : Fin n → R) : bv F x x = qv F x := rfl

theorem qv_cast (F : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    qv (F.map (Int.cast : ℤ → ℝ)) (fun i => (x i : ℝ)) = ((qv F x : ℤ) : ℝ) := by
  simp [qv]

theorem bv_cast (F : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    bv (F.map (Int.cast : ℤ → ℝ)) (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) = ((bv F x y : ℤ) : ℝ) := by
  simp [bv]

theorem abs_bv_le (F : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) (X Y : ℝ) (hx : ∀ i, |x i| ≤ X)
    (hy : ∀ i, |y i| ≤ Y) : |bv F x y| ≤ (∑ i, ∑ j, |F i j|) * X * Y := by
  unfold bv
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
  have hX : 0 ≤ X := (abs_nonneg _).trans (hx i)
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hx i) (hy j) (abs_nonneg _) hX) (abs_nonneg _)

theorem qv_smul (F : Matrix (Fin n) (Fin n) R) (hF : ∀ i j, F i j = F j i) (p : R) (x : Fin n → R) :
    qv F (p • x) = p ^ 2 * qv F x := by
  have := qv_comb F hF p 0 x x
  simp only [zero_smul, add_zero] at this
  rw [this]; ring

/-- **Cassels, Ch. 6, Lemma 8.1** (small zeros of an isotropic form; Aubry's method): *let
$f(\vec x) = \sum_{i,j} f_{ij}x_ix_j$ with $f_{ij} = f_{ji} \in \mathbb Z$ be isotropic; then there is
$\vec a \in \mathbb Z^n$, $\vec a \ne \vec 0$, with $f(\vec a) = 0$ and $\max_j\lvert a_j\rvert \le (3F)^{(n-1)/2}$,
where $F = \sum_{i,j}\lvert f_{ij}\rvert$.* Isotropy is given as a nonzero integral zero (equivalent to a nonzero
rational zero by clearing denominators); $f \ne 0$ is assumed (for $f = 0$ the bound $0$ fails, so Cassels' $f$ is
tacitly nonzero). Proof as Cassels': take a zero $\vec a$ of least sup norm $A = \lvert a_k\rvert$; if $A \ge 2$, the
linear forms theorem (`minkowski_linear_forms_at`, Cassels' Corollary to Theorem 2.4) gives $\vec b$ with
$0 < \lvert b_k\rvert < A$ and $\lvert b_ka_j/a_k - b_j\rvert \le A^{-1/(n-1)}$; then
$\vec a^{*} = f(\vec b)\vec a - 2f(\vec a, \vec b)\vec b$ is a nonzero zero with $\lVert\vec a^{*}\rVert \le
3FA\lVert\vec\delta\rVert^{2}$, $\vec\delta = \vec b - (b_k/a_k)\vec a$, and minimality gives the bound. The sharpness
example (8.6) is not formalized. -/
@[kb "cassels1978" "Ch. 6, Lemma 8.1, pp. 87–89"]
theorem aubry (F : Matrix (Fin n) (Fin n) ℤ) (hsym : ∀ i j, F i j = F j i) (hF0 : F ≠ 0)
    (hiso : ∃ a : Fin n → ℤ, a ≠ 0 ∧ qv F a = 0) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ qv F a = 0 ∧
      ∀ i, (|a i| : ℝ) ≤ (3 * ∑ i, ∑ j, |(F i j : ℝ)|) ^ (((n : ℝ) - 1) / 2) := by
  classical
  set Fs : ℝ := ∑ i, ∑ j, |(F i j : ℝ)| with hFs
  set Fr : Matrix (Fin n) (Fin n) ℝ := F.map (Int.cast : ℤ → ℝ) with hFr
  have hsymr : ∀ i j, Fr i j = Fr j i := fun i j => by simp [hFr, hsym i j]
  have hFsr : ∑ i, ∑ j, |Fr i j| = Fs := by simp [hFr, hFs]
  set P : ℕ → Prop := fun N => ∃ a : Fin n → ℤ, a ≠ 0 ∧ qv F a = 0 ∧ ∀ i, (a i).natAbs ≤ N with hP
  have hex : ∃ N, P N := by
    obtain ⟨a, ha0, haz⟩ := hiso
    exact ⟨∑ i, (a i).natAbs, a, ha0, haz, fun i =>
      Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩
  set A := Nat.find hex with hAdef
  obtain ⟨a, ha0, haz, haA⟩ := Nat.find_spec hex
  have hmin : ∀ a' : Fin n → ℤ, a' ≠ 0 → qv F a' = 0 → ∃ i, A ≤ (a' i).natAbs := by
    intro a' h0 hz
    by_contra hno
    push Not at hno
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
    have h1 : 1 ≤ (a' i).natAbs := Int.natAbs_pos.2 hi
    have hle := Nat.find_min' hex (show P (A - 1) from ⟨a', h0, hz, fun j => by have := hno j; omega⟩)
    have := hno i
    omega
  obtain ⟨k, hk⟩ := hmin a ha0 haz
  have hak : (a k).natAbs = A := le_antisymm (haA k) hk
  have hA1 : 1 ≤ A := by rw [← hak]; exact Int.natAbs_pos.2 (fun h => by
    have := hmin a ha0 haz; obtain ⟨i, hi⟩ := Function.ne_iff.1 ha0
    have := haA i; have h1 : 1 ≤ (a i).natAbs := Int.natAbs_pos.2 hi; rw [h] at hak; simp at hak; omega)
  -- the entries of `F`
  have hFs1 : 1 ≤ Fs := by
    obtain ⟨i, j, hij⟩ : ∃ i j, F i j ≠ 0 := by
      by_contra h; push Not at h; exact hF0 (Matrix.ext fun i j => h i j)
    have h1 : (1 : ℝ) ≤ |(F i j : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hij
    refine h1.trans ?_
    refine (Finset.single_le_sum (f := fun j => |(F i j : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum (f := fun i => ∑ j, |(F i j : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  -- reduce to a bound on `A`
  suffices hAX : (A : ℝ) ≤ (3 * Fs) ^ (((n : ℝ) - 1) / 2) by
    refine ⟨a, ha0, haz, fun i => ?_⟩
    have e : ((a i).natAbs : ℝ) = |(a i : ℝ)| := by simp [Nat.cast_natAbs, Int.cast_abs]
    rw [← e]
    exact (by exact_mod_cast haA i : ((a i).natAbs : ℝ) ≤ A).trans hAX
  have hn1 : 1 ≤ n := k.pos
  by_cases hn2 : n = 1
  · exfalso
    subst hn2
    apply hF0
    have hk0 : k = 0 := Subsingleton.elim _ _
    have h := haz
    simp only [qv, Fin.sum_univ_one] at h
    have ha0' : a 0 ≠ 0 := fun h0 => ha0 (funext fun i => by rw [Subsingleton.elim i 0, h0]; rfl)
    have : F 0 0 = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact (mul_eq_zero.1 h').resolve_right ha0'
      · exact absurd h' ha0'
    exact Matrix.ext fun i j => by rw [Subsingleton.elim i 0, Subsingleton.elim j 0, this]; rfl
  have hn2' : 2 ≤ n := by omega
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2'
    linarith
  rcases Nat.lt_or_ge A 2 with hA2 | hA2
  · have : A = 1 := by omega
    rw [this, Nat.cast_one]
    exact Real.one_le_rpow (by linarith) hexp
  -- the main case `A ≥ 2`
  have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA2
  have hApos : (0 : ℝ) < A := by linarith
  set ak : ℝ := (a k : ℝ) with hakdef
  have hakabs : |ak| = A := by
    rw [hakdef, ← hak]; simp [Nat.cast_natAbs, Int.cast_abs]
  have hak0 : ak ≠ 0 := fun h => by rw [h, abs_zero] at hakabs; linarith
  have habsa : ∀ i, |(a i : ℝ)| ≤ A := fun i => by
    have e : ((a i).natAbs : ℝ) = |(a i : ℝ)| := by simp [Nat.cast_natAbs, Int.cast_abs]
    rw [← e]; exact_mod_cast haA i
  set θ : Fin n → ℝ := fun j => (a j : ℝ) / ak with hθ
  have hθ1 : ∀ j, |θ j| ≤ 1 := fun j => by
    rw [hθ, abs_div, hakabs, div_le_one hApos]; exact habsa j
  have hn1r : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2'
    linarith
  set D : ℝ := (A : ℝ) ^ (-1 / ((n : ℝ) - 1)) with hD
  have hDpos : 0 < D := Real.rpow_pos_of_pos hApos _
  have hD1 : D < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by
    apply div_neg_of_neg_of_pos (by norm_num); linarith)
  -- the linear forms
  set w : Fin n → ℝ := fun j => if j = k then -2 else -θ j with hw
  set M : Matrix (Fin n) (Fin n) ℝ :=
    -(1 + Matrix.replicateCol (Fin 1) w * Matrix.replicateRow (Fin 1) (Pi.single k (1 : ℝ))) with hM
  have hMv : ∀ x : Fin n → ℝ, ∀ i, (M *ᵥ x) i = -(x i + w i * x k) := by
    intro x i
    simp only [hM, Matrix.neg_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Pi.neg_apply, Pi.add_apply]
    congr 2
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hMk : ∀ x : Fin n → ℝ, (M *ᵥ x) k = x k := fun x => by rw [hMv]; simp [hw]; ring
  have hMj : ∀ x : Fin n → ℝ, ∀ j, j ≠ k → (M *ᵥ x) j = θ j * x k - x j := fun x j hj => by
    rw [hMv]; simp [hw, hj]; ring
  have hdet : |M.det| = 1 := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) w (Pi.single k (1 : ℝ))
    rw [hM, Matrix.det_neg]
    erw [h]
    have : Pi.single k (1 : ℝ) ⬝ᵥ w = -2 := by simp [hw]
    rw [this, abs_mul]; norm_num
  have hdet0 : M.det ≠ 0 := fun h => by rw [h, abs_zero] at hdet; norm_num at hdet
  set t : Fin n → ℝ := fun j => if j = k then (A : ℝ) else D with ht
  have htpos : ∀ j, 0 < t j := fun j => by simp only [ht]; split_ifs <;> assumption
  have hprod : |M.det| ≤ ∏ j, t j := by
    rw [hdet, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    have : ∏ j ∈ Finset.univ.erase k, t j = D ^ (n - 1) := by
      rw [Finset.prod_congr rfl (fun j hj => by simp [ht, Finset.ne_of_mem_erase hj] : ∀ j ∈ Finset.univ.erase k, t j = D)]
      simp
    rw [this]
    simp only [ht, ite_true]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn1]; ring
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hApos.le, hcast,
      div_mul_cancel₀ _ (by linarith : (n : ℝ) - 1 ≠ 0), Real.rpow_neg_one, mul_inv_cancel₀ hApos.ne']
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin n, j ≠ k := by
    by_cases hk0 : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk0; simp at hk0⟩
    · exact ⟨⟨0, by omega⟩, fun h => by rw [← h] at hk0; simp at hk0⟩
  obtain ⟨b, hb0, hbj₀, hbj⟩ := minkowski_linear_forms_at j₀ M hdet0 t htpos hprod
  set br : Fin n → ℝ := fun i => (b i : ℝ) with hbr
  have hbk : |br k| < A := by
    have := hbj k (Ne.symm hj₀); rw [hMk] at this; simpa [ht] using this
  have happ : ∀ j, j ≠ k → |θ j * br k - br j| ≤ D := by
    intro j hj
    by_cases hjj : j = j₀
    · have := hbj₀; rw [← hjj, hMj _ _ hj] at this; simpa [ht, hj] using this
    · have := hbj j hjj; rw [hMj _ _ hj] at this; simpa [ht, hj] using this.le
  -- `b` is shorter than `a`
  have hbkA : |br k| ≤ (A : ℝ) - 1 := by
    have e : ((b k).natAbs : ℝ) = |br k| := by simp [hbr, Nat.cast_natAbs, Int.cast_abs]
    rw [← e] at hbk ⊢
    have : (b k).natAbs < A := by exact_mod_cast hbk
    have : (b k).natAbs ≤ A - 1 := by omega
    calc ((b k).natAbs : ℝ) ≤ ((A - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = (A : ℝ) - 1 := by push_cast [Nat.cast_sub hA1]; ring
  have hbshort : ∀ i, (b i).natAbs ≤ A - 1 := by
    intro i
    have hlt : |br i| < A := by
      by_cases hi : i = k
      · rw [hi]; linarith
      · have h1 := happ i hi
        have h2 : |θ i * br k| ≤ (A : ℝ) - 1 := by
          rw [abs_mul]; nlinarith [hθ1 i, abs_nonneg (br k), abs_nonneg (θ i)]
        have : |br i| ≤ |θ i * br k| + |θ i * br k - br i| := by
          have := abs_sub (θ i * br k) (θ i * br k - br i)
          simpa using this
        linarith
    have e : ((b i).natAbs : ℝ) = |br i| := by simp [hbr, Nat.cast_natAbs, Int.cast_abs]
    rw [← e] at hlt
    have : (b i).natAbs < A := by exact_mod_cast hlt
    omega
  have hqb : qv F b ≠ 0 := by
    intro hz
    have := Nat.find_min' hex (show P (A - 1) from ⟨b, hb0, hz, hbshort⟩)
    omega
  -- the new zero
  set as : Fin n → ℤ := (qv F b) • a + (-2 * bv F a b) • b with has
  have hasz : qv F as = 0 := by
    rw [has, qv_comb F hsym, haz]
    ring
  have has0 : as ≠ 0 := by
    intro h0
    have h1 : (qv F b) • a = (2 * bv F a b) • b := by
      have := congrArg (fun v => v + (2 * bv F a b) • b) h0
      simp only [has, zero_add] at this
      rw [← this]; ext i; simp
    have h2 := congrArg (qv F) h1
    rw [qv_smul F hsym, qv_smul F hsym, haz, mul_zero] at h2
    have h3 : 2 * bv F a b = 0 := by
      have := h2.symm
      rcases mul_eq_zero.1 this with h | h
      · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
      · exact absurd h hqb
    rw [h3, zero_smul] at h1
    apply ha0
    funext i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hqb
  -- the real expression of `as`
  set ar : Fin n → ℝ := fun i => (a i : ℝ) with har
  set m : ℝ := br k / ak with hm
  set δ : Fin n → ℝ := br - m • ar with hδ
  have hbrd : br = m • ar + (1 : ℝ) • δ := by rw [hδ, one_smul]; abel
  have hqar : qv Fr ar = 0 := by rw [qv_cast, haz]; simp
  have hbab : ((bv F a b : ℤ) : ℝ) = bv Fr ar δ := by
    rw [← bv_cast F a b]
    show bv Fr ar br = _
    rw [hbrd, bv_comb, bv_self, hqar]; ring
  have hqbb : ((qv F b : ℤ) : ℝ) = 2 * m * bv Fr ar δ + qv Fr δ := by
    rw [← qv_cast F b]
    show qv Fr br = _
    rw [hbrd, qv_comb Fr hsymr, hqar]; ring
  have hasr : ∀ i, (as i : ℝ) = qv Fr δ * ar i - 2 * bv Fr ar δ * δ i := by
    intro i
    have hb : br i = m * ar i + δ i := by
      have := congrFun hbrd i; simpa using this
    simp only [has, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hqbb, hbab]
    have : (b i : ℝ) = br i := rfl
    rw [this, hb]; ring
  have hδD : ∀ i, |δ i| ≤ D := by
    intro i
    by_cases hi : i = k
    · rw [hi]
      have : δ k = 0 := by simp [hδ, hm, har, ← hakdef]; field_simp; ring
      rw [this, abs_zero]; exact hDpos.le
    · have : δ i = -(θ i * br k - br i) := by
        simp only [hδ, hm, har, hθ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
      rw [this, abs_neg]; exact happ i hi
  have hqd : |qv Fr δ| ≤ Fs * D * D := by
    rw [← bv_self]; have := abs_bv_le Fr δ δ D D hδD hδD; rwa [hFsr] at this
  have hbd : |bv Fr ar δ| ≤ Fs * A * D := by
    have := abs_bv_le Fr ar δ A D habsa hδD; rwa [hFsr] at this
  have hasb : ∀ i, |(as i : ℝ)| ≤ 3 * Fs * A * D ^ 2 := by
    intro i
    rw [hasr]
    have h1 : |qv Fr δ * ar i| ≤ Fs * D * D * A := by
      rw [abs_mul]; exact mul_le_mul hqd (habsa i) (abs_nonneg _) (by positivity)
    have h2 : |2 * bv Fr ar δ * δ i| ≤ 2 * (Fs * A * D) * D := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbd (by norm_num)) (hδD i) (abs_nonneg _) (by positivity)
    calc |qv Fr δ * ar i - 2 * bv Fr ar δ * δ i| ≤ |qv Fr δ * ar i| + |2 * bv Fr ar δ * δ i| := abs_sub _ _
      _ ≤ Fs * D * D * A + 2 * (Fs * A * D) * D := add_le_add h1 h2
      _ = 3 * Fs * A * D ^ 2 := by ring
  obtain ⟨i, hi⟩ := hmin as has0 hasz
  have hAi : (A : ℝ) ≤ |(as i : ℝ)| := by
    have e : ((as i).natAbs : ℝ) = |(as i : ℝ)| := by simp [Nat.cast_natAbs, Int.cast_abs]
    rw [← e]; exact_mod_cast hi
  have key : 1 ≤ 3 * Fs * D ^ 2 := by
    have := hAi.trans (hasb i)
    have : (A : ℝ) * 1 ≤ A * (3 * Fs * D ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hApos
  -- conclude
  set e : ℝ := 2 / ((n : ℝ) - 1) with he
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  have hD2 : D ^ 2 = (A : ℝ) ^ (-e) := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hApos.le, he]; congr 1; push_cast; ring
  have hAe : (A : ℝ) ^ e ≤ 3 * Fs := by
    rw [hD2] at key
    have hpos : 0 < (A : ℝ) ^ e := Real.rpow_pos_of_pos hApos _
    have : (A : ℝ) ^ e * (A : ℝ) ^ (-e) = 1 := by
      rw [← Real.rpow_add hApos, add_neg_cancel, Real.rpow_zero]
    nlinarith
  have hfin : (A : ℝ) = ((A : ℝ) ^ e) ^ (((n : ℝ) - 1) / 2) := by
    rw [← Real.rpow_mul hApos.le, he]
    rw [show 2 / ((n : ℝ) - 1) * (((n : ℝ) - 1) / 2) = 1 by field_simp, Real.rpow_one]
  rw [hfin]
  exact Real.rpow_le_rpow (Real.rpow_pos_of_pos hApos _).le hAe hexp

end Aubry

end QuadFormsKB.Cassels
