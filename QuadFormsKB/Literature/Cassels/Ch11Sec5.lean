/-
# Cassels, Chapter 11, §5: simultaneous bases of two lattices

**Layer:** $\mathbb Z$-lattices `Lat ℚ n` in $V = \mathbb Q^n$ (Cassels' $\mathbb Z$ is $\mathcal O_{\mathbb Q}$); a basis
of a lattice $\Lambda$ is a family $b_0, \dots, b_{n-1}$, linearly independent over $\mathbb Q$, whose
$\mathbb Z$-span is $\Lambda$; Cassels' index $I(\Gamma, \Lambda)$ = `casselsI` and "same determinant" = equal
`latIndex` (`Ch11Sec4Index.lean`). Theorem 5.1 itself (elementary divisors) is the Smith normal form, used from
Mathlib (`Submodule.smithNormalForm`).

**Proves**
* Theorem 5.1, Corollary (p. 223) (`exists_basis_of_casselsI_prime`): if $I(\Gamma, \Lambda) = p$ is prime, there are
  $b_0, \dots, b_{n-1}$ with $pb_0, b_1, \dots, b_{n-1}$ a basis of $\Gamma$ and $b_0, \dots, b_{n-2}, pb_{n-1}$ a basis
  of $\Lambda$ (0-based; the displays (5.9), (5.10) are garbled in the scan and are read from the proof, "the Theorem
  applied to $p\Gamma \subseteq \Lambda$").
* Lemma 5.1 is in `Ch11Sec5Lemma.lean`; the helpers below (`Good`, …) prepare it.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec4Index

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Tamagawa.SiegelSpace

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-! ### Simultaneous bases: the predicate `Good` and coordinates -/

section Good

theorem exists_int_eq_aux (a : 𝓞 ℚ) : ∃ z : ℤ, a = (z : 𝓞 ℚ) := by
  obtain ⟨z, hz⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) a
  exact ⟨z, by rw [← hz]; simp⟩

theorem smul_eq_rat_smul_aux (a : 𝓞 ℚ) (x : Fin n → ℚ) : a • x = ((a : ℚ)) • x := by
  rw [Algebra.smul_def]; rfl

theorem int_smul_eq_aux (z : ℤ) (x : Fin n → ℚ) : ((z : 𝓞 ℚ)) • x = (z : ℚ) • x := by
  rw [smul_eq_rat_smul_aux]; simp

/-- **A pair of lattices with a simultaneous diagonal basis:** $b$ is a basis of $\Lambda$ and $s_jb_j$ a basis of
$\Gamma$ with $s_j > 0$. -/
def Good (Λ Γ : Lat ℚ n) (b : Fin n → Fin n → ℚ) (s : Fin n → ℚ) : Prop :=
  Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b) ∧
  Γ.1 = Submodule.span (𝓞 ℚ) (Set.range fun j => s j • b j) ∧ ∀ j, 0 < s j

theorem top_le_span_of_lat {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ}
    (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) : ⊤ ≤ Submodule.span ℚ (Set.range b) := by
  rw [← Λ.2.span_eq_top, Submodule.span_le]
  intro x hx
  have : x ∈ Submodule.span (𝓞 ℚ) (Set.range b) := h ▸ hx
  exact Submodule.span_le_restrictScalars (𝓞 ℚ) ℚ _ this

theorem linIndep_of_lat {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ}
    (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) : LinearIndependent ℚ b :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_of_lat h) (by simp)

/-- The $\mathbb Q$-basis of $\mathbb Q^n$ given by $b$. -/
def basisOfLat {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) :
    Module.Basis (Fin n) ℚ (Fin n → ℚ) :=
  Module.Basis.mk (linIndep_of_lat h) (top_le_span_of_lat h)

theorem basisOfLat_apply {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b))
    (j : Fin n) : basisOfLat h j = b j := by simp [basisOfLat]

/-- **Coordinates:** $x \in \mathrm{span}_{\mathcal O}(s_jb_j)$ iff each $b$-coordinate of $x$ is an integer
multiple of $s_k$. -/
theorem mem_span_smul_iff {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ}
    (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) (s : Fin n → ℚ) (x : Fin n → ℚ) :
    x ∈ Submodule.span (𝓞 ℚ) (Set.range fun j => s j • b j) ↔
      ∀ k, ∃ z : ℤ, (z : ℚ) * s k = (basisOfLat h).repr x k := by
  set B := basisOfLat h with hB
  constructor
  · intro hx k
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨z, hz⟩ := exists_int_eq_aux (c k)
    refine ⟨z, ?_⟩
    have hrep : ∀ j, B.repr (b j) = Finsupp.single j 1 := fun j => by
      rw [show b j = B j from (basisOfLat_apply h j).symm, B.repr_self]
    simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_rat_smul_aux, map_smul,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [hrep, hz]; simp
    · intro j _ hj
      rw [hrep]
      simp [Finsupp.single_apply, hj]
    · simp
  · intro hx
    choose z hz using hx
    rw [← B.sum_repr x]
    refine Submodule.sum_mem _ fun k _ => ?_
    have e : B.repr x k • B k = (z k : 𝓞 ℚ) • (s k • b k) := by
      rw [← hz k, show B k = b k from basisOfLat_apply h k, int_smul_eq_aux, mul_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem instPID_aux : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
    Rat.ringOfIntegersEquiv.symm.surjective

theorem inv_mulVec_mulVec_aux (γ : GL (Fin n) ℚ) (y : Fin n → ℚ) : γ⁻¹.val *ᵥ (γ.val *ᵥ y) = y := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

/-- The integral matrix $P = t\gamma^{-1}\delta$ for lattices $\delta\mathcal O^n \supseteq$ ... -/
theorem exists_intMatrix_aux {Λ Γ : Lat ℚ n} {t : ℕ} (h : ∀ x ∈ Λ.1, (t : 𝓞 ℚ) • x ∈ Γ.1)
    {γ δ : GL (Fin n) ℚ} (hγ : Γ.1 = latOf γ) (hδ : Λ.1 = latOf δ) :
    ∃ P : Matrix (Fin n) (Fin n) (𝓞 ℚ),
      P.map (algebraMap (𝓞 ℚ) ℚ) = (t : ℚ) • (γ⁻¹.val * δ.val) := by
  have hent : ∀ i j, ((t : ℚ) • (γ⁻¹.val * δ.val)) i j ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
    intro i j
    have h1 : δ.val *ᵥ Pi.single j 1 ∈ Λ.1 := by
      rw [hδ]; exact mulVec_mem_glImage (single_one_mem_intVec j)
    have h2 := h _ h1
    rw [hγ] at h2
    obtain ⟨y, hy, hyeq⟩ := mem_glImage.mp h2
    have hy' : y = (t : ℚ) • ((γ⁻¹.val * δ.val) *ᵥ Pi.single j 1) := by
      have := congrArg (fun z => γ⁻¹.val *ᵥ z) hyeq
      simp only [inv_mulVec_mulVec_aux] at this
      rw [this, smul_eq_rat_smul_aux, ← mulVec_mulVec, Matrix.mulVec_smul]
      simp
    have := hy i
    rw [hy'] at this
    simpa [mulVec_single_one] using this
  choose P hP using hent
  exact ⟨Matrix.of P, by ext i j; exact hP i j⟩

/-- Integral coordinates, mapped by $\gamma$: $z \mapsto \gamma z$. -/
def PhiLin (γ : GL (Fin n) ℚ) : (Fin n → 𝓞 ℚ) →ₗ[𝓞 ℚ] (Fin n → ℚ) :=
  ((Matrix.mulVecLin γ.val).restrictScalars (𝓞 ℚ)) ∘ₗ
    (LinearMap.pi fun i => (Algebra.linearMap (𝓞 ℚ) ℚ) ∘ₗ LinearMap.proj i)

theorem PhiLin_apply (γ : GL (Fin n) ℚ) (z : Fin n → 𝓞 ℚ) : PhiLin γ z = γ.val *ᵥ intCoe z := rfl

theorem range_PhiLin (γ : GL (Fin n) ℚ) : LinearMap.range (PhiLin γ) = latOf γ := by
  ext y
  rw [LinearMap.mem_range, latOf, mem_glImage]
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨intCoe z, intCoe_mem z, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, rfl⟩ := mem_intVec_iff_exists.mp hw
    exact ⟨z, rfl⟩

theorem span_smul_range_aux {ι : Type*} (g : ι → Fin n → ℚ) (r : ℚ) :
    Submodule.span (𝓞 ℚ) (Set.range fun j => r • g j) =
      (Submodule.span (𝓞 ℚ) (Set.range g)).map (r • (LinearMap.id : (Fin n → ℚ) →ₗ[𝓞 ℚ] (Fin n → ℚ))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem mem_span_smul_range_aux {ι : Type*} (g : ι → Fin n → ℚ) {r : ℚ} (hr : r ≠ 0) (x : Fin n → ℚ) :
    x ∈ Submodule.span (𝓞 ℚ) (Set.range fun j => r • g j) ↔ r⁻¹ • x ∈ Submodule.span (𝓞 ℚ) (Set.range g) := by
  rw [span_smul_range_aux, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [hr] using hy
  · intro hx
    exact ⟨_, hx, by simp [hr]⟩

theorem span_eq_of_sign_smul_aux {ι : Type*} (e f : ι → Fin n → ℚ)
    (h : ∀ j, ∃ u : ℤ, (u = 1 ∨ u = -1) ∧ f j = (u : ℚ) • e j) :
    Submodule.span (𝓞 ℚ) (Set.range f) = Submodule.span (𝓞 ℚ) (Set.range e) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨u, -, hu⟩ := h j
    rw [hu, ← int_smul_eq_aux]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨u, hu1, hu⟩ := h j
    have : e j = (u : 𝓞 ℚ) • f j := by
      rw [int_smul_eq_aux, hu, smul_smul]
      rcases hu1 with rfl | rfl <;> simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Diagonalization** (Smith normal form, Mathlib): if $t\Lambda \subseteq \Gamma$ then there is a basis $b$ of
$\Lambda$ and positive $s_j$ with $s_jb_j$ a basis of $\Gamma$. -/
theorem exists_good {Λ Γ : Lat ℚ n} {t : ℕ} (ht : 0 < t) (h : ∀ x ∈ Λ.1, (t : 𝓞 ℚ) • x ∈ Γ.1) :
    ∃ b s, Good Λ Γ b s := by
  classical
  haveI := instPID_aux
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing Γ
  obtain ⟨δ, hδ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing Λ
  obtain ⟨P, hP⟩ := exists_intMatrix_aux h hγ hδ
  have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  have hdet : P.det ≠ 0 := by
    intro h0
    have h1 : (P.map (algebraMap (𝓞 ℚ) ℚ)).det = 0 := by
      have := RingHom.map_det (algebraMap (𝓞 ℚ) ℚ) P
      rw [h0, map_zero] at this
      exact this.symm
    rw [hP, Matrix.det_smul, Matrix.det_mul] at h1
    have h2 := (Matrix.isUnits_det_units γ⁻¹).ne_zero
    have h3 := (Matrix.isUnits_det_units δ).ne_zero
    simp only [mul_eq_zero, pow_eq_zero_iff', htQ, false_and, false_or] at h1
    rcases h1 with h1 | h1
    · exact h2 h1
    · exact h3 h1
  have hrank : Module.finrank (𝓞 ℚ) (LinearMap.range P.mulVecLin) =
      Module.finrank (𝓞 ℚ) (Fin n → 𝓞 ℚ) :=
    LinearMap.finrank_range_of_inj (mulVec_injective_of_det_ne_zero hdet)
  obtain ⟨bM, a, ab, hab⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun (𝓞 ℚ) (Fin n)) hrank
  let e : Fin n → Fin n → ℚ := fun j => PhiLin γ (bM j)
  have hane : ∀ j, a j ≠ 0 := by
    intro j hj
    have := ab.ne_zero j
    apply this
    apply Subtype.ext
    rw [hab j, hj, zero_smul]; rfl
  -- Γ = span e
  have hΓe : Γ.1 = Submodule.span (𝓞 ℚ) (Set.range e) := by
    rw [hγ, ← range_PhiLin, ← Submodule.map_top, ← bM.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  -- N = span (a • bM)
  have hNspan : LinearMap.range P.mulVecLin = Submodule.span (𝓞 ℚ) (Set.range fun j => a j • bM j) := by
    have h1 := congrArg (Submodule.map (LinearMap.range P.mulVecLin).subtype) ab.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    rw [← h1]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, Submodule.subtype_apply, hab]
  -- Φ (P w) = t • δ w
  have hΦP : ∀ w : Fin n → 𝓞 ℚ, PhiLin γ (P *ᵥ w) = (t : ℚ) • (δ.val *ᵥ intCoe w) := by
    intro w
    rw [PhiLin_apply, ← map_mulVec_intCoe, hP, Matrix.smul_mulVec, Matrix.mulVec_smul, ← mulVec_mulVec,
      mulVec_inv_mulVec]
  have hC3 : ∀ x, (∃ y ∈ Λ.1, (t : ℚ) • y = x) ↔
      x ∈ Submodule.map (PhiLin γ) (LinearMap.range P.mulVecLin) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hδ] at hy
      obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hy
      obtain ⟨z, rfl⟩ := mem_intVec_iff_exists.mp hw
      exact ⟨P *ᵥ z, ⟨z, rfl⟩, hΦP z⟩
    · rintro ⟨m, ⟨z, rfl⟩, rfl⟩
      refine ⟨δ.val *ᵥ intCoe z, ?_, (hΦP z).symm⟩
      rw [hδ]; exact mulVec_mem_glImage (intCoe_mem z)
  have hmapspan : Submodule.map (PhiLin γ) (LinearMap.range P.mulVecLin) =
      Submodule.span (𝓞 ℚ) (Set.range fun j => a j • e j) := by
    rw [hNspan, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, map_smul, e]
  have hC4 : ∀ x, x ∈ Λ.1 ↔ (t : ℚ) • x ∈ Submodule.span (𝓞 ℚ) (Set.range fun j => a j • e j) := by
    intro x
    rw [← hmapspan, ← hC3]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have := smul_right_injective (Fin n → ℚ) htQ hyx
      rwa [← this]
  have hrQ : ((1 : ℚ) / t) ≠ 0 := by positivity
  set aq : Fin n → ℚ := fun j => algebraMap (𝓞 ℚ) ℚ (a j) with haq
  have haq0 : ∀ j, aq j ≠ 0 := fun j => by
    simpa [haq] using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 (hane j)
  refine ⟨fun j => ((1 : ℚ) / t) • (a j • e j), fun j => (t : ℚ) / |aq j|, ?_, ?_, ?_⟩
  · ext x
    rw [mem_span_smul_range_aux _ hrQ, hC4]
    simp
  · rw [hΓe]
    symm
    apply span_eq_of_sign_smul_aux
    intro j
    refine ⟨if 0 < aq j then 1 else -1, ?_, ?_⟩
    · split_ifs <;> simp
    · rw [smul_smul, smul_eq_rat_smul_aux, smul_smul]
      congr 1
      have h0 := haq0 j
      show (t : ℚ) / |aq j| * (1 / t) * aq j = _
      split_ifs with hp
      · rw [abs_of_pos hp]; push_cast; field_simp
      · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 hp) h0)]; push_cast; field_simp
  · intro j
    have := abs_pos.2 (haq0 j)
    positivity

/-! ### Sorting the diagonal into a divisibility chain -/

/-- $x \mid y$ in the rational sense: $y/x \in \mathbb Z$. -/
def DvdQ (x y : ℚ) : Prop := ∃ z : ℤ, y = z * x

theorem DvdQ.refl (x : ℚ) : DvdQ x x := ⟨1, by simp⟩

theorem DvdQ.trans {x y z : ℚ} (h1 : DvdQ x y) (h2 : DvdQ y z) : DvdQ x z := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨b * a, by push_cast; ring⟩

theorem gcd_lcm_aux (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    ∃ (u w α β : ℤ) (d : ℚ), 0 < u ∧ 0 < w ∧ α * u + β * w = 1 ∧ 0 < d ∧ x = u * d ∧ y = w * d ∧
      (∀ z, DvdQ x z → DvdQ y z → DvdQ (u * w * d) z) := by
  have key : ∃ u w : ℤ, 0 < u ∧ 0 < w ∧ IsCoprime u w ∧ x / y = (u : ℚ) / (w : ℚ) := by
    have hqpos : 0 < x / y := div_pos hx hy
    refine ⟨(x / y).num, ((x / y).den : ℤ), Rat.num_pos.2 hqpos, by exact_mod_cast (x / y).den_pos, ?_, ?_⟩
    · rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using (x / y).reduced
    · push_cast; exact (Rat.num_div_den _).symm
  obtain ⟨u, w, hu, hw, hcop, hq⟩ := key
  obtain ⟨α, β, hαβ⟩ := hcop
  have hu0 : (u : ℚ) ≠ 0 := by exact_mod_cast hu.ne'
  have hw0 : (w : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  have hxd : x = u * (x / u) := by field_simp
  have hyd : y = w * (x / u) := by
    rw [div_eq_div_iff hy.ne' hw0] at hq
    field_simp
    linarith
  have hd : 0 < x / u := div_pos hx (by exact_mod_cast hu)
  refine ⟨u, w, α, β, x / u, hu, hw, hαβ, hd, hxd, hyd, ?_⟩
  rintro z ⟨m, hm⟩ ⟨m', hm'⟩
  have hmul : (m : ℚ) * u = (m' : ℚ) * w := by
    rw [hxd] at hm; rw [hyd] at hm'
    have := hm.symm.trans hm'
    apply mul_right_cancel₀ hd.ne'
    linarith
  have hmulZ : m * u = m' * w := by exact_mod_cast hmul
  have hdvd : w ∣ m := by
    have : w ∣ m * u := ⟨m', by rw [hmulZ]; ring⟩
    exact (IsCoprime.dvd_of_dvd_mul_right (by exact ⟨β, α, by linarith⟩ : IsCoprime w u)) this
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨k, ?_⟩
  rw [hm]; push_cast; field_simp

theorem mem_pair_aux {p1 p2 : Fin n → ℚ} (a b : ℤ) :
    (a : ℚ) • p1 + (b : ℚ) • p2 ∈ Submodule.span (𝓞 ℚ) {p1, p2} :=
  Submodule.add_mem _ (by rw [← int_smul_eq_aux]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (by rw [← int_smul_eq_aux]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem span_pair_eq_aux {p1 p2 q1 q2 : Fin n → ℚ} (a b c d a' b' c' d' : ℤ)
    (h1 : q1 = (a : ℚ) • p1 + (b : ℚ) • p2) (h2 : q2 = (c : ℚ) • p1 + (d : ℚ) • p2)
    (h3 : p1 = (a' : ℚ) • q1 + (b' : ℚ) • q2) (h4 : p2 = (c' : ℚ) • q1 + (d' : ℚ) • q2) :
    Submodule.span (𝓞 ℚ) {p1, p2} = Submodule.span (𝓞 ℚ) {q1, q2} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · rw [h3]; exact mem_pair_aux _ _
    · rw [h4]; exact mem_pair_aux _ _
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · rw [h1]; exact mem_pair_aux _ _
    · rw [h2]; exact mem_pair_aux _ _

theorem swap_pair (b1 b2 : Fin n → ℚ) (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    ∃ (c1 c2 : Fin n → ℚ) (l g : ℚ), 0 < l ∧ 0 < g ∧
      Submodule.span (𝓞 ℚ) {b1, b2} = Submodule.span (𝓞 ℚ) {c1, c2} ∧
      Submodule.span (𝓞 ℚ) {x • b1, y • b2} = Submodule.span (𝓞 ℚ) {l • c1, g • c2} ∧
      DvdQ x l ∧ DvdQ y l ∧ DvdQ g x ∧ DvdQ g y ∧ (∀ z, DvdQ x z → DvdQ y z → DvdQ l z) := by
  obtain ⟨u, w, α, β, d, hu, hw, hαβ, hd, rfl, rfl, hlcm⟩ := gcd_lcm_aux x y hx hy
  have hαβQ : (α : ℚ) * u + β * w = 1 := by exact_mod_cast hαβ
  have huQ : (0 : ℚ) < u := by exact_mod_cast hu
  have hwQ : (0 : ℚ) < w := by exact_mod_cast hw
  refine ⟨((-β : ℤ) : ℚ) • b1 + (α : ℚ) • b2, (u : ℚ) • b1 + (w : ℚ) • b2, u * w * d, d,
    by positivity, hd, ?_, ?_, ⟨w, by ring⟩, ⟨u, by ring⟩, ⟨u, by ring⟩, ⟨w, by ring⟩, hlcm⟩
  · refine span_pair_eq_aux (-β) α u w (-w) α u β rfl rfl ?_ ?_ <;> push_cast <;> match_scalars <;>
      first | ring1 | linear_combination (-1 : ℚ) * hαβQ
  · refine span_pair_eq_aux (-β * w) (α * u) 1 1 (-1) (α * u) 1 (β * w) ?_ ?_ ?_ ?_ <;> push_cast <;> match_scalars <;>
      first | ring1 | linear_combination (-(u * d : ℚ)) * hαβQ | linear_combination (-(w * d : ℚ)) * hαβQ

theorem span_range_update_aux (f f' : Fin n → Fin n → ℚ) {i j : Fin n}
    (hk : ∀ k, k ≠ i → k ≠ j → f' k = f k)
    (h : Submodule.span (𝓞 ℚ) {f i, f j} = Submodule.span (𝓞 ℚ) {f' i, f' j}) :
    Submodule.span (𝓞 ℚ) (Set.range f) = Submodule.span (𝓞 ℚ) (Set.range f') := by
  have hi' : f' i ∈ Submodule.span (𝓞 ℚ) (Set.range f') := Submodule.subset_span ⟨i, rfl⟩
  have hj' : f' j ∈ Submodule.span (𝓞 ℚ) (Set.range f') := Submodule.subset_span ⟨j, rfl⟩
  have hi : f i ∈ Submodule.span (𝓞 ℚ) (Set.range f) := Submodule.subset_span ⟨i, rfl⟩
  have hj : f j ∈ Submodule.span (𝓞 ℚ) (Set.range f) := Submodule.subset_span ⟨j, rfl⟩
  have hP : Submodule.span (𝓞 ℚ) {f i, f j} ≤ Submodule.span (𝓞 ℚ) (Set.range f') := by
    rw [h, Submodule.span_le]
    rintro _ (rfl | rfl) <;> assumption
  have hP' : Submodule.span (𝓞 ℚ) {f' i, f' j} ≤ Submodule.span (𝓞 ℚ) (Set.range f) := by
    rw [← h, Submodule.span_le]
    rintro _ (rfl | rfl) <;> assumption
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases h1 : k = i
    · subst h1; exact hP (Submodule.subset_span (by simp))
    by_cases h2 : k = j
    · subst h2; exact hP (Submodule.subset_span (by simp))
    rw [← hk k h1 h2]; exact Submodule.subset_span ⟨k, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases h1 : k = i
    · subst h1; exact hP' (Submodule.subset_span (by simp))
    by_cases h2 : k = j
    · subst h2; exact hP' (Submodule.subset_span (by simp))
    rw [hk k h1 h2]; exact Submodule.subset_span ⟨k, rfl⟩

theorem swap_good {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ (b' : Fin n → Fin n → ℚ) (s' : Fin n → ℚ), Good Λ Γ b' s' ∧ (∀ k, k ≠ i → k ≠ j → s' k = s k) ∧
      DvdQ (s i) (s' i) ∧ DvdQ (s j) (s' i) ∧ DvdQ (s' j) (s i) ∧ DvdQ (s' j) (s j) ∧
      (∀ z, DvdQ (s i) z → DvdQ (s j) z → DvdQ (s' i) z) := by
  classical
  obtain ⟨hΛ, hΓ, hpos⟩ := hg
  obtain ⟨c1, c2, l, g, hl, hg0, hs1, hs2, d1, d2, d3, d4, d5⟩ :=
    swap_pair (b i) (b j) (s i) (s j) (hpos i) (hpos j)
  have hji : j ≠ i := hij.symm
  let b' : Fin n → Fin n → ℚ := fun k => if k = i then c1 else if k = j then c2 else b k
  let s' : Fin n → ℚ := fun k => if k = i then l else if k = j then g else s k
  have hb'i : b' i = c1 := by simp [b']
  have hb'j : b' j = c2 := by simp [b', hji]
  have hs'i : s' i = l := by simp [s']
  have hs'j : s' j = g := by simp [s', hji]
  have hbk : ∀ k, k ≠ i → k ≠ j → b' k = b k := fun k h1 h2 => by simp [b', h1, h2]
  have hsk : ∀ k, k ≠ i → k ≠ j → s' k = s k := fun k h1 h2 => by simp [s', h1, h2]
  refine ⟨b', s', ⟨?_, ?_, ?_⟩, hsk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΛ]
    exact span_range_update_aux b b' hbk (by rw [hb'i, hb'j]; exact hs1)
  · rw [hΓ]
    refine span_range_update_aux (i := i) (j := j) (fun j => s j • b j) (fun k => s' k • b' k) ?_ ?_
    · intro k h1 h2; simp only [hsk k h1 h2, hbk k h1 h2]
    · simp only [hb'i, hb'j, hs'i, hs'j]; exact hs2
  · intro k
    by_cases h1 : k = i
    · subst h1; rw [hs'i]; exact hl
    by_cases h2 : k = j
    · subst h2; rw [hs'j]; exact hg0
    rw [hsk k h1 h2]; exact hpos k
  · rw [hs'i]; exact d1
  · rw [hs'i]; exact d2
  · rw [hs'j]; exact d3
  · rw [hs'j]; exact d4
  · rw [hs'i]; exact d5

/-- The sorting invariant: the first $k$ entries form a divisibility chain and dominate all later entries. -/
def SortInv (k : ℕ) (s : Fin n → ℚ) : Prop :=
  (∀ i j : Fin n, i.1 < j.1 → j.1 < k → DvdQ (s j) (s i)) ∧
  (∀ i j : Fin n, i.1 < k → k ≤ j.1 → DvdQ (s j) (s i))

theorem sort_inner {Λ Γ : Lat ℚ n} (k : ℕ) (hk : k < n) :
    ∀ m, k < m → m ≤ n → ∀ (b : Fin n → Fin n → ℚ) (s : Fin n → ℚ), Good Λ Γ b s → SortInv k s →
      ∃ (b' : Fin n → Fin n → ℚ) (s' : Fin n → ℚ), Good Λ Γ b' s' ∧ SortInv k s' ∧
        ∀ j : Fin n, k < j.1 → j.1 < m → DvdQ (s' j) (s' ⟨k, hk⟩) := by
  intro m hkm hmn
  induction m, hkm using Nat.le_induction with
  | base =>
    intro b s hg hinv
    exact ⟨b, s, hg, hinv, fun j h1 h2 => by omega⟩
  | succ m hkm ih =>
    intro b s hg hinv
    obtain ⟨b1, s1, hg1, hinv1, hK⟩ := ih (by omega) b s hg hinv
    have hm : m < n := by omega
    set i : Fin n := ⟨k, hk⟩ with hi
    set j : Fin n := ⟨m, hm⟩ with hj
    have hij : i ≠ j := by
      intro h; have := congrArg Fin.val h; simp [hi, hj] at this; omega
    obtain ⟨b2, s2, hg2, hsk, d1, d2, d3, d4, d5⟩ := swap_good hg1 hij
    have hne : ∀ q : Fin n, q.1 < k → q ≠ i ∧ q ≠ j := fun q hq =>
      ⟨fun h => by rw [h] at hq; simp [hi] at hq, fun h => by rw [h] at hq; simp [hj] at hq; omega⟩
    refine ⟨b2, s2, hg2, ⟨?_, ?_⟩, ?_⟩
    · intro a c hac hc
      rw [hsk a (hne a (by omega)).1 (hne a (by omega)).2, hsk c (hne c hc).1 (hne c hc).2]
      exact hinv1.1 a c hac hc
    · intro a q ha hq
      rw [hsk a (hne a ha).1 (hne a ha).2]
      have hai : DvdQ (s1 i) (s1 a) := hinv1.2 a i ha (by simp [hi])
      have haj : DvdQ (s1 j) (s1 a) := hinv1.2 a j ha (by simp [hj]; omega)
      by_cases h1 : q = i
      · subst h1; exact d5 _ hai haj
      by_cases h2 : q = j
      · subst h2; exact d3.trans hai
      rw [hsk q h1 h2]; exact hinv1.2 a q ha hq
    · intro q hq1 hq2
      by_cases h2 : q = j
      · subst h2; exact d3.trans d1
      have hq3 : q.1 < m := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hq2 with h | h
        · exact h
        · exact absurd (Fin.ext (by simpa [hj] using h)) h2
      have h1 : q ≠ i := fun h => by rw [h] at hq1; simp [hi] at hq1
      rw [hsk q h1 h2]
      exact (hK q hq1 hq3).trans d1

/-- Sorting step. -/
theorem sort_step {Λ Γ : Lat ℚ n} (k : ℕ) (hk : k < n) {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ}
    (hg : Good Λ Γ b s) (hinv : SortInv k s) :
    ∃ (b' : Fin n → Fin n → ℚ) (s' : Fin n → ℚ), Good Λ Γ b' s' ∧ SortInv (k + 1) s' := by
  obtain ⟨b', s', hg', hinv', hK⟩ := sort_inner k hk n (by omega) le_rfl b s hg hinv
  refine ⟨b', s', hg', ⟨?_, ?_⟩⟩
  · intro a c hac hc
    by_cases h : c.1 < k
    · exact hinv'.1 a c hac h
    · have hck : c.1 = k := by omega
      have : c = ⟨k, hk⟩ := Fin.ext hck
      subst this
      exact hinv'.2 a _ (by simpa using hac) le_rfl
  · intro a c ha hc
    by_cases h : a.1 < k
    · exact hinv'.2 a c h (by omega)
    · have hak : a.1 = k := by omega
      have : a = ⟨k, hk⟩ := Fin.ext hak
      subst this
      exact hK c (by omega) c.2

/-- **A divisibility chain basis:** a good pair can be chosen with $s_{j+1} \mid s_j$ for all $j$. -/
theorem exists_good_chain {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s) :
    ∃ (b' : Fin n → Fin n → ℚ) (s' : Fin n → ℚ), Good Λ Γ b' s' ∧
      ∀ i j : Fin n, i.1 < j.1 → DvdQ (s' j) (s' i) := by
  have : ∀ k, k ≤ n → ∃ (b' : Fin n → Fin n → ℚ) (s' : Fin n → ℚ), Good Λ Γ b' s' ∧ SortInv k s' := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨b, s, hg, ⟨fun i j _ hj => by omega, fun i j hi => by omega⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨b', s', hg', hinv⟩ := ih (by omega)
      exact sort_step k (by omega) hg' hinv
  obtain ⟨b', s', hg', hinv⟩ := this n le_rfl
  exact ⟨b', s', hg', fun i j hij => hinv.1 i j hij j.2⟩

/-! ### The Corollary: values of the diagonal -/

theorem repr_smul_aux {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b))
    (j k : Fin n) (c : ℚ) : (basisOfLat h).repr (c • b j) k = if j = k then c else 0 := by
  rw [show b j = basisOfLat h j from (basisOfLat_apply h j).symm, map_smul, Module.Basis.repr_self]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [Finsupp.single_apply, hjk]

/-- A multiple of $b_j$ lying in $\Gamma$ has coordinate in $s_j\mathbb Z$. -/
theorem coord_dvd_aux {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s)
    (j : Fin n) (c : ℚ) (hc : c • b j ∈ Γ.1) : ∃ z : ℤ, (z : ℚ) * s j = c := by
  have := (mem_span_smul_iff hg.1 s _).1 (hg.2.1 ▸ hc) j
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by rw [hz, repr_smul_aux]; simp⟩

theorem coord_int_aux {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b))
    (j : Fin n) (c : ℚ) (hc : c • b j ∈ Λ.1) : ∃ z : ℤ, (z : ℚ) = c := by
  have h1 : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range fun j => (fun _ => (1 : ℚ)) j • b j) := by
    simpa using h
  have := (mem_span_smul_iff h (fun _ => (1 : ℚ)) _).1 (h1 ▸ hc) j
  obtain ⟨z, hz⟩ := this
  rw [repr_smul_aux] at hz
  exact ⟨z, by simpa using hz⟩

theorem diag_values_aux {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s)
    {p : ℕ} (hp : p.Prime) (h1 : ∀ x ∈ Λ.1, (p : 𝓞 ℚ) • x ∈ Γ.1) (h2 : ∀ x ∈ Γ.1, (p : 𝓞 ℚ) • x ∈ Λ.1)
    (j : Fin n) : s j = p ∨ s j = 1 ∨ s j = 1 / p := by
  have hb : b j ∈ Λ.1 := hg.1 ▸ Submodule.subset_span ⟨j, rfl⟩
  have hbΓ : s j • b j ∈ Γ.1 := hg.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩
  have e1 := h1 _ hb
  have e2 := h2 _ hbΓ
  have hc : (((p : ℕ) : 𝓞 ℚ) : ℚ) = (p : ℚ) := map_natCast (algebraMap (𝓞 ℚ) ℚ) p
  rw [smul_eq_rat_smul_aux, hc] at e1 e2
  obtain ⟨z, hz⟩ := coord_dvd_aux hg j (p : ℚ) e1
  obtain ⟨z', hz'⟩ := coord_int_aux hg.1 j ((p : ℚ) * s j) (by rwa [smul_smul] at e2)
  have hsj := hg.2.2 j
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hzz : (z : ℚ) * z' = (p : ℚ) * p := by rw [hz']; linear_combination (p : ℚ) * hz
  have hzz' : z * z' = (p : ℤ) * p := by exact_mod_cast hzz
  have hz'pos : 0 < z' := by
    have : (0 : ℚ) < z' := by rw [hz']; positivity
    exact_mod_cast this
  have hdvd : z'.natAbs ∣ p ^ 2 := by
    have : z' ∣ ((p : ℤ) ^ 2) := ⟨z, by rw [sq, ← hzz']; ring⟩
    have := Int.natAbs_dvd_natAbs.2 this
    simpa [Int.natAbs_pow] using this
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hz'e : z' = (p : ℤ) ^ i := by
    have : z' = (z'.natAbs : ℤ) := (Int.natAbs_of_nonneg hz'pos.le).symm
    rw [this, hi']; push_cast; rfl
  have hpne : (p : ℚ) ≠ 0 := hpQ.ne'
  have hs : s j = (z' : ℚ) / p := by rw [hz']; field_simp
  rw [hs, hz'e]
  interval_cases i
  · right; right; simp
  · right; left; push_cast; field_simp
  · left; push_cast; field_simp

theorem repr_b_aux {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b))
    (j k : Fin n) : (basisOfLat h).repr (b j) k = if j = k then 1 else 0 := by
  simpa using repr_smul_aux h j k 1

theorem count_big_aux {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s)
    {p : ℕ} (hp : p.Prime) (hv : ∀ j, s j = p ∨ s j = 1 ∨ s j = 1 / p) (hI : casselsI Λ Γ = p) :
    ∃! j, s j = p := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hex : ∃ j, s j = p := by
    by_contra hno
    push_neg at hno
    have hle : Λ.1 ≤ Γ.1 := by
      rw [hg.1, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, hg.2.1, mem_span_smul_iff hg.1]
      intro k
      rw [repr_b_aux hg.1 j k]
      by_cases hjk : j = k
      · subst hjk
        simp only [if_true]
        rcases hv j with h | h | h
        · exact absurd h (hno j)
        · exact ⟨1, by simp [h]⟩
        · exact ⟨p, by rw [h]; push_cast; field_simp⟩
      · exact ⟨0, by simp [hjk]⟩
    have : casselsI Λ Γ = 1 := by
      unfold casselsI
      rw [inf_eq_left.2 hle]
      exact AddSubgroup.relIndex_self _
    rw [hI] at this
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨j0, hj0⟩ := hex
  refine ⟨j0, hj0, fun i hi => ?_⟩
  by_contra hne
  -- two indices with s = p give index ≥ p²
  have hne0 : casselsI Λ Γ ≠ 0 := by rw [hI]; exact hp.ne_zero
  set L := Λ.1.toAddSubgroup with hL
  set K := (Λ.1 ⊓ Γ.1).toAddSubgroup with hK
  haveI : (K.addSubgroupOf L).FiniteIndex := ⟨hne0⟩
  haveI : Finite (↥L ⧸ K.addSubgroupOf L) := AddSubgroup.finite_quotient_of_finiteIndex
  have hbi : b i ∈ Λ.1 := hg.1 ▸ Submodule.subset_span ⟨i, rfl⟩
  have hbj : b j0 ∈ Λ.1 := hg.1 ▸ Submodule.subset_span ⟨j0, rfl⟩
  have hmem : ∀ a a' : ℤ, (a : ℚ) • b i + (a' : ℚ) • b j0 ∈ Λ.1 := fun a a' => by
    refine Submodule.add_mem _ ?_ ?_
    · rw [← int_smul_eq_aux]; exact Λ.1.smul_mem _ hbi
    · rw [← int_smul_eq_aux]; exact Λ.1.smul_mem _ hbj
  let x : ℤ → ℤ → ↥L := fun a a' => ⟨(a : ℚ) • b i + (a' : ℚ) • b j0, hmem a a'⟩
  let f : Fin p × Fin p → ↥L ⧸ K.addSubgroupOf L := fun q => QuotientAddGroup.mk (x q.1.1 q.2.1)
  have hs_i : s i = p := hi
  have hij : i ≠ j0 := hne
  have hf : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ hfq
    have h1 := QuotientAddGroup.eq.1 hfq
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : (-(x a a') + x c c' : ↥L).1 ∈ Γ.1 := (Submodule.mem_inf.1 h1).2
    have h3 : (-(x a a') + x c c' : ↥L).1 =
        (((c : ℤ) - a : ℤ) : ℚ) • b i + (((c' : ℤ) - a' : ℤ) : ℚ) • b j0 := by
      simp only [x, AddSubmonoid.coe_add, AddSubgroup.coe_neg, Submodule.coe_toAddSubmonoid]
      push_cast
      module
    rw [h3, hg.2.1, mem_span_smul_iff hg.1] at h2
    have hji : j0 ≠ i := hij.symm
    obtain ⟨z, hz⟩ := h2 i
    obtain ⟨z', hz'⟩ := h2 j0
    rw [map_add, Finsupp.add_apply, repr_smul_aux, repr_smul_aux] at hz hz'
    simp only [if_true, hji, hij, ite_false, add_zero, zero_add, hs_i, hj0] at hz hz'
    have hz2 : z * (p : ℤ) = (c : ℤ) - a := by exact_mod_cast hz
    have hz2' : z' * (p : ℤ) = (c' : ℤ) - a' := by exact_mod_cast hz'
    have key : ∀ (c a : ℕ), c < p → a < p → ∀ z : ℤ, z * (p : ℤ) = (c : ℤ) - a → a = c := by
      intro c a hc ha z hz
      have hdv : (p : ℤ) ∣ (c : ℤ) - a := ⟨z, by rw [← hz]; ring⟩
      have habs : |(c : ℤ) - a| < p := by rw [abs_lt]; constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdv habs
      omega
    have e1 := key c a hc ha z hz2
    have e2 := key c' a' hc' ha' z' hz2'
    subst e1; subst e2
    rfl
  have hcard := Nat.card_le_card_of_injective f hf
  have hq : Nat.card (↥L ⧸ K.addSubgroupOf L) = p := by
    rw [← AddSubgroup.index_eq_card]; exact hI
  rw [hq, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  have := hp.two_le
  nlinarith

theorem good_swap_aux {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s) :
    Good Γ Λ (fun j => s j • b j) (fun j => (s j)⁻¹) := by
  refine ⟨hg.2.1, ?_, fun j => inv_pos.2 (hg.2.2 j)⟩
  rw [hg.1]
  congr 2
  ext j : 1
  simp [smul_smul, inv_mul_cancel₀ (hg.2.2 j).ne']

theorem smul_mem_of_casselsI_aux {L M : Lat ℚ n} {p : ℕ} (hI : casselsI L M = p) :
    ∀ x ∈ L.1, (p : 𝓞 ℚ) • x ∈ M.1 := by
  intro x hx
  have := relIndex_nsmul_mem_aux (H := (L.1 ⊓ M.1).toAddSubgroup) (K := L.1.toAddSubgroup) (x := x) hx
  unfold casselsI at hI
  rw [hI] at this
  rw [Nat.cast_smul_eq_nsmul]
  exact (Submodule.mem_inf.1 this).2

theorem le_of_dvdQ_aux {x y : ℚ} (hx : 0 < x) (hy : 0 < y) (h : DvdQ x y) : x ≤ y := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℚ) < z := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have : (1 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℤ) < z by exact_mod_cast hz)
  have h1 : (1 : ℚ) ≤ z := by exact_mod_cast this
  nlinarith

end Good

/-- **Cassels, Theorem 5.1, Corollary** (Ch. 11, p. 223): *let $\Gamma, \Lambda$ be $\mathbb Z$-lattices of the same
determinant in the $\mathbb Q$-vector space $V$ with $I(\Gamma, \Lambda) = p$ for some prime $p$. Then there are
$b_1, \dots, b_n \in V$ such that $pb_1, b_2, \dots, b_n$ and $b_1, \dots, b_{n-1}, pb_n$ are bases of $\Gamma,
\Lambda$ respectively* (0-based; (5.9), (5.10) reconstructed). For $n \le 1$ the hypothesis cannot hold. -/
@[kb "cassels1978" "Ch. 11, Thm. 5.1, Cor., p. 223 ((5.9)–(5.10) reconstructed; 0-based)"]
theorem exists_basis_of_casselsI_prime (hn : 2 ≤ n) {Γ Λ : Lat ℚ n} (h : latIndex Γ = latIndex Λ) {p : ℕ}
    (hp : p.Prime) (hI : casselsI Γ Λ = p) :
    ∃ b : Fin n → Fin n → ℚ, LinearIndependent ℚ b ∧
      Γ.1 = Submodule.span (𝓞 ℚ) (Set.range fun j : Fin n => if j.1 = 0 then (p : ℚ) • b j else b j) ∧
      Λ.1 = Submodule.span (𝓞 ℚ) (Set.range fun j : Fin n => if j.1 = n - 1 then (p : ℚ) • b j else b j) := by
  have hI' : casselsI Λ Γ = p := (casselsI_comm h).symm.trans hI
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℚ) < p := by linarith
  obtain ⟨b0, s0, hg0⟩ := exists_good hp.pos (smul_mem_of_casselsI_aux hI')
  obtain ⟨b, s, hg, hch⟩ := exists_good_chain hg0
  have hv := diag_values_aux hg hp (smul_mem_of_casselsI_aux hI') (smul_mem_of_casselsI_aux hI)
  have hg2 := good_swap_aux hg
  have hv2 : ∀ j, (s j)⁻¹ = p ∨ (s j)⁻¹ = 1 ∨ (s j)⁻¹ = 1 / p := by
    intro j
    rcases hv j with h | h | h
    · right; right; rw [h]; simp
    · right; left; rw [h]; simp
    · left; rw [h]; simp
  obtain ⟨j1, hj1, hj1u⟩ := count_big_aux hg hp hv hI'
  obtain ⟨j2, hj2, hj2u⟩ := count_big_aux hg2 hp hv2 hI
  have hpos := hg.2.2
  have hmono : ∀ i j : Fin n, i.1 < j.1 → s j ≤ s i := fun i j hij =>
    le_of_dvdQ_aux (hpos j) (hpos i) (hch i j hij)
  have hn0 : 0 < n := by omega
  obtain ⟨z0, hz0v⟩ : ∃ z0 : Fin n, z0.1 = 0 := ⟨⟨0, hn0⟩, rfl⟩
  obtain ⟨zl, hzlv⟩ : ∃ zl : Fin n, zl.1 = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have hz0l : z0 ≠ zl := fun h => by have := congrArg Fin.val h; omega
  have hge0 : ∀ j : Fin n, s j ≤ s z0 := fun j => by
    by_cases h : z0.1 < j.1
    · exact hmono z0 j h
    · exact le_of_eq (by congr 1; ext; omega)
  have hlel : ∀ j : Fin n, s zl ≤ s j := fun j => by
    by_cases h : j.1 < zl.1
    · exact hmono j zl h
    · exact le_of_eq (by congr 1; ext; have := j.2; omega)
  have hone : (1 : ℚ) / p < 1 := by rw [div_lt_one hp0]; exact hpQ
  have hs0 : s z0 = p := by
    have h1 : (p : ℚ) ≤ s z0 := hj1 ▸ hge0 j1
    rcases hv z0 with h | h | h
    · exact h
    · rw [h] at h1; linarith
    · rw [h] at h1; linarith
  have hz0j1 : z0 = j1 := hj1u z0 hs0
  have hs2 : s j2 = 1 / p := by
    have : s j2 = ((s j2)⁻¹)⁻¹ := (inv_inv _).symm
    rw [this, hj2]; simp
  have hsl : s zl = 1 / p := by
    have h1 : s zl ≤ 1 / p := hs2 ▸ hlel j2
    rcases hv zl with h | h | h
    · rw [h] at h1; linarith
    · rw [h] at h1; linarith
    · exact h
  have hzlj2 : zl = j2 := hj2u zl (by show (s zl)⁻¹ = p; rw [hsl]; field_simp)
  have hmid : ∀ j : Fin n, j ≠ z0 → j ≠ zl → s j = 1 := by
    intro j h0 hl
    rcases hv j with h | h | h
    · exact absurd (hz0j1.trans (hj1u j h).symm) (Ne.symm h0)
    · exact h
    · exfalso
      apply hl
      rw [hzlj2]
      exact hj2u j (by show (s j)⁻¹ = p; rw [h]; field_simp)
  have hsval : ∀ j : Fin n, s j = if j.1 = 0 then (p : ℚ) else if j.1 = n - 1 then 1 / p else 1 := by
    intro j
    by_cases h0 : j.1 = 0
    · have : j = z0 := Fin.ext (by omega)
      rw [if_pos h0, this, hs0]
    by_cases hl : j.1 = n - 1
    · have : j = zl := Fin.ext (by omega)
      rw [if_neg h0, if_pos hl, this, hsl]
    · rw [if_neg h0, if_neg hl]
      exact hmid j (fun h => h0 (by rw [h]; exact hz0v)) (fun h => hl (by rw [h]; exact hzlv))
  have hn1 : n - 1 ≠ 0 := by omega
  refine ⟨fun j => if j.1 = n - 1 then ((1 : ℚ) / p) • b j else b j, ?_, ?_, ?_⟩
  · have := (linIndep_of_lat hg.1).units_smul
      (fun j : Fin n => if j.1 = n - 1 then Units.mk0 ((1 : ℚ) / p) (by positivity) else 1)
    convert this using 1
    ext j : 1
    by_cases hl : j.1 = n - 1 <;> simp [hl, Units.smul_def]
  · rw [hg.2.1]
    congr 2
    ext j : 1
    rw [hsval j]
    by_cases h0 : j.1 = 0
    · have : j.1 ≠ n - 1 := by omega
      simp [h0, this, hn1, hn1.symm]
    · by_cases hl : j.1 = n - 1
      · simp [h0, hl, hn1]
      · simp [h0, hl]
  · rw [hg.1]
    congr 2
    ext j : 1
    by_cases hl : j.1 = n - 1
    · simp [hl, smul_smul, mul_inv_cancel₀ hp0.ne', hn1, hn1.symm]
    · simp [hl]

end QuadFormsKB.Lattices
