/-
# One proper class in the genus of $x_0^2+x_1^2$ and of $x_0^2-2x_1^2$

**Layer:** number fields, then $\mathbb Q$.

**The criterion** (`dc_eq_one_of_represents_one`, every number field $F$, $\langle1,D\rangle = x_0^2 + Dx_1^2$, $D\ne0$): if every
lattice in the genus of $L = \mathcal O_F^2$ contains a vector $x$ with $Q(x) = 1$, then the double cosets
$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ (`DC`) are one point. *Proof:* for $b\in SO(V)(\mathbb A_f)$ the lattice
$M = bL$ (`latSMul`) is in the genus; if $x\in M$, $Q(x) = 1$, then $M = \gamma_xL$ with $\gamma_x$ the rotation with first
column $x$ (`BinaryNormOne.eq_glImage_rotOf_of_mem`), so $\gamma_x^{-1}b$ stabilizes $\hat L$ (`stabilizer_eq_locStab`) and
has determinant $1$: $b\in SO(V)(F)\,SO(\hat L)$.

**Over $\mathbb Q$** (`represents_one_sumTwoSq`, `represents_one_pell2`): with $E = \mathbb Q(i)$, resp. $\mathbb Q(\sqrt2)$,
$\theta = i$, resp. $\sqrt2$, and coordinates $c(x) = x_0 + x_1\theta$, the lattice of $\mathbb Z[\theta] = \mathcal O_E$ is $\mathbb Z^2$;
every lattice in its genus is $c^{-1}(d^{-1}\mathfrak A)$ with $N\mathfrak A = (d^2)$ (`BinaryCM.exists_pair_of_genus`), $\mathcal O_E$
is a principal ideal domain (Minkowski's bound, `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`: $|d_E| = 4 < \pi^2$,
$|d_E| = 8 < 16$), so $\mathfrak A = (\alpha)$ with $N\alpha = \pm d^2$, and $\alpha/d$ (times $1+\sqrt2$ if $N\alpha = -d^2$) is a
vector of value $1$. Hence **`subsingleton_DC_sumTwoSq`**, **`subsingleton_DC_pell2`**. Unconditional.
-/
import QuadFormsKB.Tamagawa.Classical.Binary
import QuadFormsKB.Tamagawa.BinaryCMClasses

open NumberField IsDedekindDomain Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.HilbertModular

section General

variable {F : Type} [Field F] [NumberField F]

/-- **One proper class if every lattice in the genus represents $1$** ($\langle1,D\rangle$ over $\mathcal O_F$, $D \ne 0$):
every $b \in SO(V)(\mathbb A_f)$ is in the double coset of $1$. -/
theorem dc_eq_one_of_represents_one (D : 𝓞 F) (hD : D ≠ 0)
    (h1 : ∀ M : Lat F 2, SameGenus (formF (diagForm1 D)) intVec M.1 →
      ∃ x ∈ M.1, (formF (diagForm1 D)).eval x = 1)
    (b : SOAf (diagForm1 D)) : (⟦b⟧ : DC (diagForm1 D)) = ⟦1⟧ := by
  let _ : MulAction (OAf (formF (diagForm1 D))) (Lat F 2) := latAction (formF (diagForm1 D))
  set L : Lat F 2 := ⟨intVec, intVec_isLattice⟩ with hL
  set M : Lat F 2 := latSMul (formF (diagForm1 D)) (b : OAf (formF (diagForm1 D))) L with hMdef
  have hM : SameGenus (formF (diagForm1 D)) intVec M.1 := fun v =>
    ⟨_, ((b : OAf (formF (diagForm1 D))) v).2, (loc_latSMul (formF (diagForm1 D)) (b : OAf (formF (diagForm1 D))) L v).symm⟩
  obtain ⟨x, hx, hQx⟩ := h1 M hM
  have himg := eq_glImage_rotOf_of_mem D hD hM hx hQx
  have hγO : rotOf D hQx ∈ orthGroup (formF (diagForm1 D)) F := rotGL_mem D _ _
  have hγdet : (rotOf D hQx).val.det = 1 := det_rotMat (norm_one_of_eval D hQx)
  let γS : soSub (formF (diagForm1 D)) F := ⟨⟨rotOf D hQx, hγO⟩, mem_soSub.mpr hγdet⟩
  set g := diagSOAdele (diagForm1 D) γS with hg
  have hgΓ : g ∈ GammaSOAdele (diagForm1 D) := ⟨γS, rfl⟩
  have hg2 : ((g.2 : SOAf (diagForm1 D)) : OAf (formF (diagForm1 D))) = diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩ := rfl
  -- `g₂ L = M`
  have hgL : latSMul (formF (diagForm1 D)) (diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩) L = M := by
    rw [diagF_smul]
    exact Subtype.ext himg
  set k : SOAf (diagForm1 D) := g.2⁻¹ * b with hk
  have hkK : k ∈ KSO (diagForm1 D) := by
    rw [KSO, Subgroup.mem_subgroupOf, ← stabilizer_eq_locStab, MulAction.mem_stabilizer_iff]
    show latSMul (formF (diagForm1 D)) ((g.2⁻¹ * b : SOAf (diagForm1 D)) : OAf (formF (diagForm1 D))) L = L
    have e : ((g.2⁻¹ * b : SOAf (diagForm1 D)) : OAf (formF (diagForm1 D))) =
        (diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩)⁻¹ * (b : OAf (formF (diagForm1 D))) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hg2]
    rw [e]
    change ((diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩)⁻¹ * (b : OAf (formF (diagForm1 D)))) • L = L
    rw [mul_smul]
    change (diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩)⁻¹ • M = L
    rw [← hgL]
    change (diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩)⁻¹ • (diagF (formF (diagForm1 D)) ⟨rotOf D hQx, hγO⟩ • L) = L
    rw [inv_smul_smul]
  have hrel : (dcSetoid (diagForm1 D)) 1 b := ⟨g, hgΓ, k, hkK, by rw [hk, mul_one, mul_inv_cancel_left]⟩
  exact (Quotient.sound hrel).symm

/-- **One proper class** under the criterion of `dc_eq_one_of_represents_one`. -/
theorem subsingleton_DC_of_represents_one (D : 𝓞 F) (hD : D ≠ 0)
    (h1 : ∀ M : Lat F 2, SameGenus (formF (diagForm1 D)) intVec M.1 →
      ∃ x ∈ M.1, (formF (diagForm1 D)).eval x = 1) :
    Subsingleton (DC (diagForm1 D)) := by
  refine ⟨fun i j => ?_⟩
  induction i using Quotient.inductionOn with | h b => ?_
  induction j using Quotient.inductionOn with | h b' => ?_
  rw [dc_eq_one_of_represents_one D hD h1 b, dc_eq_one_of_represents_one D hD h1 b']

end General

/-! ### Over $\mathbb Q$: every lattice in the genus represents $\pm1$ -/

section Rat

open QuadFormsKB.Binary QuadFormsKB.Binary.Rel QuadFormsKB.Tamagawa.BinaryCM

instance isQuadraticExtension_QField (D : ℤ) [IsQuadDisc D] : Algebra.IsQuadraticExtension ℚ (QField D) :=
  ⟨finrank_eq⟩

/-- A square root $\theta\notin\mathbb Q$ of a rational number is sent to $-\theta$ by the conjugation. -/
theorem conj_eq_neg_of_sq {E : Type} [Field E] [Algebra ℚ E] [Algebra.IsQuadraticExtension ℚ E] {θ : E} {q : ℚ}
    (hθ : θ ^ 2 = algebraMap ℚ E q) (hθq : θ ∉ Set.range (algebraMap ℚ E)) : conj ℚ E θ = -θ := by
  have hsq : (conj ℚ E θ - θ) * (conj ℚ E θ + θ) = 0 := by
    have : (conj ℚ E θ) ^ 2 = θ ^ 2 := by rw [← map_pow, hθ, AlgEquiv.commutes]
    linear_combination this
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    obtain ⟨a, ha⟩ := (conj_eq_self_iff θ).1 (sub_eq_zero.mp h)
    exact hθq ⟨a, ha⟩
  · linear_combination h

/-- **The square root $\omega$ of $-d$ in $\mathbb Q(\sqrt D)$** (for $D \equiv 0 \pmod 4$, $\omega^2 = D/4$). -/
def sqrtDataQ (D : ℤ) [IsQuadDisc D] (d : 𝓞 ℚ) (hqb : qb D = 0)
    (hd : algebraMap (𝓞 ℚ) ℚ d = -((qa D : ℤ) : ℚ)) (hd0 : d ≠ 0) : SqrtData d (QField D) where
  θ := ⟨0, 1⟩
  sq := by
    rw [hd]
    ext
    · rw [sq, QuadraticAlgebra.re_mul]; simp
    · rw [sq, QuadraticAlgebra.im_mul]; simp; exact Int.dvd_of_emod_eq_zero hqb
  conj_eq := by
    refine conj_eq_neg_of_sq (q := ((qa D : ℤ) : ℚ)) ?_ ?_
    · ext
      · rw [sq, QuadraticAlgebra.re_mul]; simp
      · rw [sq, QuadraticAlgebra.im_mul]; simp; exact Int.dvd_of_emod_eq_zero hqb
    · rintro ⟨q, hq⟩
      have := congrArg QuadraticAlgebra.im hq
      simp at this
  D_ne := hd0

theorem cE_sqrtDataQ (D : ℤ) [IsQuadDisc D] (d : 𝓞 ℚ) (hqb : qb D = 0)
    (hd : algebraMap (𝓞 ℚ) ℚ d = -((qa D : ℤ) : ℚ)) (hd0 : d ≠ 0) (x : Fin 2 → ℚ) :
    cE (sqrtDataQ D d hqb hd hd0) x = ⟨x 0, x 1⟩ := by
  ext <;> simp [cE, sqrtDataQ]

/-- **The lattice of $\mathcal O_E = \mathbb Z[\omega]$ is $\mathbb Z^2$.** -/
theorem latE_sqrtDataQ (D : ℤ) [IsQuadDisc D] (d : 𝓞 ℚ) (hqb : qb D = 0)
    (hd : algebraMap (𝓞 ℚ) ℚ d = -((qa D : ℤ) : ℚ)) (hd0 : d ≠ 0) :
    latE (sqrtDataQ D d hqb hd hd0) = intVec := by
  refine le_antisymm (fun x hx => ?_) (intVec_le_latE _)
  rw [mem_latE, cE_sqrtDataQ, isIntegral_iff] at hx
  obtain ⟨y, hy⟩ := hx
  have h0 := congrArg QuadraticAlgebra.re hy
  have h1 := congrArg QuadraticAlgebra.im hy
  simp only [QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap] at h0 h1
  intro i
  fin_cases i
  · exact ⟨y.re, by simp [← h0]⟩
  · exact ⟨y.im, by simp [← h1]⟩

instance isPrincipalIdealRing_QField_neg_four : IsPrincipalIdealRing (𝓞 (QField (-4))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_three
  norm_num [Nat.factorial]
  nlinarith

instance isPrincipalIdealRing_QField_eight : IsPrincipalIdealRing (𝓞 (QField 8)) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_pos (by norm_num)]
  norm_num [Nat.factorial]

/-- A unit of $\mathcal O_\mathbb Q$ is $\pm1$ in $\mathbb Q$. -/
theorem unit_rat_eq (u : (𝓞 ℚ)ˣ) : ((u : 𝓞 ℚ) : ℚ) = 1 ∨ ((u : 𝓞 ℚ) : ℚ) = -1 := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h1 : e (u : 𝓞 ℚ) * e ((u⁻¹ : (𝓞 ℚ)ˣ) : 𝓞 ℚ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hc : ∀ a : 𝓞 ℚ, ((a : 𝓞 ℚ) : ℚ) = (e a : ℚ) := fun a => by
    conv_lhs => rw [← e.symm_apply_apply a]
    simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h
  · left; rw [hc, h]; simp
  · right; rw [hc, h]; simp

/-- **Every lattice in the genus of $\mathbb Z^2$ for $x_0^2 + dx_1^2$ represents $\pm1$**, when
$\mathcal O_E = \mathbb Z[\sqrt{-d}]$ is a principal ideal domain. -/
theorem represents_pm_one (D : ℤ) [IsQuadDisc D] [IsPrincipalIdealRing (𝓞 (QField D))] (d : 𝓞 ℚ)
    (hqb : qb D = 0) (hd : algebraMap (𝓞 ℚ) ℚ d = -((qa D : ℤ) : ℚ)) (hd0 : d ≠ 0)
    (M : Lat ℚ 2) (hM : SameGenus (formF (diagForm1 d)) intVec M.1) :
    ∃ x ∈ M.1, (formF (diagForm1 d)).eval x = 1 ∨ (formF (diagForm1 d)).eval x = -1 := by
  set S := sqrtDataQ D d hqb hd hd0
  rw [← latE_sqrtDataQ D d hqb hd hd0] at hM
  obtain ⟨d₀, 𝔄, hd₀, -, hN, hMeq⟩ := exists_pair_of_genus S M.2 hM
  obtain ⟨α, rfl⟩ := (IsPrincipalIdealRing.principal 𝔄).principal
  rw [← Ideal.span, Ideal.relNorm_singleton, Ideal.span_singleton_eq_span_singleton] at hN
  obtain ⟨u, hu⟩ := hN
  set dE := algebraMap ℚ (QField D) (algebraMap (𝓞 ℚ) ℚ d₀)
  obtain ⟨x, hx⟩ := exists_cE_eq S (dE⁻¹ * algebraMap (𝓞 (QField D)) (QField D) α)
  refine ⟨x, ?_, ?_⟩
  · rw [hMeq, mem_latI]
    exact ⟨α, Submodule.mem_span_singleton_self α, hx.symm⟩
  · rw [← norm_cE_eq_eval S, hx, show dE⁻¹ = algebraMap ℚ (QField D) (algebraMap (𝓞 ℚ) ℚ d₀)⁻¹ from
      (map_inv₀ _ _).symm, map_mul, norm_algebraMap_F]
    have hNα : Algebra.norm ℚ (algebraMap (𝓞 (QField D)) (QField D) α) =
        ((d₀ : ℚ)) ^ 2 * (((u⁻¹ : (𝓞 ℚ)ˣ) : 𝓞 ℚ) : ℚ) := by
      have e1 := congrArg (fun a : 𝓞 ℚ => (a : ℚ)) hu
      simp only [map_mul, map_pow] at e1
      have e2 : ((Algebra.intNorm (𝓞 ℚ) (𝓞 (QField D)) α : 𝓞 ℚ) : ℚ) =
          Algebra.norm ℚ (algebraMap (𝓞 (QField D)) (QField D) α) := coe_intNorm α
      rw [← e2]
      have hu1 : (((u : 𝓞 ℚ) : ℚ)) * (((u⁻¹ : (𝓞 ℚ)ˣ) : 𝓞 ℚ) : ℚ) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      calc ((Algebra.intNorm (𝓞 ℚ) (𝓞 (QField D)) α : 𝓞 ℚ) : ℚ)
          = ((Algebra.intNorm (𝓞 ℚ) (𝓞 (QField D)) α : 𝓞 ℚ) : ℚ) * (((u : 𝓞 ℚ) : ℚ) *
              (((u⁻¹ : (𝓞 ℚ)ˣ) : 𝓞 ℚ) : ℚ)) := by rw [hu1, mul_one]
        _ = _ := by rw [← mul_assoc]; exact congrArg (· * _) e1
    have hd₀' : ((d₀ : ℚ)) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hd₀
    rw [hNα, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hd₀'), one_mul]
    exact unit_rat_eq u⁻¹

/-- **Every lattice in the genus represents $1$** when $\mathcal O_E$ is principal and $x_0^2 + dx_1^2$ takes the value $-1$ on
$\mathbb Z^2$ (a unit of norm $-1$; for $d > 0$ use `represents_pm_one` and positivity instead). -/
theorem represents_one_of_neg (D : ℤ) [IsQuadDisc D] [IsPrincipalIdealRing (𝓞 (QField D))] (d : 𝓞 ℚ)
    (hqb : qb D = 0) (hd : algebraMap (𝓞 ℚ) ℚ d = -((qa D : ℤ) : ℚ)) (hd0 : d ≠ 0)
    {y : Fin 2 → ℚ} (hy : y ∈ (intVec : Submodule (𝓞 ℚ) (Fin 2 → ℚ))) (hQy : (formF (diagForm1 d)).eval y = -1)
    (M : Lat ℚ 2) (hM : SameGenus (formF (diagForm1 d)) intVec M.1) :
    ∃ x ∈ M.1, (formF (diagForm1 d)).eval x = 1 := by
  obtain ⟨x, hx, h | h⟩ := represents_pm_one D d hqb hd hd0 M hM
  · exact ⟨x, hx, h⟩
  · set S := sqrtDataQ D d hqb hd hd0
    have hM' := hM
    rw [← latE_sqrtDataQ D d hqb hd hd0] at hM'
    have hε : IsIntegral ℤ (cE S y) := (mem_latE S).1 (intVec_le_latE S hy)
    refine ⟨mulMat S (cE S y) *ᵥ x, genus_mulMat_mem S M.2 hM' hε hx, ?_⟩
    rw [← norm_cE_eq_eval S, cE_mulMat, map_mul, norm_cE_eq_eval, norm_cE_eq_eval, hQy, h]
    norm_num

end Rat

end QuadFormsKB.Tamagawa.Classical
