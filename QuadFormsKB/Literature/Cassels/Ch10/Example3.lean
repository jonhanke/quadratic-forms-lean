/-
# Cassels, Chapter 10, Example 3: congruence conditions on a rotation of an indefinite ternary lattice

**Layer** (as in `Example1.lean`, `Example2.lean` and `Ch11Examples3.lean`): $V = \mathbb Q^3$ with the form
$Q$ = `Q : QuadForm ℚ 3`; the lattice $\Lambda$ = `L : Lat ℚ 3`; the primes $p$ are `v : HeightOneSpectrum (𝓞 ℚ)`;
$\Lambda_p$ = `loc v L.1`; $O^+(\Lambda_p)$ = `locStabV Q v L ⊓ Tamagawa.soSub Q _`; $\theta$ = `spinorNorm`;
$\theta(O^+(\Lambda_p))$ = `localSpinorNormGroup`; $p\Lambda$ = `v.asIdeal • L.1`; $p\Lambda_p$ = `pLat v L`.

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 10, Example 3, p. 193): let $\Lambda$ be a lattice in a
$3$-dimensional regular rational quadratic space with (i) $Q$ indefinite, (ii) $Q$ integer-valued on $\Lambda$,
(iii) every $p$-adic unit a spinor norm of $O^+(\Lambda_p)$ for every prime $p$; let $P^*$ be a set of primes at which
$\Lambda_p$ satisfies the hypotheses of Examples 1 and 2 ($p \ne 2$, $p$ divides the determinant exactly once, $V_p$
anisotropic); let $\eta_p = \pm 1$ for $p \in P^*$ and let $b \in \Lambda$ have $\lvert Q(b)\rvert_p = p^{-1}$ for
$p \in P^*$. Then there is $\beta \in O^+(\Lambda)$ with $\beta b \equiv \eta_p b \pmod{p\Lambda}$ for all $p \in P^*$
(`ch10_example3`). The group $O^+(\Lambda)$ is the group of rational rotations that stabilize every localization
$\Lambda_w$ (`locAct w (orthMap Q _ β) (loc w L.1) = loc w L.1` for all primes $w$), as in the statement of Chapter 11,
Example 11 (`Ex11Statement`); this is the stabilizer of $\Lambda$ in $O^+(V)$ since a lattice is the intersection of its
localizations. The statement is unconditional (no named inputs): strong approximation for the spinor kernel
(`strongApproximationSpin`) is proved in the library. Cassels notes that $P^*$ is automatically finite; this is proved
(`finite_setOf_det_valued_eq`) rather than assumed.

**Proof** (a reconstruction; Cassels gives no proof). Let $t$ be the product of the primes $p \in P^*$ with
$\eta_p = -1$. For every prime $w$ choose $\sigma_w \in O^+(\Lambda_w)$ with spinor norm the class of $t$: for
$w \in P^*$ by Example 1 (`localSpinorNormGroup_eq_top_of_det`), for $w \notin P^*$ by (iii), since $t$ is then a unit.
By Example 2 (`ch10_example2`), $\sigma_p b \equiv \eta_p b \pmod{p\Lambda_p}$ for $p \in P^*$. By O'Meara 101:8
(`exists_evalIn_eq_mul`, which needs $Q$ isotropic at the infinite place, i.e. indefinite) there is a rational rotation
$\rho = \tau_x\tau_y$ of spinor norm $t$. Then $\rho^{-1}\sigma$ is in the adelic spinor kernel, and strong
approximation gives $\delta \in O'(V)$ with $u_w = (\rho\delta)^{-1}\sigma_w \in O(\Lambda_w)$ for all $w$
(`exists_rotation_approx`); $u_w$ is a rotation of spinor norm $1$. Put $\beta = \rho\delta$: it stabilizes every
$\Lambda_w$, and $\beta b = \sigma_p u_p^{-1} b \equiv \sigma_p b \equiv \eta_p b \pmod{p\Lambda_p}$, where
$u_p^{-1}b \equiv b$ is Example 2 for a rotation of unit spinor class (`local_congruence`). Finally a congruence modulo
$p\Lambda_p$ of a vector of $\Lambda$ is a congruence modulo $p\Lambda$ (`mem_ideal_smul_of_mem_pLat`).

**Reconstructed.** Integrality of the form on $\Lambda_p$ (needed by Examples 1, 2) from integrality on $\Lambda$
(`loc_evalIn_le_one`). The hypothesis "$\Lambda_p$ satisfies the hypotheses of Examples 1, 2" is read as in
`Ex11Statement`: for a basis `γ` of $\Lambda_p$ the Gram matrix `locGram Q v γ` of $B = 2Q$ has determinant of valuation
$\exp(-1)$ ($2$ is a unit).

**Algebra structures.** For $F = \mathbb Q$ the file-local instance `algAdicEx3Q` makes `Q.evalIn (v.adicCompletion ℚ)`
use the library's $\mathbb Q$-algebra structure on $\mathbb Q_p$ (the one of `loc`, `locVec`, `localSpinorNormGroup`)
instead of Mathlib's unrelated `DivisionRing.toRatAlgebra` (see `Sec106Facts.lean`).
-/
import QuadFormsKB.Literature.Cassels.Ch10.Example1
import QuadFormsKB.Literature.Cassels.Ch10.Example2
import QuadFormsKB.Literature.Cassels.Ch11Sec1Indef
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm
import QuadFormsKB.Lattices.SpinorGlobal

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### The algebra structure on $\mathbb Q_p$ -/

/-- Helper: the library's $F$-algebra structure on the completion $F_\mathfrak p$ (the one used by `loc`, `locVec`,
`locAct`, `localSpinorNormGroup`), as a reducible definition. -/
@[reducible] def algAdicEx3 (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra F (v.adicCompletion F) := inferInstance

/-- Helper (file-local): for $F = \mathbb Q$ use the library's algebra structure on $\mathbb Q_p$ rather than the unrelated
(propositionally equal) `DivisionRing.toRatAlgebra`, so that the statements below match the library layer. -/
local instance (priority := high) algAdicEx3Q (w : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) := algAdicEx3 ℚ w

/-! ### Local integrality from global integrality -/

section LocalIntegral

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Helper: an $\mathfrak o_\mathfrak p$-span of vectors $t$ with $\lvert Q(t)\rvert \le 1$ and pairwise
$\lvert B(t, t')\rvert \le 1$ consists of vectors $x$ with $\lvert Q(x)\rvert \le 1$. Arguments: `T` the spanning set,
`hT` the bound on $Q$ over `T`, `hTT` the bound on the bilinear form $B(x,y) = Q(x+y)-Q(x)-Q(y)$ (`qbil`) over pairs
from `T`. -/
theorem valued_evalIn_le_one_of_span (T : Set (Fin n → Fv)) (hT : ∀ t ∈ T, Valued.v (Q.evalIn Fv t) ≤ 1)
    (hTT : ∀ t ∈ T, ∀ t' ∈ T, Valued.v (qbil Q Fv t t') ≤ 1) :
    ∀ x ∈ Submodule.span 𝔬 T, Valued.v (Q.evalIn Fv x) ≤ 1 := by
  have hsmul : ∀ (c : 𝔬) (x : Fin n → Fv), c • x = (c : Fv) • x := fun c x => rfl
  have h1 : ∀ t ∈ T, ∀ x ∈ Submodule.span 𝔬 T, Valued.v (qbil Q Fv t x) ≤ 1 := by
    intro t ht x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hTT t ht x hx
    | zero =>
      have : qbil Q Fv t 0 = 0 := by
        have := qbil_smul_right Q Fv (0 : Fv) t t
        simpa using this
      rw [this, map_zero]; exact zero_le
    | add x y _ _ ihx ihy =>
      rw [qbil_add_right]; exact Valuation.map_add_le _ ihx ihy
    | smul c x _ ih =>
      rw [hsmul, qbil_smul_right, map_mul]
      exact mul_le_one' c.2 ih
  have h2 : ∀ x ∈ Submodule.span 𝔬 T, ∀ y ∈ Submodule.span 𝔬 T, Valued.v (qbil Q Fv x y) ≤ 1 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx => exact h1 x hx y hy
    | zero =>
      have : qbil Q Fv 0 y = 0 := by
        have := qbil_smul_left Q Fv (0 : Fv) y y
        simpa using this
      rw [this, map_zero]; exact zero_le
    | add x x' _ _ ihx ihx' =>
      rw [qbil_add_left]; exact Valuation.map_add_le _ ihx ihx'
    | smul c x _ ih =>
      rw [hsmul, qbil_smul_left, map_mul]
      exact mul_le_one' c.2 ih
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hT x hx
  | zero =>
    have : Q.evalIn Fv 0 = 0 := by
      have := evalIn_smul_sq Q Fv (0 : Fv) 0
      simpa using this
    rw [this, map_zero]; exact zero_le
  | add x y hx hy ihx ihy =>
    have e : Q.evalIn Fv (x + y) = Q.evalIn Fv x + Q.evalIn Fv y + qbil Q Fv x y := by
      rw [qbil_eq_polar]; ring
    rw [e]
    exact Valuation.map_add_le _ (Valuation.map_add_le _ ihx ihy) (h2 x hx y hy)
  | smul c x _ ih =>
    rw [hsmul, evalIn_smul_sq, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' c.2 2) ih

end LocalIntegral

section LocalIntegralRat

variable {n : ℕ} (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ))

/-- Helper: **$Q$ integer-valued on the lattice $\Lambda$ implies $\lvert Q\rvert \le 1$ on $\Lambda_p$**, for every
prime $p$ (here `v`). Arguments: `Q` the form, `L` the lattice, `hint` the integrality of $Q$ on $L$. -/
theorem loc_evalIn_le_one (hint : ∀ x ∈ L.1, ∃ z : ℤ, Q.eval x = z) :
    ∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
  have hz : ∀ z : ℤ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (z : ℚ)) ≤ 1 := fun z => by
    have := valued_int_le_one v (z : 𝓞 ℚ)
    simpa using this
  have hQ : ∀ l ∈ L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) (locVec v l)) ≤ 1 := fun l hl => by
    obtain ⟨z, hz'⟩ := hint l hl
    have e : Q.evalIn (v.adicCompletion ℚ) (locVec v l) = algebraMap ℚ (v.adicCompletion ℚ) (Q.eval l) :=
      evalIn_locVec Q v l
    rw [e, hz']; exact hz z
  refine valued_evalIn_le_one_of_span Q v (locVec v '' L.1) ?_ ?_
  · rintro _ ⟨l, hl, rfl⟩; exact hQ l hl
  · rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    rw [qbil_eq_polar, ← map_add]
    exact Valuation.map_sub_le _ (Valuation.map_sub_le _ (hQ _ (L.1.add_mem hl hl')) (hQ l hl)) (hQ l' hl')

end LocalIntegralRat

/-! ### From a congruence at $\mathfrak p\Lambda_p$ to a congruence modulo $\mathfrak p\Lambda$ -/

section GlobalLocal

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {n : ℕ}
  (v : HeightOneSpectrum (𝓞 F))

/-- Helper: **a global vector of the lattice that lies in $\mathfrak p\Lambda_p$ lies in $\mathfrak p\Lambda$.** Arguments:
`v` the prime $\mathfrak p$, `L` the lattice $\Lambda$, `z` a vector with $z \in \Lambda$ (`hz`) whose image in
$F_\mathfrak p^n$ is in $\mathfrak p\Lambda_p$ (`hp`, `pLat`). (Proof: $a^{-1}z \in \Lambda_w$ for every prime $w$, where $a$ is a
generator of $\mathfrak p$; a lattice is the intersection of its localizations.) -/
theorem mem_ideal_smul_of_mem_pLat (L : Lat F n) {z : Fin n → F} (hz : z ∈ L.1) (hp : locVec v z ∈ pLat v L) :
    z ∈ v.asIdeal • L.1 := by
  set g : 𝓞 F := primeGen v with hg
  set a : F := algebraMap (𝓞 F) F g with ha
  have ha0 : a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (primeGen_ne_zero v)
  have hmem : a⁻¹ • z ∈ L.1 := by
    rw [mem_iff_forall_loc L.2]
    intro w
    have hloc : locVec w (a⁻¹ • z) = algebraMap F (w.adicCompletion F) a⁻¹ • locVec w z := by
      ext i; simp
    rw [hloc]
    by_cases hw : w = v
    · subst hw
      obtain ⟨y, hy, hzy⟩ := hp
      rw [hzy, smul_smul]
      refine smul_mem_loc L ?_ hy
      have hav : Valued.v (algebraMap F (w.adicCompletion F) a) = exp (-1 : ℤ) := by
        rw [ha, ← IsScalarTower.algebraMap_apply, valued_algebraMap_int, hg, intValuation_primeGen_self]
      rw [map_mul, map_inv₀, map_inv₀, hav, valued_pi, inv_mul_cancel₀ exp_ne_zero]
    · refine smul_mem_loc L ?_ (locVec_mem_loc w hz)
      have h1 : Valued.v (algebraMap F (w.adicCompletion F) a) = 1 := by
        rw [ha, ← IsScalarTower.algebraMap_apply, valued_algebraMap_int, hg,
          intValuation_primeGen_of_ne w hw]
      rw [map_inv₀, map_inv₀, h1]; simp
  have hzz : z = g • (a⁻¹ • z) := by
    rw [← algebraMap_smul F g (a⁻¹ • z), ← ha, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  rw [hzz]
  exact Submodule.smul_mem_smul (Submodule.IsPrincipal.generator_mem v.asIdeal) hmem

end GlobalLocal

/-! ### Finiteness of the set of primes dividing the determinant -/

section FiniteDet

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- Helper: **only finitely many primes divide the determinant of a lattice exactly once** (Cassels' remark that the set
$P^*$ of Example 3 is finite). Arguments: `Q` a nondegenerate form (`hQ`), `L` a lattice. The set is that of primes
$\mathfrak p$ at which some basis `γ` of $\Lambda_\mathfrak p$ (`loc v L.1 = locAct v γ (std v)`) has a Gram matrix
`locGram Q v γ` whose determinant has valuation $\exp(-1)$. -/
theorem finite_setOf_det_valued_eq (Q : QuadForm F n) (hQ : Q.Nondegenerate) (L : Lat F n) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ γ : GL (Fin n) (v.adicCompletion F),
      loc v L.1 = locAct v γ (std v) ∧ Valued.v (locGram Q v γ).det = exp (-1 : ℤ)}.Finite := by
  have hH : Q.hessian.det ≠ 0 := hQ
  refine (Filter.eventually_cofinite.mp ((loc_eventually_std L.2).and (eventually_valuation_eq_one hH))).subset ?_
  rintro v ⟨γ, hγ, hdet⟩ ⟨hstd, hH1⟩
  have hn : ‖γ.val.det‖ = ‖(1 : GL (Fin n) (v.adicCompletion F)).val.det‖ :=
    norm_det_eq_of_locAct_std_eq v γ 1 (by rw [← hγ, hstd, locAct_one])
  have hγ1 : Valued.v γ.val.det = 1 := by
    have h0 : γ.val.det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
    have := valued_eq_of_norm_eq v h0 (by simp) hn
    simpa using this
  rw [locGram_det, map_mul, map_pow, hγ1, one_pow, one_mul] at hdet
  have hH1' : Valued.v (algebraMap F (v.adicCompletion F) Q.hessian.det) = 1 := by
    rw [valued_algebraMap]; exact hH1
  rw [hH1'] at hdet
  have : (1 : WithZero (Multiplicative ℤ)) = exp (-1 : ℤ) := hdet
  rw [← exp_zero, exp_inj] at this
  omega

end FiniteDet

/-! ### Strong approximation for a field of local rotations of a common spinor norm -/

section Approx

variable (Q : QuadForm ℚ 3)

/-- Helper: **global rotation and strong approximation** (the global half of the proof of Example 3). Arguments: `Q` a
nondegenerate (`hQ`) indefinite (`hind`) ternary form over $\mathbb Q$, `L` a lattice, `t` a nonzero rational,
`σ` a family of local rotations $\sigma_w \in O^+(\Lambda_w)$ (`hσL`, `hσso`) all of spinor norm the class of `t` (`hσθ`).
Then there is a rational rotation $\beta \in O^+(V)$ with $\beta_w^{-1}\sigma_w \in O^+(\Lambda_w)$ of spinor norm $1$ at every
prime $w$. (Proof: $\rho = \tau_x\tau_y$ with spinor norm $t$ (O'Meara 101:8); then $\rho^{-1}\sigma$ lies in the adelic
spinor kernel; strong approximation gives $\delta \in O'(V)$ with $\delta^{-1}\rho^{-1}\sigma \in O(\hat\Lambda)$; take
$\beta = \rho\delta$.) -/
theorem exists_rotation_approx (hQ : Q.Nondegenerate) (hind : IsIndefinite Q) (L : Lat ℚ 3) {t : ℚ} (ht : t ≠ 0)
    (σ : ∀ w : HeightOneSpectrum (𝓞 ℚ), orthGroup Q (w.adicCompletion ℚ))
    (hσL : ∀ w, σ w ∈ locStabV Q w L) (hσso : ∀ w, σ w ∈ Tamagawa.soSub Q (w.adicCompletion ℚ))
    (hσθ : ∀ w, spinorNorm Q (w.adicCompletion ℚ) (σ w) = sqClassOf (algebraMap ℚ (w.adicCompletion ℚ) t)) :
    ∃ β ∈ Tamagawa.soSub Q ℚ, ∀ w : HeightOneSpectrum (𝓞 ℚ),
      (orthMap Q (w.adicCompletion ℚ) β)⁻¹ * σ w ∈ locStabV Q w L ⊓ Tamagawa.soSub Q (w.adicCompletion ℚ) ∧
      spinorNorm Q (w.adicCompletion ℚ) ((orthMap Q (w.adicCompletion ℚ) β)⁻¹ * σ w) = 1 := by
  classical
  obtain ⟨w0, h0⟩ := hind
  obtain ⟨x, y, hy, hxy⟩ := exists_evalIn_eq_mul Q hQ (le_refl 3)
    (fun w => (Subsingleton.elim w w0) ▸ h0) ht
  have hx0 : Q.evalIn ℚ x ≠ 0 := by rw [hxy]; exact mul_ne_zero ht hy
  set ρ : orthGroup Q ℚ := symm Q ℚ x * symm Q ℚ y with hρ
  have hρso : ρ ∈ Tamagawa.soSub Q ℚ := by
    rw [Tamagawa.mem_soSub, hρ, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q ℚ hx0, symm_det Q ℚ hy]
    norm_num
  have hρθ : ∀ w : HeightOneSpectrum (𝓞 ℚ), spinorNorm Q (w.adicCompletion ℚ) (orthMap Q _ ρ) =
      sqClassOf (algebraMap ℚ (w.adicCompletion ℚ) t) := by
    intro w
    rw [hρ, spinorNorm_orthMap_symm_mul Q hQ w hx0 hy, hxy, map_mul, map_mul]
    have hyv : algebraMap ℚ (w.adicCompletion ℚ) (Q.evalIn ℚ y) ≠ 0 := (map_ne_zero _).mpr hy
    have htv : algebraMap ℚ (w.adicCompletion ℚ) t ≠ 0 := (map_ne_zero _).mpr ht
    rw [mul_assoc, sqClassOf_mul htv (mul_ne_zero hyv hyv),
      (sqClassOf_eq_one_iff (mul_ne_zero hyv hyv)).mpr ⟨_, rfl⟩, mul_one]
  -- the adelic element `σ`
  let A : OAf Q := ⟨σ, by
    filter_upwards [loc_eventually_std L.2] with w hw
    exact (locStabV_eq_stdStab Q w L hw).mp (hσL w)⟩
  set h : OAf Q := (diagF Q ρ)⁻¹ * A with hh
  have hhw : ∀ w, h w = (orthMap Q (w.adicCompletion ℚ) ρ)⁻¹ * σ w := fun w => rfl
  have hhK : h ∈ spinorKernelAf Q := by
    intro w
    rw [hhw, spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
      map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hρθ, hσθ, inv_mul_cancel]
    refine ⟨rfl, ?_⟩
    have h1 := orthMap_mem_soSub Q (w.adicCompletion ℚ) hρso
    have h2 := (Tamagawa.soSub Q (w.adicCompletion ℚ)).mul_mem ((Tamagawa.soSub Q _).inv_mem h1) (hσso w)
    exact Units.ext h2
  obtain ⟨δ, hδK, hδL⟩ := strongApproximationSpin.approx Q (le_refl 3) hQ ⟨w0, h0⟩ L h hhK
  refine ⟨ρ * δ, (Tamagawa.soSub Q ℚ).mul_mem hρso (spinorKernel_le_soSub Q ℚ hδK), fun w => ?_⟩
  have hexp : (orthMap Q (w.adicCompletion ℚ) (ρ * δ))⁻¹ * σ w =
      ((diagF Q δ)⁻¹ * h) w := by
    rw [map_mul, _root_.mul_inv_rev]
    rw [show ((diagF Q δ)⁻¹ * h) w = (orthMap Q (w.adicCompletion ℚ) δ)⁻¹ * h w from rfl, hhw]
    group
  rw [hexp]
  have hmem : ((diagF Q δ)⁻¹ * h) w ∈ locStabV Q w L := hδL w
  have hδw : orthMap Q (w.adicCompletion ℚ) δ ∈ spinorKernel Q (w.adicCompletion ℚ) :=
    orthMap_mem_spinorKernel Q w hδK
  have hhw' : h w ∈ spinorKernel Q (w.adicCompletion ℚ) := hhK w
  have hk : ((diagF Q δ)⁻¹ * h) w ∈ spinorKernel Q (w.adicCompletion ℚ) :=
    (spinorKernel Q _).mul_mem ((spinorKernel Q _).inv_mem hδw) hhw'
  refine ⟨⟨hmem, spinorKernel_le_soSub Q _ hk⟩, ?_⟩
  exact (Subgroup.mem_inf.mp ((spinorKernel_eq_ker Q (w.adicCompletion ℚ) hQ).le hk)).1

end Approx

/-! ### The local congruence -/

section LocalCongruence

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Helper: **the local congruence of Example 3.** Under the hypotheses of Examples 1 and 2 at the prime `v` (`hQ`, `h2`,
`L`, `γ`, `hγ`, `hint`, `hdet`, `haniso`; see `ch10_example2`), let `σ` and `u` be rotations in $O^+(\Lambda_p)$
(`hσ`, `hu`), `u` of spinor norm $1$ (`hθu`) and `σ` of the spinor norm of `t` (`hθσ`), where `t` is a unit
(first alternative of `hε`) and $\varepsilon = 1$, or `t` has valuation $\exp(-1)$ and $\varepsilon = -1$ (second
alternative). Then for every `b` $\in \Lambda_p$ of value $\lvert\varpi\rvert$ (`hb`, `hQb`):
$\sigma u^{-1} b \equiv \varepsilon b \pmod{\mathfrak p\Lambda_p}$. -/
theorem local_congruence (Q : QuadForm F 3) (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F 3)
    (γ : GL (Fin 3) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hdet : Valued.v (locGram Q v γ).det = exp (-1 : ℤ)) (haniso : ¬ Q.IsotropicIn Fv)
    {σ u : orthGroup Q Fv} (hσ : σ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q Fv)
    (hu : u ∈ locStabV Q v L ⊓ Tamagawa.soSub Q Fv) (hθu : spinorNorm Q Fv u = 1)
    {t : Fv} (hθσ : spinorNorm Q Fv σ = sqClassOf t) (ε : Fv)
    (hε : (ε = 1 ∧ Valued.v t = 1) ∨ (ε = -1 ∧ Valued.v t = exp (-1 : ℤ)))
    {b : Fin 3 → Fv} (hb : b ∈ loc v L.1) (hQb : Valued.v (Q.evalIn Fv b) = exp (-1 : ℤ)) :
    ((σ * u⁻¹ : orthGroup Q Fv) : GL (Fin 3) Fv).val *ᵥ b - ε • b ∈ pLat v L := by
  have hu' : u⁻¹ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q Fv := (Subgroup.inv_mem _ hu)
  have hθu' : spinorNorm Q Fv u⁻¹ = 1 := by
    have := map_inv (spinorNormHom Q Fv hQ) u
    rw [spinorNormHom_apply, spinorNormHom_apply, hθu, inv_one] at this
    exact this
  have hone : IsUnitSqClass v (spinorNorm Q Fv u⁻¹) := by
    rw [hθu']
    exact ⟨1, map_one _, ((sqClassOf_eq_one_iff one_ne_zero).mpr ⟨1, (mul_one 1).symm⟩).symm⟩
  have hA : (u⁻¹ : GL (Fin 3) Fv).val *ᵥ b - b ∈ pLat v L :=
    (ch10_example2 v Q hQ h2 L γ hγ hint hdet haniso hu' hb hQb).1 hone
  have hB : (σ : GL (Fin 3) Fv).val *ᵥ ((u⁻¹ : GL (Fin 3) Fv).val *ᵥ b - b) ∈ pLat v L :=
    mulVec_mem_pLat hσ.1 hA
  have hsplit : ((σ * u⁻¹ : orthGroup Q Fv) : GL (Fin 3) Fv).val *ᵥ b =
      (σ : GL (Fin 3) Fv).val *ᵥ ((u⁻¹ : GL (Fin 3) Fv).val *ᵥ b - b) + (σ : GL (Fin 3) Fv).val *ᵥ b := by
    rw [Matrix.mulVec_sub, sub_add_cancel, Matrix.mulVec_mulVec]
    rfl
  rcases hε with ⟨rfl, htv⟩ | ⟨rfl, htv⟩
  · have hC : (σ : GL (Fin 3) Fv).val *ᵥ b - b ∈ pLat v L :=
      (ch10_example2 v Q hQ h2 L γ hγ hint hdet haniso hσ hb hQb).1 ⟨t, htv, hθσ⟩
    have := add_mem_pLat L hB hC
    rw [hsplit, one_smul]
    convert this using 1
    abel
  · have hC : (σ : GL (Fin 3) Fv).val *ᵥ b + b ∈ pLat v L := by
      refine (ch10_example2 v Q hQ h2 L γ hγ hint hdet haniso hσ hb hQb).2 ⟨t / ((LocalDensity.NF.π v : 𝔬) : Fv), ?_, ?_⟩
      · rw [map_div₀, htv, valued_pi, div_self exp_ne_zero]
      · rw [mul_div_cancel₀ _ pi_ne_zero]; exact hθσ
    have := add_mem_pLat L hB hC
    rw [hsplit, neg_smul, one_smul, sub_neg_eq_add]
    convert this using 1
    abel

end LocalCongruence

/-! ### Example 3 -/

section Example3Main

variable (Q : QuadForm ℚ 3)

/-- **Cassels, Ch. 10, Example 3** (p. 193; Cassels' $\phi$ is $Q$, his $\mathbb Z$-lattice $\Lambda$ is `L`, the primes
$p$ are the places `v : HeightOneSpectrum (𝓞 ℚ)`). Let $\Lambda$ be a $\mathbb Z$-lattice in a $3$-dimensional regular
quadratic space over $\mathbb Q$ such that (i) $Q$ is indefinite (`hind`), (ii) $Q$ is integer-valued on $\Lambda$
(`hint`), (iii) for every prime $p$ every $p$-adic unit is a spinor norm of a rotation of $\Lambda_p$ (`hU`:
$U_p \subseteq \theta(O^+(\Lambda_p))$, `localSpinorNormGroup`). Let `Pstar` be a set of primes at each of which
$\Lambda_p$ satisfies the hypotheses of Examples 1 and 2: $p \ne 2$ (`h2`), the determinant of $\Lambda_p$ is divisible
by $p$ exactly once (`hdet`: for a basis `γ` of $\Lambda_p$ the Gram matrix `locGram Q v γ` of the bilinear form $2Q$ has
determinant of valuation $\exp(-1)$; $2$ is a unit), and $V_p$ is anisotropic (`hani`); the set is automatically finite
(`finite_setOf_det_valued_eq`). Let $\eta_p = \pm 1$ (`η`, `hη`) be given for $p \in P^*$ and let `b` $\in \Lambda$
(`hb`) satisfy $\lvert Q(b)\rvert_p = p^{-1}$ for $p \in P^*$ (`hbv`). Then there is a rotation
$\beta \in O^+(\Lambda)$ with $\beta b \equiv \eta_p b \pmod{p\Lambda}$ for all $p \in P^*$. Here the group
$O^+(\Lambda)$ is, as in `Ex11Statement`, the group of rational rotations $\beta \in O^+(V)$ (`Tamagawa.soSub Q ℚ`)
that stabilize $\Lambda_w$ at every prime $w$ (`locAct w (orthMap Q _ β) (loc w L.1) = loc w L.1`; equivalently
$\beta\Lambda = \Lambda$, because a lattice is the intersection of its localizations), and
$p\Lambda$ is `v.asIdeal • L.1`.

*Proof* (not Cassels' sketch): choose $t = \prod p$ over the primes $p \in P^*$ with $\eta_p = -1$. At every prime $w$
choose $\sigma_w \in O^+(\Lambda_w)$ of spinor norm the class of $t$ (Example 1 for $w \in P^*$, (iii) otherwise, since
then $t$ is a unit); by Example 2, $\sigma_p b \equiv \eta_p b \pmod{p\Lambda_p}$. A rational rotation $\rho$ has spinor
norm $t$ everywhere (O'Meara 101:8, the form being isotropic at the infinite place), and strong approximation
(`strongApproximationSpin`) gives $\delta \in O'(V)$ with $u_w = (\rho\delta)_w^{-1}\sigma_w \in O(\Lambda_w)$ of spinor norm
$1$ for all $w$ (`exists_rotation_approx`). Then $\beta = \rho\delta$ stabilizes every $\Lambda_w$ and
$\beta b = \sigma_p u_p^{-1} b \equiv \sigma_p b \equiv \eta_p b$, by Example 2 for $u_p^{-1}$ (unit class) and for
$\sigma_p$ (`local_congruence`). Unconditional. -/
@[kb "cassels1978" "Ch. 10, Example 3, p. 193"]
theorem ch10_example3 (hQ : Q.Nondegenerate) (hind : IsIndefinite Q) (L : Lat ℚ 3)
    (hint : ∀ x ∈ L.1, ∃ z : ℤ, Q.eval x = z)
    (hU : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (Pstar : Set (HeightOneSpectrum (𝓞 ℚ)))
    (h2 : ∀ v ∈ Pstar, (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hani : ∀ v ∈ Pstar, ¬ Q.IsotropicIn (v.adicCompletion ℚ))
    (hdet : ∀ v ∈ Pstar, ∃ γ : GL (Fin 3) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = exp (-1 : ℤ))
    (b : Fin 3 → ℚ) (hb : b ∈ L.1)
    (hbv : ∀ v ∈ Pstar, Valued.v (Q.evalIn (v.adicCompletion ℚ) (locVec v b)) = exp (-1 : ℤ))
    (η : HeightOneSpectrum (𝓞 ℚ) → ℚ) (hη : ∀ v ∈ Pstar, η v = 1 ∨ η v = -1) :
    ∃ β ∈ Tamagawa.soSub Q ℚ,
      (∀ v ∈ Pstar, ((β : orthGroup Q ℚ) : GL (Fin 3) ℚ).val.mulVec b - η v • b ∈ v.asIdeal • L.1) ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        locAct w ((orthMap Q (w.adicCompletion ℚ) β : orthGroup Q _) : GL (Fin 3) (w.adicCompletion ℚ))
          (loc w L.1) = loc w L.1 := by
  classical
  have hfin : Pstar.Finite := (finite_setOf_det_valued_eq Q hQ L).subset fun v hv => hdet v hv
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset.filter (fun v => η v = -1) with hS
  have hSP : ∀ v ∈ S, v ∈ Pstar := fun v hv => hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hSη : ∀ v ∈ S, η v = -1 := fun v hv => (Finset.mem_filter.mp hv).2
  set ε : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun _ => 1 with hε
  set t0 : 𝓞 ℚ := ∏ w ∈ S, primeGen w ^ ε w with ht0
  set t : ℚ := algebraMap (𝓞 ℚ) ℚ t0 with ht
  have ht0ne : t ≠ 0 := by
    refine (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ)).mpr ?_
    exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  have htin : ∀ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) t) = exp (-1 : ℤ) := by
    intro v hv
    rw [ht, ← IsScalarTower.algebraMap_apply, ht0, valued_prod_primeGen_of_mem v ε hv]
    simp [hε]
  have htout : ∀ v ∉ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) t) = 1 := by
    intro v hv
    rw [ht, ← IsScalarTower.algebraMap_apply, ht0]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have htv0 : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (v.adicCompletion ℚ) t ≠ 0 := fun v =>
    (map_ne_zero _).mpr ht0ne
  -- the local rotations `σ_w`
  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ σ : orthGroup Q (w.adicCompletion ℚ),
      σ ∈ locStabV Q w L ⊓ Tamagawa.soSub Q (w.adicCompletion ℚ) ∧
      spinorNorm Q (w.adicCompletion ℚ) σ = sqClassOf (algebraMap ℚ (w.adicCompletion ℚ) t) := by
    intro w
    have hmem : Units.mk0 _ (htv0 w) ∈ localSpinorNormGroup Q hQ w L := by
      by_cases hw : w ∈ Pstar
      · obtain ⟨γ, hγ, hd⟩ := hdet w hw
        have := localSpinorNormGroup_eq_top_of_det Q w hQ (h2 w hw) L γ hγ (loc_evalIn_le_one Q L w hint) hd
        rw [this]; exact Subgroup.mem_top _
      · exact hU w _ (htout w fun hS' => hw (hSP w hS'))
    obtain ⟨σ, hσ, hθ⟩ := (mem_localSpinorNormGroup Q hQ w L).mp hmem
    exact ⟨σ, hσ, by rw [hθ, sqClassOf_of_ne_zero (htv0 w)]⟩
  choose σ hσ hσθ using hloc
  obtain ⟨β, hβso, hβ⟩ := exists_rotation_approx Q hQ hind L ht0ne σ (fun w => (hσ w).1) (fun w => (hσ w).2) hσθ
  have hβstab : ∀ w : HeightOneSpectrum (𝓞 ℚ), orthMap Q (w.adicCompletion ℚ) β ∈ locStabV Q w L := by
    intro w
    have h1 := (hβ w).1.1
    have h2' : orthMap Q (w.adicCompletion ℚ) β = σ w * ((orthMap Q (w.adicCompletion ℚ) β)⁻¹ * σ w)⁻¹ := by
      group
    rw [h2']
    exact (locStabV Q w L).mul_mem (hσ w).1 ((locStabV Q w L).inv_mem h1)
  refine ⟨β, hβso, fun v hv => ?_, fun w => hβstab w⟩
  -- the congruence at `v ∈ Pstar`
  obtain ⟨γ, hγ, hd⟩ := hdet v hv
  set K := v.adicCompletion ℚ with hK
  have hbmem : locVec v b ∈ loc v L.1 := locVec_mem_loc v hb
  have hβu : orthMap Q K β = σ v * ((orthMap Q K β)⁻¹ * σ v)⁻¹ := by group
  have hηv := hη v hv
  have hcong : ((orthMap Q K β : orthGroup Q K) : GL (Fin 3) K).val *ᵥ locVec v b -
      algebraMap ℚ K (η v) • locVec v b ∈ pLat v L := by
    rw [hβu]
    refine local_congruence v Q hQ (h2 v hv) L γ hγ (loc_evalIn_le_one Q L v hint) hd (hani v hv) (hσ v) (hβ v).1
      (hβ v).2 (hσθ v) (algebraMap ℚ K (η v)) ?_ hbmem (hbv v hv)
    rcases hηv with h | h
    · left
      refine ⟨by rw [h, map_one], htout v fun hvS => ?_⟩
      have := hSη v hvS
      rw [h] at this
      norm_num at this
    · right
      refine ⟨by rw [h, map_neg, map_one], htin v ?_⟩
      exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hv, h⟩
  have hloc_z : ∀ w : HeightOneSpectrum (𝓞 ℚ), locVec w (((β : orthGroup Q ℚ) : GL (Fin 3) ℚ).val.mulVec b - η v • b) =
      ((orthMap Q (w.adicCompletion ℚ) β : orthGroup Q _) : GL (Fin 3) (w.adicCompletion ℚ)).val *ᵥ locVec w b -
        algebraMap ℚ (w.adicCompletion ℚ) (η v) • locVec w b := by
    intro w
    rw [map_sub, locVec_mulVec]
    congr 1
    ext i; simp
  refine mem_ideal_smul_of_mem_pLat v L ?_ ?_
  · rw [mem_iff_forall_loc L.2]
    intro w
    rw [hloc_z w]
    refine (loc w L.1).sub_mem (mulVec_mem_loc (hβstab w) (locVec_mem_loc w hb)) ?_
    rcases hηv with h | h
    · rw [h, map_one, one_smul]; exact locVec_mem_loc w hb
    · rw [h, map_neg, map_one, neg_smul, one_smul]; exact (loc w L.1).neg_mem (locVec_mem_loc w hb)
  · rw [hloc_z v]; exact hcong

end Example3Main

end QuadFormsKB.Lattices
