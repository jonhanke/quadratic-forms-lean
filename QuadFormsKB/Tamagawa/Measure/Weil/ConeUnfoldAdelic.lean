import QuadFormsKB.Tamagawa.Measure.Weil.ConeOrbitsNF
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoCone
import QuadFormsKB.Tamagawa.Measure.ConeAdelicDw

/-!
# The cone unfolding: Step 3 of Weil's induction

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n\ge3$ variables with $Q = Q_0\otimes F$ isotropic,
$G = SO(V)$ with Weil's measure $\mu$ = `muTam Q₀ hQ 1`, $\Gamma = G(F)$, $D$ a fundamental domain of $\Gamma$. Fix
$\xi_0\in C(F)\setminus0$ (a rational isotropic vector) and let $P = \operatorname{Stab}_{G(\mathbb A)}(\xi_0)$
(`stabP`), with $\Gamma_P = \Gamma\cap P$ (`gammaP`). Weil 1982, §4.5, p. 108.

**The data and the input.** `AdelicConeData Q₀ Q'` consists of $\xi_0$, the adelic punctured cone $C\subseteq\mathbb A^n$
with a measure $\sigma_C$, coordinates $C\times P\cong G(\mathbb A)$, a measure $\mu_P$ on $P$, and the semidirect-product
structure $P = N\rtimes SO(V')(\mathbb A)$, $N\cong V'_{\mathbb A} = \mathbb A^k$, $V' = \xi_0^\perp/\xi_0$ with form $Q'$
in $k = n-2$ variables: maps $n_{\mathbb A} : \mathbb A^k\to P$, $h_{\mathbb A} : SO(Q')(\mathbb A)\to P$, the action
$\operatorname{act}$ of $SO(Q')(\mathbb A)$ on $\mathbb A^k$ and the coordinates $\mathbb A^k\times SO(Q')(\mathbb A)\cong P$.
Its properties (`AdelicConeFibration`, **input**: the adelic assembly of the local cone orbital
identities) are the orbit-coordinate equations, the fibration
$\mu = \mathrm{coord}_*(\sigma_C\otimes\mu_P)$ with constant $1$, homogeneity of degree $n-2$ of $\sigma_C$ under the ideles,
the semidirect-product relations, rationality ($\Gamma_P = N(F)\rtimes SO(Q')(F)$), left invariance of $\mu_P$ and
$\mu_P = (dw^{\mathrm{Tam}}\otimes\mu_{SO(Q')})$ in the coordinates. It says nothing about the covolume of $\Gamma$.

**Main results.**
* **`AdelicConeFibration.covolume_gammaP`**: $\operatorname{covol}(\Gamma_P\backslash P) = \operatorname{covol}(SO(Q')(F)
  \backslash SO(Q')(\mathbb A))\cdot\operatorname{vol}(V'_{\mathbb A}/V'_F) = \operatorname{covol}(SO(Q'))$, through the
  exact fundamental domain $n_{\mathbb A}(D_N)\,h_{\mathbb A}(D_H)$ and $\operatorname{vol}(D_N) = 1$
  (`addCovolume_dwTam`).
* **`AdelicConeFibration.lintegral_unfold`** (the cone unfolding, in $[0,\infty]$, **no hypothesis on
  $\operatorname{vol}(\Gamma\backslash G)$**): $\int_D\sum_{\eta\in C(F)\setminus0}f(g^{-1}\eta)\,d\mu(g) =
  \operatorname{covol}(SO(Q'))\int_Cf\,d\sigma_C$; it uses Witt's theorem on the cone (`exists_smul_eq_ratCone`, $n\ge3$).
* **`AdelicConeFibration.coneC1_eq`**, **`AdelicConeFibration.coneC2_eq`** (the cone terms of Step 2 in closed form, $s>0$):
  $$C_1(s) = \operatorname{covol}(SO(Q'))\,I_C(\Phi)\,\frac{\rho_F}{2+2s},\qquad
    C_2(s) = \operatorname{covol}(SO(Q'))\,I_C(\hat\Phi)\,\frac{\rho_F}{n-2+2s},\qquad I_C(\Phi) = \int_C\Phi\,d\sigma_C.$$
* `AdelicConeFibration.coneC1_le`, `coneC2_le`: the bounds for $0 < s\le1$ used in Step 4, finite when
  $\operatorname{covol}(SO(Q')) < \infty$ and $I_C(\Phi), I_C(\hat\Phi) < \infty$.
-/

open MeasureTheory Set MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta

variable {F : Type} [Field F] [NumberField F] {n k : ℕ}

/-! ### The adelic stabilizer of a vector -/

/-- **The stabilizer** $P = \operatorname{Stab}_{SO(V)(\mathbb A)}(y)$ of $y\in\mathbb A^n$ (for $y = \xi_0$ rational
isotropic: the parabolic $P' = SO(V')\ltimes V'$, adelically). -/
abbrev stabP (Q₀ : QuadForm (𝓞 F) n) (y : AdeleSpace F (Fin n)) : Subgroup (SOAdele Q₀) := stabilizer (SOAdele Q₀) y

/-- **The rational points of the stabilizer**: $\Gamma_P = SO(V)(F)\cap P$, as a subgroup of $P$. -/
abbrev gammaP (Q₀ : QuadForm (𝓞 F) n) (y : AdeleSpace F (Fin n)) : Subgroup (stabP Q₀ y) :=
  (GammaSOAdele Q₀).subgroupOf (stabP Q₀ y)

instance (Q₀ : QuadForm (𝓞 F) n) (y : AdeleSpace F (Fin n)) : Countable (gammaP Q₀ y) := by
  have := countable_GammaSOAdele Q₀
  refine Function.Injective.countable (f := fun γ : gammaP Q₀ y => (⟨γ.1.1, γ.2⟩ : GammaSOAdele Q₀)) ?_
  intro a b h
  simp only at h
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))

instance (Q₀ : QuadForm (𝓞 F) n) (y : AdeleSpace F (Fin n)) :
    MeasurableConstSMul (gammaP Q₀ y) (stabP Q₀ y) :=
  ⟨fun γ => ((measurable_const_mul ((γ : stabP Q₀ y) : SOAdele Q₀)).comp measurable_subtype_coe).subtype_mk⟩

/-! ### The adelic cone data and the fibration (input) -/

/-- **Adelic data for the cone** (Weil 1982, §4.5, p. 108): a base point $\xi_0\in C(F)\setminus0$, the
adelic punctured cone $C\subseteq\mathbb A_F^n$ with its measure $\sigma_C$, a measure $\mu_P$ on the stabilizer
$P$ = `stabP Q₀ ξ₀`, coordinates $C\times P\cong SO(V)(\mathbb A)$, and the semidirect-product structure
$P = N\rtimes SO(Q')(\mathbb A)$ with $N\cong\mathbb A^k$ ($Q'$ the form on $V' = \xi_0^\perp/\xi_0$). Pure data, no
properties (those are `AdelicConeFibration`). Fields: `ξ`, `C`, `σ`, `μP`, `coord`, `nA`, `hA`, `act`, `decomp`. -/
structure AdelicConeData (Q₀ : QuadForm (𝓞 F) n) (Q' : QuadForm (𝓞 F) k) where
  /-- The base point $\xi_0\in C(F)\setminus0$. -/
  ξ : RatCone Q₀
  /-- The adelic punctured cone $C^\circ(\mathbb A)$. -/
  C : Set (AdeleSpace F (Fin n))
  /-- Its measure $\sigma_C$ (Weil's $dx/dQ$ on the cone, Tamagawa-normalized). -/
  σ : Measure C
  /-- The measure $\mu_P$ on the stabilizer $P$. -/
  μP : Measure (stabP Q₀ (diagVec F (Fin n) ξ.1))
  /-- The coordinates $C\times P\cong SO(V)(\mathbb A)$. -/
  coord : C × stabP Q₀ (diagVec F (Fin n) ξ.1) ≃ᵐ SOAdele Q₀
  /-- The unipotent radical $n_{\mathbb A} : \mathbb A^k\to N\subseteq P$. -/
  nA : AdeleSpace F (Fin k) → stabP Q₀ (diagVec F (Fin n) ξ.1)
  /-- The Levi factor $h_{\mathbb A} : SO(Q')(\mathbb A)\to P$. -/
  hA : SOAdele Q' →* stabP Q₀ (diagVec F (Fin n) ξ.1)
  /-- The action of $SO(Q')(\mathbb A)$ on $\mathbb A^k$ by conjugation of $N$. -/
  act : SOAdele Q' → AdeleSpace F (Fin k) → AdeleSpace F (Fin k)
  /-- The coordinates $\mathbb A^k\times SO(Q')(\mathbb A)\cong P$. -/
  decomp : AdeleSpace F (Fin k) × SOAdele Q' ≃ᵐ stabP Q₀ (diagVec F (Fin n) ξ.1)

/-- **Weil's adelic fibration over the cone** (**input**; Weil 1982, Lemma 2.4.1, Thm 2.4.3 [unverified page], applied on
p. 108 to $G/P' = C^\circ$). For data `A`:
* `mul`, `orbit`: $\mathrm{coord}(x, p'p) = p'\,\mathrm{coord}(x,p)$ and $\mathrm{coord}(x,p)^{-1}\xi_0 = x$;
* `sFinite`: $\sigma_C$ is s-finite;
* `fib`: **$\mu_{SO(V)} = \mathrm{coord}_*(\sigma_C\otimes\mu_P)$** with constant exactly $1$ (the local constants
  $|2c_0|_v^{-2(k+1)}$ multiply to $1$, `prod_cone_constants_eq_one`);
* `homog`: $\int_C f(zx)\,d\sigma_C(x) = \|z\|^{2-n}\int_C f\,d\sigma_C$ for every idele $z$ (homogeneity of degree $n-2$,
  `map_smul_sigConeV` and its archimedean analogues, product formula);
* `decomp_apply`, `nA_add`, `conj`: $\mathrm{decomp}(w,h) = n_{\mathbb A}(w)h_{\mathbb A}(h)$,
  $n_{\mathbb A}(w+w') = n_{\mathbb A}(w)n_{\mathbb A}(w')$, $h_{\mathbb A}(h)n_{\mathbb A}(w)h_{\mathbb A}(h)^{-1} =
  n_{\mathbb A}(\operatorname{act}(h,w))$;
* `nA_rat`, `hA_rat`, `rat_decomp`: $\Gamma_P = n_{\mathbb A}(F^k)\,h_{\mathbb A}(SO(Q')(F))$;
* `leftInv`: $\mu_P$ is left invariant;
* `μP_eq`: $\mu_P = \mathrm{decomp}_*(dw^{\mathrm{Tam}}\otimes\mu_{SO(Q')})$ (`dwTam`, Weil's `muTam`).
It says nothing about the covolume of $SO(V)(F)$ or of $SO(Q')(F)$. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 108 (fibration over the cone)"]
structure AdelicConeFibration {Q₀ : QuadForm (𝓞 F) n} (hQ : Q₀.Nondegenerate) {Q' : QuadForm (𝓞 F) k}
    (hQ' : Q'.Nondegenerate) (A : AdelicConeData Q₀ Q') : Prop where
  /-- Left equivariance in the fibre coordinate. -/
  mul : ∀ (x : A.C) (p p' : stabP Q₀ (diagVec F (Fin n) A.ξ.1)),
    A.coord (x, p' * p) = (p' : SOAdele Q₀) * A.coord (x, p)
  /-- The first coordinate is the orbit point $g^{-1}\xi_0$. -/
  orbit : ∀ (x : A.C) (p : stabP Q₀ (diagVec F (Fin n) A.ξ.1)),
    (A.coord (x, p))⁻¹ • diagVec F (Fin n) A.ξ.1 = x.1
  /-- $\sigma_C$ is s-finite. -/
  sFinite : SFinite A.σ
  /-- The fibration identity of Tamagawa measures, constant $1$. -/
  fib : muTam Q₀ hQ 1 = (A.σ.prod A.μP).map A.coord
  /-- Homogeneity of degree $n - 2$ under the ideles. -/
  homog : ∀ (z : (Adeles F)ˣ) (f : AdeleSpace F (Fin n) → ℝ≥0∞), Measurable f →
    ∫⁻ x, f (z • x.1) ∂A.σ = ENNReal.ofReal (ideleNorm F z ^ ((2 : ℝ) - n)) * ∫⁻ x, f x.1 ∂A.σ
  /-- The coordinates of $P$ are $(w, h)\mapsto n_{\mathbb A}(w)h_{\mathbb A}(h)$. -/
  decomp_apply : ∀ w h, A.decomp (w, h) = A.nA w * A.hA h
  /-- $n_{\mathbb A}$ is additive. -/
  nA_add : ∀ w w', A.nA (w + w') = A.nA w * A.nA w'
  /-- Conjugation of $N$ by the Levi factor. -/
  conj : ∀ h w, A.hA h * A.nA w * (A.hA h)⁻¹ = A.nA (A.act h w)
  /-- $n_{\mathbb A}(F^k)\subseteq\Gamma$. -/
  nA_rat : ∀ ν ∈ diagVecSub F (Fin k), ((A.nA ν : stabP Q₀ (diagVec F (Fin n) A.ξ.1)) : SOAdele Q₀) ∈
    GammaSOAdele Q₀
  /-- $h_{\mathbb A}(SO(Q')(F))\subseteq\Gamma$. -/
  hA_rat : ∀ η ∈ GammaSOAdele Q', ((A.hA η : stabP Q₀ (diagVec F (Fin n) A.ξ.1)) : SOAdele Q₀) ∈
    GammaSOAdele Q₀
  /-- The coordinates of a rational point of $P$ are rational. -/
  rat_decomp : ∀ p : stabP Q₀ (diagVec F (Fin n) A.ξ.1), (p : SOAdele Q₀) ∈ GammaSOAdele Q₀ →
    (A.decomp.symm p).1 ∈ diagVecSub F (Fin k) ∧ (A.decomp.symm p).2 ∈ GammaSOAdele Q'
  /-- $\mu_P$ is left invariant. -/
  leftInv : A.μP.IsMulLeftInvariant
  /-- $\mu_P = dw^{\mathrm{Tam}}\otimes\mu_{SO(Q')}$ in the coordinates. -/
  μP_eq : A.μP = ((ConeAdelic.dwTam F k).prod (muTam Q' hQ' 1)).map A.decomp

/-- **The cone integral** $I_C(\Phi) = \int_{C^\circ(\mathbb A)}\Phi\,d\sigma_C$ for the data `A`. -/
def AdelicConeData.coneInt {Q₀ : QuadForm (𝓞 F) n} {Q' : QuadForm (𝓞 F) k} (A : AdelicConeData Q₀ Q')
    (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, Φ x.1 ∂A.σ

/-- The covolume of $SO(Q')(F)$ in $SO(Q')(\mathbb A)$ (a priori in $[0,\infty]$). -/
abbrev covolSO (Q' : QuadForm (𝓞 F) k) (hQ' : Q'.Nondegenerate) : ℝ≥0∞ :=
  covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' 1)

/-! ### The covolume of $\Gamma_P$ -/

theorem dwTam_eq_muAddVec (k : ℕ) : ConeAdelic.dwTam F k = muAddVec F (Fin k) := by
  rw [ConeAdelic.dwTam, ← ConeAdelic.muAddVec_eq_smul_dwVec]

variable {Q₀ : QuadForm (𝓞 F) n} {hQ : Q₀.Nondegenerate} {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
  {A : AdelicConeData Q₀ Q'}

theorem mul_conj_aux {G : Type*} [Group G] (a b c d : G) : a * b * (c * d) = a * (b * c * b⁻¹) * (b * d) := by
  group

/-- The multiplication law in the coordinates of $P$:
$\mathrm{decomp}(\nu,\eta)\,\mathrm{decomp}(w,h) = \mathrm{decomp}(\nu + \operatorname{act}(\eta,w),\eta h)$. -/
theorem AdelicConeFibration.decomp_mul (hA : AdelicConeFibration hQ hQ' A) (ν w : AdeleSpace F (Fin k))
    (η h : SOAdele Q') : A.decomp (ν, η) * A.decomp (w, h) = A.decomp (ν + A.act η w, η * h) := by
  rw [hA.decomp_apply, hA.decomp_apply, hA.decomp_apply, hA.nA_add, ← hA.conj, A.hA.map_mul η h]
  exact mul_conj_aux _ _ _ _

/-- **An exact fundamental domain of $\Gamma_P$ in $P$**: $\mathrm{decomp}(D_N\times D_H)$ for exact fundamental domains
$D_N$ of $F^k$ in $\mathbb A^k$ and $D_H$ of $SO(Q')(F)$ in $SO(Q')(\mathbb A)$. -/
theorem AdelicConeFibration.existsUnique_smul_mem (hA : AdelicConeFibration hQ hQ' A) {DN : Set (AdeleSpace F (Fin k))}
    (hDN : ∀ w, ∃! ν : diagVecSub F (Fin k), ν +ᵥ w ∈ DN) {DH : Set (SOAdele Q')}
    (hDH : ∀ h : SOAdele Q', ∃! η : GammaSOAdele Q', η • h ∈ DH) (p : stabP Q₀ (diagVec F (Fin n) A.ξ.1)) :
    ∃! γ : gammaP Q₀ (diagVec F (Fin n) A.ξ.1), γ • p ∈ A.decomp.symm ⁻¹' (DN ×ˢ DH) := by
  set w := (A.decomp.symm p).1
  set h := (A.decomp.symm p).2
  have hp : p = A.decomp (w, h) := (A.decomp.apply_symm_apply p).symm
  obtain ⟨η, hη, hηu⟩ := hDH h
  obtain ⟨ν, hν, hνu⟩ := hDN (A.act η w)
  have hmem : ∀ (ν' : AdeleSpace F (Fin k)) (η' : SOAdele Q'),
      A.decomp (ν', η') * p ∈ A.decomp.symm ⁻¹' (DN ×ˢ DH) ↔ ν' + A.act η' w ∈ DN ∧ η' * h ∈ DH := by
    intro ν' η'
    rw [hp, hA.decomp_mul, mem_preimage, MeasurableEquiv.symm_apply_apply, mem_prod]
  have hγ : ((A.decomp ((ν : AdeleSpace F (Fin k)), (η : SOAdele Q')) : stabP Q₀ _) : SOAdele Q₀) ∈
      GammaSOAdele Q₀ := by
    rw [hA.decomp_apply, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (hA.nA_rat _ ν.2) (hA.hA_rat _ η.2)
  refine ⟨⟨_, hγ⟩, ?_, fun γ' hγ' => ?_⟩
  · show A.decomp ((ν : AdeleSpace F (Fin k)), (η : SOAdele Q')) * p ∈ _
    rw [hmem]
    exact ⟨hν, hη⟩
  · obtain ⟨hr1, hr2⟩ := hA.rat_decomp γ'.1 γ'.2
    obtain ⟨⟨ν', η'⟩, hq⟩ : ∃ q, A.decomp.symm γ'.1 = q := ⟨_, rfl⟩
    rw [hq] at hr1 hr2
    have hγ'eq : (γ'.1 : stabP Q₀ _) = A.decomp (ν', η') := by rw [← hq, A.decomp.apply_symm_apply]
    have h1 : A.decomp (ν', η') * p ∈ A.decomp.symm ⁻¹' (DN ×ˢ DH) := by
      rw [← hγ'eq]; exact hγ'
    rw [hmem] at h1
    have e1 : (⟨η', hr2⟩ : GammaSOAdele Q') = η := hηu _ h1.2
    have hη' : η' = (η : SOAdele Q') := congrArg Subtype.val e1
    rw [hη'] at h1
    have e2 : (⟨ν', hr1⟩ : diagVecSub F (Fin k)) = ν := hνu _ h1.1
    have hν' : ν' = (ν : AdeleSpace F (Fin k)) := congrArg Subtype.val e2
    apply Subtype.ext
    show (γ'.1 : stabP Q₀ _) = A.decomp ((ν : AdeleSpace F (Fin k)), (η : SOAdele Q'))
    rw [hγ'eq, hν', hη']

/-- **$\operatorname{covol}(\Gamma_P\backslash P) = \operatorname{covol}(SO(Q'))\cdot\operatorname{vol}(V'_{\mathbb A}/V'_F) =
\operatorname{covol}(SO(Q'))$** ($\operatorname{vol}(V'_{\mathbb A}/V'_F) = 1$ for
$dw^{\mathrm{Tam}}$), together with an exact measurable fundamental domain realizing it. -/
@[kb "weil1982" "§4.5, p. 108 (covol(P') = covol(SO(V'))·vol(V'_A/V'_k)) [unverified page]"]
theorem AdelicConeFibration.exists_fundamentalDomain_gammaP (hA : AdelicConeFibration hQ hQ' A) :
    ∃ E : Set (stabP Q₀ (diagVec F (Fin n) A.ξ.1)), MeasurableSet E ∧
      (∀ p, ∃! γ : gammaP Q₀ (diagVec F (Fin n) A.ξ.1), γ • p ∈ E) ∧ A.μP E = covolSO Q' hQ' := by
  have := discreteTopology_GammaSOAdele Q'
  have := countable_GammaSOAdele Q'
  obtain ⟨DH, hDHm, hDH⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q')
  have hDNm : MeasurableSet (fundDomVec F (Fin k)) := MeasurableSet.univ_pi fun _ => measurableSet_fundDom
  refine ⟨A.decomp.symm ⁻¹' (fundDomVec F (Fin k) ×ˢ DH), A.decomp.symm.measurable (hDNm.prod hDHm),
    hA.existsUnique_smul_mem existsUnique_vadd_mem_fundDomVec hDH, ?_⟩
  have hDHf : IsFundamentalDomain (GammaSOAdele Q') DH (muTam Q' hQ' 1) :=
    IsFundamentalDomain.mk' hDHm.nullMeasurableSet hDH
  rw [hA.μP_eq, MeasurableEquiv.map_apply, ← preimage_comp, show (A.decomp.symm ∘ A.decomp) = id from
      funext A.decomp.symm_apply_apply, preimage_id, Measure.prod_prod, dwTam_eq_muAddVec, muAddVec_fundDomVec,
    one_mul, covolSO, hDHf.covolume_eq_volume]

/-! ### The cone unfolding -/

/-- The orbit coordinates of `AdelicConeData` satisfying the fibration. -/
def AdelicConeFibration.orbitCoord (hA : AdelicConeFibration hQ hQ' A) :
    OrbitCoord (stabP Q₀ (diagVec F (Fin n) A.ξ.1)).subtype (Subtype.val : A.C → AdeleSpace F (Fin n))
      (diagVec F (Fin n) A.ξ.1) :=
  ⟨A.coord, hA.mul, hA.orbit⟩

/-- **The cone unfolding** (Weil 1982, §4.5, p. 108; the abstract `lintegral_sphere_unfold`
instantiated with $X = C(F)\setminus0$ and $H = P$): for $n\ge3$, a fundamental domain $D$ and measurable $f\ge0$,
$$\int_D\sum_{\eta\in C(F)\setminus0}f(g^{-1}\eta)\,d\mu(g) = \operatorname{covol}(SO(Q')(F)\backslash SO(Q')(\mathbb A))
  \cdot\int_C f\,d\sigma_C$$
in $[0,\infty]$, with no hypothesis on $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A))$. -/
@[kb "weil1982" "§4.5, p. 108 (unfolding along the cone); Lemma 2.4.1, Thm 2.4.3 [unverified page]"]
theorem AdelicConeFibration.lintegral_unfold (hn : 3 ≤ n) (hA : AdelicConeFibration hQ hQ' A)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {f : AdeleSpace F (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g in D, ∑' η : RatCone Q₀, f (g⁻¹ • diagVec F (Fin n) η.1) ∂muTam Q₀ hQ 1 =
      covolSO Q' hQ' * ∫⁻ x, f x.1 ∂A.σ := by
  have := countable_GammaSOAdele Q₀
  haveI := hA.sFinite
  have : SigmaFinite (muAddVec F (Fin k)) := by unfold muAddVec; infer_instance
  have : SFinite A.μP := by rw [hA.μP_eq, dwTam_eq_muAddVec]; infer_instance
  have := hA.leftInv
  set P := stabP Q₀ (diagVec F (Fin n) A.ξ.1)
  have hinv : ∀ (c : gammaP Q₀ (diagVec F (Fin n) A.ξ.1)) (t : Set P),
      A.μP ((fun p => c • p) ⁻¹' t) = A.μP t := fun c t => by
    have e : (fun p : P => c • p) = fun p => (c : P) * p := funext fun p => Subgroup.smul_def c p
    rw [e]; exact measure_preimage_mul A.μP (c : P) t
  have : SMulInvariantMeasure (gammaP Q₀ (diagVec F (Fin n) A.ξ.1)) P A.μP := ⟨fun c t _ => hinv c t⟩
  obtain ⟨E, hEm, hEx, hEμ⟩ := hA.exists_fundamentalDomain_gammaP
  have hEf : IsFundamentalDomain (gammaP Q₀ (diagVec F (Fin n) A.ξ.1)) E A.μP :=
    IsFundamentalDomain.mk' hEm.nullMeasurableSet hEx
  have hfix : ∀ (h : P) (hh : h ∈ gammaP Q₀ (diagVec F (Fin n) A.ξ.1)),
      (⟨P.subtype h, hh⟩ : GammaSOAdele Q₀) • A.ξ = A.ξ := by
    intro h hh
    apply Subtype.ext
    apply diagVec_injective (F := F) (ι := Fin n)
    rw [diagVec_smul_ratCone]
    exact mem_stabilizer_iff.mp h.2
  have hstab : ∀ γ : GammaSOAdele Q₀, γ • A.ξ = A.ξ →
      ∃ h ∈ gammaP Q₀ (diagVec F (Fin n) A.ξ.1), P.subtype h = γ := by
    intro γ hγ
    have hγP : (γ : SOAdele Q₀) ∈ P := by
      show (γ : SOAdele Q₀) • diagVec F (Fin n) A.ξ.1 = diagVec F (Fin n) A.ξ.1
      rw [← diagVec_smul_ratCone, hγ]
    exact ⟨⟨γ, hγP⟩, γ.2, rfl⟩
  have key := lintegral_sphere_unfold (Γ := GammaSOAdele Q₀) (μ := muTam Q₀ hQ 1)
    (ΓH := gammaP Q₀ (diagVec F (Fin n) A.ξ.1)) (μH := A.μP)
    (fun η : RatCone Q₀ => diagVec F (Fin n) η.1) (fun γ η => diagVec_smul_ratCone Q₀ γ η) A.ξ
    (fun η => exists_smul_eq_ratCone Q₀ hQ hn A.ξ η) P.subtype A.σ Subtype.val hA.orbitCoord
    (fun h hh => hh) hfix hstab hEm hEx 1 (by rw [one_smul]; exact hA.fib) hD f (hf.comp measurable_subtype_coe)
  rw [key, one_mul, hEf.covolume_eq_volume, hEμ]

/-! ### The cone terms in closed form -/

theorem measurable_units_smul_left {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) (y : AdeleSpace F (Fin n)) :
    Measurable fun z : (Adeles F)ˣ => Φ (z • y) :=
  hΦ.comp (measurable_units_smul.comp (measurable_id.prodMk measurable_const))

/-- The multiplicative transform of the cone term on $\|z\|\le1$:
$f_s(y) = \int_{D_M,\ \|z\|\le1}\|z\|^{n+2s}\Phi(zy)\,d\nu(z)$. -/
def coneLoFn (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ) (y : AdeleSpace F (Fin n)) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F).indicator (fun z => zetaWeight s n z * Φ (z • y)) z ∂tamIdeles F

/-- The dual transform $f'_s(y) = \int_{D_M,\ \|z\|\le1}\|z\|^{2s}\hat\Phi(z^{-1}y)\,d\nu(z)$. -/
def coneRemFn (Φh : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ) (y : AdeleSpace F (Fin n)) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * Φh (z⁻¹ • y)) z
    ∂tamIdeles F

theorem measurable_coneLoFn_uncurry {α : Type*} [MeasurableSpace α] {Φ : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (s : ℝ) {f : α → AdeleSpace F (Fin n)} (hf : Measurable f) :
    Measurable fun p : α × (Adeles F)ˣ =>
      (normLeOne F).indicator (fun z => zetaWeight s n z * Φ (z • f p.1)) p.2 := by
  classical
  simp only [indicator_apply]
  exact Measurable.ite (measurable_snd measurableSet_normLeOne)
    (((measurable_zetaWeight s n).comp measurable_snd).mul
      (hΦ.comp (measurable_units_smul.comp (measurable_snd.prodMk (hf.comp measurable_fst))))) measurable_const

theorem measurable_coneRemFn_uncurry {α : Type*} [MeasurableSpace α] {Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦh : Measurable Φh) (s : ℝ) {f : α → AdeleSpace F (Fin n)} (hf : Measurable f) :
    Measurable fun p : α × (Adeles F)ˣ =>
      (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * Φh (z⁻¹ • f p.1)) p.2 := by
  classical
  simp only [indicator_apply]
  refine Measurable.ite (measurable_snd measurableSet_normLeOne) ?_ measurable_const
  exact ((ENNReal.measurable_ofReal.comp (continuous_ideleNorm.measurable.pow_const _)).comp measurable_snd).mul
    (hΦh.comp (measurable_units_smul.comp ((measurable_inv.comp measurable_snd).prodMk (hf.comp measurable_fst))))

theorem measurable_coneLoFn {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) (DM : Set (Adeles F)ˣ) (s : ℝ) :
    Measurable (coneLoFn Φ DM s) :=
  (measurable_coneLoFn_uncurry hΦ s measurable_id).lintegral_prod_right'

theorem measurable_coneRemFn {Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦh : Measurable Φh) (DM : Set (Adeles F)ˣ)
    (s : ℝ) : Measurable (coneRemFn Φh DM s) :=
  (measurable_coneRemFn_uncurry hΦh s measurable_id).lintegral_prod_right'

open Classical in
/-- $\mathrm{coneLo}(g,s) = \sum_{\eta\in C(F)\setminus0}f_s(g^{-1}\eta)$. -/
theorem coneLo_eq_tsum (Q₀ : QuadForm (𝓞 F) n) {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ)
    (DM : Set (Adeles F)ˣ) (s : ℝ) (g : SOAdele Q₀) :
    coneLo Q₀ Φ DM s g = ∑' η : RatCone Q₀, coneLoFn Φ DM s (g⁻¹ • diagVec F (Fin n) η.1) := by
  refine Eq.trans ?_ (tsum_ite_eq_tsum_ratCone Q₀ fun ξ => coneLoFn Φ DM s (g⁻¹ • diagVec F (Fin n) ξ))
  rw [coneLo]
  have h1 : ∀ z, (normLeOne F).indicator (fun z => zetaWeight s n z * coneTheta Q₀ Φ g z) z =
      ∑' ξ : Fin n → F, (if qF Q₀ ξ = 0 ∧ ξ ≠ 0 then (normLeOne F).indicator
        (fun z => zetaWeight s n z * Φ (z • g⁻¹ • diagVec F (Fin n) ξ)) z else 0) := by
    intro z
    by_cases hz : z ∈ normLeOne F
    · simp only [indicator_of_mem hz, coneTheta, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      split_ifs <;> simp
    · simp [indicator_of_notMem hz]
  rw [lintegral_congr h1, lintegral_tsum fun ξ => ?_]
  · refine tsum_congr fun ξ => ?_
    split_ifs
    · rfl
    · simp
  · split_ifs
    · exact (((measurable_zetaWeight s n).mul (measurable_units_smul_left hΦ _)).indicator
        measurableSet_normLeOne).aemeasurable
    · exact aemeasurable_const

open Classical in
/-- $\mathrm{coneRem}(g,s) = \sum_{\eta\in C(F)\setminus0}f'_s(g^{-1}\eta)$. -/
theorem coneRem_eq_tsum (Q₀ : QuadForm (𝓞 F) n) {Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦh : Measurable Φh)
    (DM : Set (Adeles F)ˣ) (s : ℝ) (g : SOAdele Q₀) :
    coneRem Q₀ Φh DM s g = ∑' η : RatCone Q₀, coneRemFn Φh DM s (g⁻¹ • diagVec F (Fin n) η.1) := by
  refine Eq.trans ?_ (tsum_ite_eq_tsum_ratCone Q₀ fun ξ => coneRemFn Φh DM s (g⁻¹ • diagVec F (Fin n) ξ))
  rw [coneRem]
  have h1 : ∀ z, (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * coneTheta Q₀ Φh g z⁻¹) z =
      ∑' ξ : Fin n → F, (if qF Q₀ ξ = 0 ∧ ξ ≠ 0 then (normLeOne F).indicator
        (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * Φh (z⁻¹ • g⁻¹ • diagVec F (Fin n) ξ)) z
          else 0) := by
    intro z
    by_cases hz : z ∈ normLeOne F
    · simp only [indicator_of_mem hz, coneTheta, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      split_ifs <;> simp
    · simp [indicator_of_notMem hz]
  rw [lintegral_congr h1, lintegral_tsum fun ξ => ?_]
  · refine tsum_congr fun ξ => ?_
    split_ifs
    · rfl
    · simp
  · split_ifs
    · exact (((ENNReal.measurable_ofReal.comp (continuous_ideleNorm.measurable.pow_const _)).mul
        (hΦh.comp (measurable_units_smul.comp (measurable_inv.prodMk measurable_const)))).indicator
          measurableSet_normLeOne).aemeasurable
    · exact aemeasurable_const

theorem ofReal_rpow_mul_rpow (z : (Adeles F)ˣ) (a b : ℝ) :
    ENNReal.ofReal (ideleNorm F z ^ a) * ENNReal.ofReal (ideleNorm F z ^ b) = ENNReal.ofReal (ideleNorm F z ^ (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ideleNorm_pos z).le _), ← Real.rpow_add (ideleNorm_pos z)]

/-- $\int_C f_s\,d\sigma_C = I_C(\Phi)\,\rho_F/(2+2s)$ (homogeneity of $\sigma_C$ and
`lintegral_ideleFD_le_one_rpow`). -/
theorem AdelicConeFibration.lintegral_coneLoFn (hA : AdelicConeFibration hQ hQ' A) {Φ : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, coneLoFn Φ DM s x.1 ∂A.σ = A.coneInt Φ * ENNReal.ofReal (dedekindZeta_residue F / (2 + 2 * s)) := by
  haveI := hA.sFinite
  have hm : Measurable fun p : A.C × (Adeles F)ˣ =>
      (normLeOne F).indicator (fun z => zetaWeight s n z * Φ (z • p.1.1)) p.2 :=
    measurable_coneLoFn_uncurry hΦ s measurable_subtype_coe
  unfold coneLoFn
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have h1 : ∀ z : (Adeles F)ˣ, ∫⁻ x, (normLeOne F).indicator (fun z => zetaWeight s n z * Φ (z • x.1)) z ∂A.σ =
      A.coneInt Φ * (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 + 2 * s))) z := by
    intro z
    by_cases hz : z ∈ normLeOne F
    · simp only [indicator_of_mem hz]
      have hmz : Measurable fun x : A.C => Φ (z • x.1) :=
        hΦ.comp ((measurable_const_smul z).comp measurable_subtype_coe)
      rw [lintegral_const_mul _ hmz,
        hA.homog z Φ hΦ, AdelicConeData.coneInt, zetaWeight, ← mul_assoc, ofReal_rpow_mul_rpow, mul_comm]
      congr 2
      ring_nf
    · simp [indicator_of_notMem hz]
  have hmi : Measurable fun z : (Adeles F)ˣ =>
      (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 + 2 * s))) z :=
    (ENNReal.measurable_ofReal.comp (continuous_ideleNorm.measurable.pow_const _)).indicator measurableSet_normLeOne
  rw [lintegral_congr h1, lintegral_const_mul _ hmi]
  simp_rw [indicator_rpow_eq]
  rw [lintegral_ideleFD_le_one_rpow hDM (by positivity)]

/-- $\int_C f'_s\,d\sigma_C = I_C(\hat\Phi)\,\rho_F/(n-2+2s)$ ($n\ge3$). -/
theorem AdelicConeFibration.lintegral_coneRemFn (hn : 3 ≤ n) (hA : AdelicConeFibration hQ hQ' A)
    {Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦh : Measurable Φh) {DM : Set (Adeles F)ˣ}
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, coneRemFn Φh DM s x.1 ∂A.σ =
      A.coneInt Φh * ENNReal.ofReal (dedekindZeta_residue F / ((n : ℝ) - 2 + 2 * s)) := by
  haveI := hA.sFinite
  have hm : Measurable fun p : A.C × (Adeles F)ˣ =>
      (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * Φh (z⁻¹ • p.1.1)) p.2 :=
    measurable_coneRemFn_uncurry hΦh s measurable_subtype_coe
  unfold coneRemFn
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have h1 : ∀ z : (Adeles F)ˣ, ∫⁻ x, (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * Φh (z⁻¹ • x.1)) z ∂A.σ =
      A.coneInt Φh * (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ ((n : ℝ) - 2 + 2 * s))) z := by
    intro z
    by_cases hz : z ∈ normLeOne F
    · simp only [indicator_of_mem hz]
      have hmz : Measurable fun x : A.C => Φh (z⁻¹ • x.1) :=
        hΦh.comp ((measurable_const_smul z⁻¹).comp measurable_subtype_coe)
      rw [lintegral_const_mul _ hmz,
        hA.homog z⁻¹ Φh hΦh, AdelicConeData.coneInt, ideleNorm_inv,
        Real.inv_rpow (ideleNorm_pos z).le, ← Real.rpow_neg (ideleNorm_pos z).le, ← mul_assoc, ofReal_rpow_mul_rpow,
        mul_comm]
      congr 2
      ring_nf
    · simp [indicator_of_notMem hz]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmi : Measurable fun z : (Adeles F)ˣ =>
      (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ ((n : ℝ) - 2 + 2 * s))) z :=
    (ENNReal.measurable_ofReal.comp (continuous_ideleNorm.measurable.pow_const _)).indicator measurableSet_normLeOne
  rw [lintegral_congr h1, lintegral_const_mul _ hmi]
  simp_rw [indicator_rpow_eq]
  rw [lintegral_ideleFD_le_one_rpow hDM (by linarith)]

/-- **The cone term $C_1(s)$ in closed form** (Weil 1982, §4.5, p. 108): for $n\ge3$ and $s > 0$,
$$C_1(s) = \operatorname{covol}(SO(Q'))\cdot I_C(\Phi)\cdot\frac{\rho_F}{2+2s},$$
in $[0,\infty]$, with no hypothesis on the volume of $SO(V)(F)\backslash SO(V)(\mathbb A)$. -/
@[kb "weil1982" "§4.5, p. 108 (the cone term: covol(P')·I_C(Φ)·ρ_k/(2+2s)) [unverified page]"]
theorem AdelicConeFibration.coneC1_eq (hn : 3 ≤ n) (hA : AdelicConeFibration hQ hQ' A)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) {s : ℝ} (hs : 0 < s) :
    coneC1 Q₀ hQ Φ D DM s =
      covolSO Q' hQ' * (A.coneInt Φ * ENNReal.ofReal (dedekindZeta_residue F / (2 + 2 * s))) := by
  rw [coneC1, lintegral_congr fun g => coneLo_eq_tsum Q₀ hΦ DM s g,
    hA.lintegral_unfold hn hD (measurable_coneLoFn hΦ DM s), hA.lintegral_coneLoFn hΦ hDM hs]

/-- **The dual cone term $C_2(s)$ in closed form**: for $n\ge3$ and $s > 0$,
$$C_2(s) = \operatorname{covol}(SO(Q'))\cdot I_C(\hat\Phi)\cdot\frac{\rho_F}{n-2+2s}.$$ -/
@[kb "weil1982" "§4.5, p. 108 (the dual cone term: covol(P')·I_C(Φ̂)·ρ_k/(m−2+2s)) [unverified page]"]
theorem AdelicConeFibration.coneC2_eq (hn : 3 ≤ n) (hA : AdelicConeFibration hQ hQ' A)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    {Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦh : Measurable Φh) {s : ℝ} (hs : 0 < s) :
    coneC2 Q₀ hQ Φh D DM s =
      covolSO Q' hQ' * (A.coneInt Φh * ENNReal.ofReal (dedekindZeta_residue F / ((n : ℝ) - 2 + 2 * s))) := by
  rw [coneC2, lintegral_congr fun g => coneRem_eq_tsum Q₀ hΦh DM s g,
    hA.lintegral_unfold hn hD (measurable_coneRemFn hΦh DM s), hA.lintegral_coneRemFn hn hΦh hDM hs]

/-- The bound on $C_1$ used in Step 4: $C_1(s)\le\operatorname{covol}(SO(Q'))\,I_C(\Phi)\,\rho_F/2$ for $s > 0$. -/
theorem AdelicConeFibration.coneC1_le (hn : 3 ≤ n) (hA : AdelicConeFibration hQ hQ' A)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) {s : ℝ} (hs : 0 < s) :
    coneC1 Q₀ hQ Φ D DM s ≤ covolSO Q' hQ' * (A.coneInt Φ * ENNReal.ofReal (dedekindZeta_residue F / 2)) := by
  rw [hA.coneC1_eq hn hD hDM hΦ hs]
  have := dedekindZeta_residue_pos F
  gcongr <;> linarith

/-- The bound on $C_2$ used in Step 4: $C_2(s)\le\operatorname{covol}(SO(Q'))\,I_C(\hat\Phi)\,\rho_F/(n-2)$ for
$s > 0$, $n\ge3$. -/
theorem AdelicConeFibration.coneC2_le (hn : 3 ≤ n) (hA : AdelicConeFibration hQ hQ' A)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    {Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦh : Measurable Φh) {s : ℝ} (hs : 0 < s) :
    coneC2 Q₀ hQ Φh D DM s ≤
      covolSO Q' hQ' * (A.coneInt Φh * ENNReal.ofReal (dedekindZeta_residue F / ((n : ℝ) - 2))) := by
  rw [hA.coneC2_eq hn hD hDM hΦh hs]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have := dedekindZeta_residue_pos F
  gcongr <;> linarith

end QuadFormsKB.Tamagawa.Measure.Weil
