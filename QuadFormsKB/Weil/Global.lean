/-
# The theta distribution and its $\mathrm{SL}_2(F)$-invariance

**Layer:** global, over a number field $F$; the inputs are the local results of `Weil/NonArch.lean`, adelic Poisson
summation in one variable (`adelicPoisson_factorizable`), Weil's product formula $\prod_v\gamma_v(t) = 1$
(`weilInf_mul_finprod_weilV`), Hilbert reciprocity and $|t|_{\mathbb A} = 1$ (`Weil/ProductFormulas.lean`).

**Setting.** $V = F^{2m}$ with $Q(x) = \sum_{i<2m}a_ix_i^2$, $a_i \in F^\times$ (every nondegenerate quadratic space over
$F$ has an orthogonal basis; 0-based indices). The archimedean component is the block
$F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$ (`localDataInf`: $\psi_\infty = e\circ\operatorname{Tr}_\infty$, the self-dual
measure, $|t|_\infty = \prod_{w\ \mathrm{real}}|t_w|\prod_{w\ \mathrm{complex}}|t_w|^2$, $\gamma_\infty$ = `weilInf`,
$(s,t)_\infty = \prod_{w\ \mathrm{real}}(s_w,t_w)_{\mathbb R}$, Schwartz functions). A **global datum** (`GDatum`) is a family
$\Phi = (\Phi_\infty, (\Phi_v)_v)$ of functions on $V_\infty = F_\infty^{2m}$ and $V_v = F_v^{2m}$; it stands for the
factorizable function $\Phi_\infty\otimes\bigotimes_v\Phi_v$ on $V(\mathbb A)$, and
$$\Theta(\Phi) = \sum_{\xi\in V(F)}\Phi_\infty(\xi)\prod_v\Phi_v(\xi)\qquad(\texttt{thetaDist}).$$

**The action of $\mathrm{SL}_2(F)$** (`omegaG`): componentwise, by the Bruhat-cell formula (`cellRep`) in the local
operators $\omega_u(n(b))$, $\omega_u(m(t))$, $\omega_u(w)$ of `Weil/Model.lean` at every place $u$. At each finite place
this is the local representation `weilRepV` (`omegaG_fin_eq_weilRepV`).

**Main theorem** (`thetaDist_omegaG`): for $\gamma \in \mathrm{SL}_2(F)$ and every *fully factorizable* datum $\Phi$
(`IsPure`: $\Phi_u = c_u\bigotimes_if_{u,i}$ with $f_{\infty,i}$ Schwartz, $f_{v,i}$ locally constant with compact
support, $c_v = 1$, $f_{v,i} = \mathbf 1_{\mathcal O_v}$ for almost all $v$),
$$\Theta(\omega(\gamma)\Phi) = \Theta(\Phi).$$
*Proof.* On the generators: $n(b)$ by $\psi_\infty\prod_v\psi_v = 1$ on $F$ (`thetaDist_gN`); $m(t)$ by Hilbert reciprocity
$\prod_u(t, (-1)^m\det V)_u = 1$ and $|t|_{\mathbb A} = 1$ (`thetaDist_gM`); $w$ by Poisson summation in each coordinate and
**the product formula for the Weil index** $\prod_u\gamma_{V,u} = 1$ (`prod_gammaV_eq_one`, `thetaDist_gW`); then the
Bruhat cells. Only $n(b)$ and $m(t)$ need no purity; $w$ needs the coordinate factorization, which $n(b)$ preserves.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.ProductFormulas
import QuadFormsKB.Analysis.AdelicPoisson
import QuadFormsKB.Analysis.WeilIndexInf

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Metric MeasureTheory
open QuadFormsKB.Analysis
open scoped MatrixGroups Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

variable {F : Type} [Field F] [NumberField F]

local notation "V∞" => mixedSpace F

/-! ### The archimedean component $F_\infty$ -/

/-- The standard character $\psi_\infty = e\circ\operatorname{Tr}_\infty$ of $F_\infty$ as an additive character. -/
def psiInfChar : AddChar (mixedSpace F) Circle where
  toFun := psiInf
  map_zero_eq_one' := by simp [psiInf, traceInf]
  map_add_eq_mul' x y := by simp only [psiInf, traceInf_add, AddChar.map_add_eq_mul]

@[simp] lemma psiInfChar_apply (x : mixedSpace F) : psiInfChar x = psiInf x := rfl

/-- The Schwartz functions on $F_\infty$, as a space of functions. -/
def schwartzInf : Submodule ℂ (mixedSpace F → ℂ) where
  carrier := {f | ∃ g : SchwartzMap (mixedSpace F) ℂ, (g : mixedSpace F → ℂ) = f}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩; exact ⟨g + h, rfl⟩
  smul_mem' := by rintro c _ ⟨g, rfl⟩; exact ⟨c • g, rfl⟩

/-- $2$ as a unit of $F_\infty$. -/
def twoInf : (mixedSpace F)ˣ := Units.map (mixedEmbedding F).toMonoidHom (Units.mk0 2 two_ne_zero)

lemma twoInf_val : ((twoInf : (mixedSpace F)ˣ) : mixedSpace F) = 2 := by
  show mixedEmbedding F 2 = 2; exact map_ofNat _ 2

/-- **The archimedean local data:** $\psi_\infty$, the self-dual measure `selfDualInf`, the modulus
$|t|_\infty$ = `mixedEmbedding.norm`, the Weil constant $\gamma_\infty$ = `weilInf`, the Hilbert symbol `hilbInf` and the
Schwartz functions. -/
@[kb "weil1964" "§14, §26 (the archimedean places) [unverified]"]
def localDataInf : LocalData (mixedSpace F) where
  ψ := psiInfChar
  μ := selfDualInf
  md := fun x => mixedEmbedding.norm x
  γ := weilInf
  hilb := hilbInf
  S := schwartzInf
  two := twoInf
  two_eq := twoInf_val

lemma localDataInf_four (f : mixedSpace F → ℂ) : (localDataInf (F := F)).four f = fourierInf f := rfl

instance : SigmaFinite (localDataInf (F := F)).μ := by
  show SigmaFinite selfDualInf; unfold selfDualInf; infer_instance

/-! ### Global data and the theta distribution -/

variable (F) in
/-- **A global datum** of dimension $n$: functions $\Phi_\infty$ on $F_\infty^n$ and $\Phi_v$ on $F_v^n$, standing for the
factorizable function $\Phi_\infty\otimes\bigotimes_v\Phi_v$ on $\mathbb A_F^n$. -/
structure GDatum (n : ℕ) where
  inf : (Fin n → mixedSpace F) → ℂ
  fin : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → v.adicCompletion F) → ℂ

/-- $\xi \in F^n$ in $F_\infty^n$. -/
def ιInf {n : ℕ} (ξ : Fin n → F) : Fin n → mixedSpace F := fun i => mixedEmbedding F (ξ i)

/-- $\xi \in F^n$ in $F_v^n$. -/
def ιV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (ξ : Fin n → F) : Fin n → v.adicCompletion F :=
  fun i => algebraMap F (v.adicCompletion F) (ξ i)

/-- The value $\Phi(\xi) = \Phi_\infty(\xi)\prod_v\Phi_v(\xi)$ at a rational point $\xi \in F^n$. -/
def GDatum.eval {n : ℕ} (Φ : GDatum F n) (ξ : Fin n → F) : ℂ :=
  Φ.inf (ιInf ξ) * ∏ᶠ v, Φ.fin v (ιV v ξ)

/-- **The theta distribution** $\Theta(\Phi) = \sum_{\xi\in F^n}\Phi(\xi)$. -/
@[kb "weil1964" "§29–§30 (the distribution $\\sum_{\\xi\\in X_k}\\Phi(\\xi)$) [unverified]"]
def thetaDist {n : ℕ} (Φ : GDatum F n) : ℂ := ∑' ξ : Fin n → F, Φ.eval ξ

/-! ### The coefficients at each place -/

variable {m : ℕ} (a : Fin (2 * m) → Fˣ)

/-- The coefficients $a_i$ in $F_\infty$. -/
def aInf : Fin (2 * m) → (mixedSpace F)ˣ := fun i => Units.map (mixedEmbedding F).toMonoidHom (a i)

/-- The coefficients $a_i$ in $F_v$. -/
def aV (v : HeightOneSpectrum (𝓞 F)) : Fin (2 * m) → (v.adicCompletion F)ˣ :=
  fun i => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom (a i)

lemma aV_val (v : HeightOneSpectrum (𝓞 F)) (i : Fin (2 * m)) :
    ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) = algebraMap F _ (a i : F) := rfl

lemma aInf_val (i : Fin (2 * m)) : ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F) = mixedEmbedding F (a i : F) :=
  rfl

/-- **The global action of $n(b)$**, $b \in F$: $\omega_u(n(b))$ at every place. -/
def gN (b : F) : Function.End (GDatum F (2 * m)) := fun Φ =>
  ⟨(localDataInf (F := F)).opNf (aInf a) (mixedEmbedding F b) Φ.inf,
    fun v => (localDataV v).opNf (aV a v) (algebraMap F _ b) (Φ.fin v)⟩

/-- **The global action of $m(t)$**, $t \in F^\times$. -/
def gM (t : Fˣ) : Function.End (GDatum F (2 * m)) := fun Φ =>
  ⟨(localDataInf (F := F)).opMf (aInf a) (mixedEmbedding F t) Φ.inf,
    fun v => (localDataV v).opMf (aV a v) (algebraMap F _ t) (Φ.fin v)⟩

/-- **The global action of $w$.** -/
def gW : Function.End (GDatum F (2 * m)) := fun Φ =>
  ⟨(localDataInf (F := F)).opWf (aInf a) Φ.inf, fun v => (localDataV v).opWf (aV a v) (Φ.fin v)⟩

/-- **The action of $\gamma \in \mathrm{SL}_2(F)$ on global data**, by the Bruhat-cell formula in the global generator
actions (`cellRep`): $\omega(\gamma) = \omega(m(a))\omega(n(b/a))$ ($c = 0$),
$\omega(n(a/c))\omega(m(-c^{-1}))\omega(w)\omega(n(d/c))$ ($c \ne 0$). -/
@[kb "weil1964" "§14, §29 (the action of $\\mathrm{Sp}(X_k)$ on $\\mathcal S(X_{\\mathbb A})$) [unverified]"]
def omegaG (γ : SL(2, F)) : Function.End (GDatum F (2 * m)) := cellRep (gN a) (gM a) (gW a) γ

/-! ### Elementary facts about the embeddings -/

lemma Qform_ιInf (ξ : Fin (2 * m) → F) :
    Qform (aInf a) (ιInf ξ) = mixedEmbedding F (Qform a ξ) := by
  simp [Qform, ιInf, aInf, map_sum, map_mul, map_pow]

lemma Qform_ιV (v : HeightOneSpectrum (𝓞 F)) (ξ : Fin (2 * m) → F) :
    Qform (aV a v) (ιV v ξ) = algebraMap F (v.adicCompletion F) (Qform a ξ) := by
  simp [Qform, ιV, aV, map_sum, map_mul, map_pow]

lemma discV_aInf : ((discV (aInf a) : (mixedSpace F)ˣ) : mixedSpace F) =
    mixedEmbedding F ((discV a : Fˣ) : F) := by
  simp [discV, aInf, map_prod]

lemma discV_aV (v : HeightOneSpectrum (𝓞 F)) : ((discV (aV a v)) : v.adicCompletion F) =
    algebraMap F (v.adicCompletion F) ((discV a : Fˣ) : F) := by
  simp [discV, aV, map_prod]

/-- The standard indicator $\mathbf 1_{\mathcal O_v^n} = \bigotimes_i\mathbf 1_{\mathcal O_v}$. -/
def oneV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : (Fin n → v.adicCompletion F) → ℂ :=
  ptensor fun _ => ballIndV v 0 0

lemma ballIndV_algebraMap_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 F) x) : ballIndV v 0 0 (algebraMap F (v.adicCompletion F) x) = 1 := by
  rw [ballIndV, Set.indicator_of_mem]
  simpa using valued_le_one_of_not_mem_support hv

/-- The finite places where some coordinate of $\xi$ is not integral. -/
def badSet {n : ℕ} (ξ : Fin n → F) : Set (HeightOneSpectrum (𝓞 F)) :=
  ⋃ i, (HeightOneSpectrum.Support (𝓞 F) (ξ i) : Set (HeightOneSpectrum (𝓞 F)))

lemma badSet_finite {n : ℕ} (ξ : Fin n → F) : (badSet ξ).Finite :=
  Set.finite_iUnion fun i => HeightOneSpectrum.Support.finite (𝓞 F) (ξ i)

lemma oneV_eval_eq_one {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {ξ : Fin n → F} (hv : v ∉ badSet ξ) :
    oneV v n (ιV v ξ) = 1 := by
  unfold oneV ptensor
  refine Finset.prod_eq_one fun i _ => ?_
  exact ballIndV_algebraMap_eq_one fun h => hv (Set.mem_iUnion.mpr ⟨i, h⟩)

/-- **Admissible data:** $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ for all but finitely many $v$. -/
def GDatum.Adm {n : ℕ} (Φ : GDatum F n) : Prop := ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ T, Φ.fin v = oneV v n

lemma GDatum.Adm.finite_mulSupport {n : ℕ} {Φ : GDatum F n} (hΦ : Φ.Adm) (ξ : Fin n → F) :
    Function.HasFiniteMulSupport fun v => Φ.fin v (ιV v ξ) := by
  obtain ⟨T, hT⟩ := hΦ
  refine ((T.finite_toSet).union (badSet_finite ξ)).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, not_or] at h
  exact hv (by show Φ.fin v (ιV v ξ) = 1; rw [hT v h.1, oneV_eval_eq_one h.2])

/-! ### Invariance under $n(b)$ -/

lemma ψInf_eq (x : mixedSpace F) : (localDataInf (F := F)).ψ x = psiInf x := rfl
lemma ψV_eq (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : (localDataV v).ψ x = psiV v x := rfl

lemma eval_gN {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) (b : F) (ξ : Fin (2 * m) → F) :
    (gN a b Φ).eval ξ = Φ.eval ξ := by
  simp only [GDatum.eval, gN, LocalData.opNf, Qform_ιInf, Qform_ιV, ψInf_eq, ψV_eq, ← map_mul]
  rw [finprod_mul_distrib (hasFiniteMulSupport_psiV_coe _) (hΦ.finite_mulSupport ξ)]
  have h := psiInf_mul_finprod_psiV (b * Qform a ξ)
  rw [show ∀ x y z w : ℂ, x * y * (z * w) = (x * z) * (y * w) by intros; ring, h, one_mul]

/-- **$\Theta$ is invariant under $\omega(n(b))$**, $b \in F$: $\psi(bQ(\xi)) = 1$ for $\xi \in V(F)$. -/
@[kb "weil1964" "§29 ($\\psi$ is trivial on $F$) [unverified]"]
theorem thetaDist_gN {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) (b : F) : thetaDist (gN a b Φ) = thetaDist Φ :=
  tsum_congr fun ξ => eval_gN a hΦ b ξ

/-! ### Invariance under $m(t)$ -/

/-- Multiplication by a unit of $F$ on $F^n$. -/
def mulEquiv {K : Type*} [Field K] {n : ℕ} (t : Kˣ) : (Fin n → K) ≃ (Fin n → K) where
  toFun ξ i := t * ξ i
  invFun ξ i := ↑t⁻¹ * ξ i
  left_inv ξ := by ext i; simp [← mul_assoc]
  right_inv ξ := by ext i; simp [← mul_assoc]

lemma chiV_prod_eq_one (t : Fˣ) :
    (localDataInf (F := F)).chiV (aInf a) (mixedEmbedding F t) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).chiV (aV a v) (algebraMap F _ t) = 1 := by
  simp only [LocalData.chiV, LocalData.hC, discV_aInf, discV_aV]
  exact prod_hilbert_eq_one t.ne_zero (discV a).ne_zero

lemma md_prod_eq_one (t : Fˣ) :
    ((localDataInf (F := F)).md (mixedEmbedding F t) : ℂ) ^ m *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m = 1 := by
  have hfin := hasFiniteMulSupport_modK (t := (t : F)) t.ne_zero
  have h := prod_modulus_eq_one (t := (t : F)) t.ne_zero
  have hfinC : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t) : ℝ) : ℂ) :=
    hfin.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hmap := MonoidHom.map_finprod (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom hfin
  calc ((localDataInf (F := F)).md (mixedEmbedding F t) : ℂ) ^ m *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m
      = (((mixedEmbedding.norm (mixedEmbedding F t) : ℝ) : ℂ) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Analysis.Weil.modK (v.adicCompletion F)
            (algebraMap F (v.adicCompletion F) t) : ℝ) : ℂ)) ^ m := by
        rw [mul_pow, finprod_pow hfinC]; rfl
    _ = 1 := by
        have : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Analysis.Weil.modK (v.adicCompletion F)
            (algebraMap F (v.adicCompletion F) t) : ℝ) : ℂ)) = ((∏ᶠ v : HeightOneSpectrum (𝓞 F),
            Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t) : ℝ) : ℂ) :=
          hmap.symm
        rw [this, ← Complex.ofReal_mul, h]; simp

lemma hasFiniteMulSupport_chiV (t : Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).chiV (aV a v) (algebraMap F _ t) := by
  refine (HN.finite_hilbert_finite_eq_neg_one (t : F) ((discV a : Fˣ) : F) t.ne_zero (discV a).ne_zero).subset
    fun v hv => ?_
  simp only [Function.mem_mulSupport, LocalData.chiV, LocalData.hC, discV_aV] at hv
  rcases HN.hilbertSymbol_eq_one_or (v.adicCompletion F) (algebraMap F _ t) (algebraMap F _ ((discV a : Fˣ) : F))
    with h | h
  · exact absurd (by rw [show (localDataV v).hilb = hilbertSymbol (v.adicCompletion F) from rfl, h]; simp) hv
  · exact h

lemma hasFiniteMulSupport_mdV_pow (t : Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m :=
  (hasFiniteMulSupport_modK (t := (t : F)) t.ne_zero).subset fun v hv h' => hv (by
    simp only at h'
    show ((Analysis.Weil.modK (v.adicCompletion F) (algebraMap F _ (t : F)) : ℝ) : ℂ) ^ m = 1
    rw [h']; simp)

lemma eval_gM {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) (t : Fˣ) (ξ : Fin (2 * m) → F) :
    (gM a t Φ).eval ξ = Φ.eval (mulEquiv t ξ) := by
  have hι : (fun i => mixedEmbedding F (t : F) * ιInf ξ i) = ιInf (mulEquiv t ξ) := by
    ext i <;> simp [ιInf, mulEquiv]
  have hιv : ∀ v, (fun i => algebraMap F (v.adicCompletion F) (t : F) * ιV v ξ i) = ιV v (mulEquiv t ξ) := by
    intro v; ext i; simp [ιV, mulEquiv]
  simp only [GDatum.eval, gM, LocalData.opMf, hι, hιv]
  have hcm : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).chiV (aV a v) (algebraMap F _ t) * ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m :=
    (hasFiniteMulSupport_chiV a t).mul (hasFiniteMulSupport_mdV_pow t)
  rw [finprod_mul_distrib hcm (hΦ.finite_mulSupport _), finprod_mul_distrib (hasFiniteMulSupport_chiV a t)
    (hasFiniteMulSupport_mdV_pow t)]
  have h1 := chiV_prod_eq_one a t
  have h2 := md_prod_eq_one (m := m) (F := F) t
  set A := (localDataInf (F := F)).chiV (aInf a) (mixedEmbedding F t)
  set B := ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).chiV (aV a v) (algebraMap F _ t)
  set C := ((localDataInf (F := F)).md (mixedEmbedding F t) : ℂ) ^ m
  set E := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m
  calc A * C * Φ.inf (ιInf (mulEquiv t ξ)) * (B * E * ∏ᶠ v, Φ.fin v (ιV v (mulEquiv t ξ)))
      = (A * B) * (C * E) * (Φ.inf (ιInf (mulEquiv t ξ)) * ∏ᶠ v, Φ.fin v (ιV v (mulEquiv t ξ))) := by ring
    _ = _ := by rw [h1, h2, one_mul, one_mul]

/-- **$\Theta$ is invariant under $\omega(m(t))$**, $t \in F^\times$: by Hilbert reciprocity
$\prod_u\chi_{V,u}(t) = 1$, the product formula $\prod_u|t|_u = 1$, and $\xi \mapsto t\xi$ on $V(F)$. -/
@[kb "weil1964" "§29 (Hilbert reciprocity and $|t|_{\\mathbb A} = 1$) [unverified]"]
theorem thetaDist_gM {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) (t : Fˣ) : thetaDist (gM a t Φ) = thetaDist Φ := by
  rw [thetaDist, tsum_congr fun ξ => eval_gM a hΦ t ξ]
  exact (mulEquiv t).tsum_eq fun ξ => Φ.eval ξ

/-! ### Admissibility is preserved -/

lemma valued_eq_one_of_not_mem {v : HeightOneSpectrum (𝓞 F)} {x : F} (hx : x ≠ 0)
    (h1 : v ∉ HeightOneSpectrum.Support (𝓞 F) x) (h2 : v ∉ HeightOneSpectrum.Support (𝓞 F) x⁻¹) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  have a1 := valued_le_one_of_not_mem_support h1
  have a2 := valued_le_one_of_not_mem_support h2
  rw [map_inv₀, map_inv₀] at a2
  have hv0 : Valued.v (algebraMap F (v.adicCompletion F) x) ≠ 0 := by simpa using hx
  exact le_antisymm a1 ((inv_le_one₀ (pos_iff_ne_zero.mpr hv0)).mp a2)

lemma norm_eq_one_of_valued {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (h : Valued.v x = 1) :
    ‖x‖ = 1 := by
  rw [FinitePlace.norm_def, h, map_one]; rfl

lemma chirp_ballIndV {v : HeightOneSpectrum (𝓞 F)} {s : v.adicCompletion F} (hs : Valued.v s ≤ 1) :
    (localDataV v).chirp s (ballIndV v 0 0) = ballIndV v 0 0 := by
  funext x
  rw [LocalData.chirp, mul_comm]
  exact congrFun (ballIndV_mul_chirp_eq hs) x

lemma dil_ballIndV {v : HeightOneSpectrum (𝓞 F)} {s : v.adicCompletion F} (hs : Valued.v s = 1) :
    dil s (ballIndV v 0 0) = ballIndV v 0 0 := by
  funext x
  simp only [dil, ballIndV, sub_zero, Set.indicator, Set.mem_setOf_eq, map_mul, hs, one_mul]

lemma fourierV_ballIndV_zero {v : HeightOneSpectrum (𝓞 F)} (hd : diffExp v = 0) :
    fourierV v (ballIndV v 0 0) = ballIndV v 0 0 := by
  rw [fourierV_ballIndV_eq, selfDualV_real_Ov_of_diffExp v hd, hd]
  funext y; simp

lemma Fa_ballIndV {v : HeightOneSpectrum (𝓞 F)} (hd : diffExp v = 0) {α : v.adicCompletion F}
    (hα : Valued.v (2 * α) = 1) : (localDataV v).Fa α (ballIndV v 0 0) = ballIndV v 0 0 := by
  unfold LocalData.Fa
  rw [localDataV_four, fourierV_ballIndV_zero hd, dil_ballIndV hα]
  have : (localDataV v).md (2 * α) = 1 := by
    show Analysis.Weil.modK _ _ = 1
    rw [modK_eq_norm v (by intro h; rw [h] at hα; simp at hα), norm_eq_one_of_valued hα]
  rw [this, Real.sqrt_one, Complex.ofReal_one, one_smul]

lemma GDatum.Adm.gN {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) (b : F) : (gN a b Φ).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  have hfin : (⋃ i, (HeightOneSpectrum.Support (𝓞 F) (b * a i) : Set (HeightOneSpectrum (𝓞 F)))).Finite :=
    Set.finite_iUnion fun i => HeightOneSpectrum.Support.finite (𝓞 F) _
  refine ⟨T ∪ hfin.toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_iUnion, not_or, not_exists] at hv
  show (localDataV v).opNf (aV a v) (algebraMap F _ b) (Φ.fin v) = oneV v (2 * m)
  rw [hT v hv.1, oneV, opNf_ptensor]
  congr 1; funext i
  refine chirp_ballIndV ?_
  have := valued_le_one_of_not_mem_support (hv.2 i)
  simpa [aV, map_mul] using this

lemma GDatum.Adm.gM {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) (t : Fˣ) : (gM a t Φ).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  set S := (HeightOneSpectrum.Support.finite (𝓞 F) (t : F)).union
    ((HeightOneSpectrum.Support.finite (𝓞 F) (t : F)⁻¹).union
      (HN.finite_hilbert_finite_eq_neg_one (t : F) ((discV a : Fˣ) : F) t.ne_zero (discV a).ne_zero))
  refine ⟨T ∪ S.toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
  obtain ⟨hvT, hv1, hv2, hv3⟩ := hv
  have hval := valued_eq_one_of_not_mem t.ne_zero hv1 hv2
  show (localDataV v).opMf (aV a v) (algebraMap F _ t) (Φ.fin v) = oneV v (2 * m)
  rw [hT v hvT, oneV, opMf_ptensor]
  have hχ : (localDataV v).chiV (aV a v) (algebraMap F _ t) = 1 := by
    simp only [LocalData.chiV, LocalData.hC, discV_aV]
    rcases HN.hilbertSymbol_eq_one_or (v.adicCompletion F) (algebraMap F _ t)
      (algebraMap F _ ((discV a : Fˣ) : F)) with h | h
    · rw [show (localDataV v).hilb = hilbertSymbol (v.adicCompletion F) from rfl, h]; simp
    · exact absurd h hv3
  have hmd : (localDataV v).md (algebraMap F _ t) = 1 := by
    show Analysis.Weil.modK _ _ = 1
    rw [modK_eq_norm v ((map_ne_zero _).mpr t.ne_zero), norm_eq_one_of_valued hval]
  rw [hχ, hmd]
  simp only [Complex.ofReal_one, one_pow, mul_one, one_smul]
  congr 1; funext i
  exact dil_ballIndV hval

lemma valued_two_eq_one {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ HeightOneSpectrum.Support (𝓞 F) (2 : F)⁻¹) :
    Valued.v (2 : v.adicCompletion F) = 1 := by
  have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
    rw [show (2 : v.adicCompletion F) = algebraMap F _ 2 from (map_ofNat _ 2).symm]
    exact valued_le_one_of_not_mem_support (v := v) (x := (2 : F)) (by
      simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt]
      exact_mod_cast v.valuation_le_one (K := F) ((2 : ℕ) : 𝓞 F))
  have := valued_le_one_of_not_mem_support h
  rw [map_inv₀, map_inv₀, show algebraMap F (v.adicCompletion F) 2 = 2 from map_ofNat _ 2] at this
  have hv0 : Valued.v (2 : v.adicCompletion F) ≠ 0 := by simp
  exact le_antisymm h2le ((inv_le_one₀ (pos_iff_ne_zero.mpr hv0)).mp this)

/-- The finite places where some $\omega_v(w)$ does not fix $\mathbf 1_{\mathcal O_v^n}$: $d_v \ne 0$, $v \mid 2$, some $a_i$
not a unit, or $(-1, (-1)^m\det V)_v = -1$. -/
def badW : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | (diffExp v : ℤ) ≠ 0} ∪ (HeightOneSpectrum.Support (𝓞 F) (2 : F)⁻¹ ∪
    ((⋃ i, (HeightOneSpectrum.Support (𝓞 F) (a i : F) ∪ HeightOneSpectrum.Support (𝓞 F) (a i : F)⁻¹)) ∪
      {v | (NFPlace.finite v).hilbert (-1) ((discV a : Fˣ) : F) = -1}))

lemma badW_finite : (badW a).Finite := by
  refine (finite_support_diffExp.subset fun v hv => ?_).union
    ((HeightOneSpectrum.Support.finite (𝓞 F) _).union ((Set.finite_iUnion fun i =>
      (HeightOneSpectrum.Support.finite (𝓞 F) _).union (HeightOneSpectrum.Support.finite (𝓞 F) _)).union
      (HN.finite_hilbert_finite_eq_neg_one (-1) _ (by norm_num) (discV a).ne_zero)))
  simpa using hv

lemma gammaV_eq_one {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badW a) : (localDataV v).gammaV (aV a v) = 1 := by
  simp only [badW, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hv
  obtain ⟨hd, h2, hai, hχ⟩ := hv
  have hd' : diffExp v = 0 := by exact_mod_cast hd
  have h2' := valued_two_eq_one h2
  have hχ' : (localDataV v).chiV (aV a v) (-1) = 1 := by
    simp only [LocalData.chiV, LocalData.hC, discV_aV]
    rcases HN.hilbertSymbol_eq_one_or (v.adicCompletion F) (-1) (algebraMap F _ ((discV a : Fˣ) : F))
      with h | h
    · rw [show (localDataV v).hilb = hilbertSymbol (v.adicCompletion F) from rfl, h]; simp
    · exact absurd (by rw [NFPlace.hilbert, map_neg, map_one]; exact h) hχ
  have hg : ∀ i, (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    intro i
    have hval := valued_eq_one_of_not_mem (a i).ne_zero (hai i).1 (hai i).2
    unfold LocalData.gN
    have hγ : (localDataV v).γ (algebraMap F _ (a i : F)) = 1 := weilV_eq_one v hd' h2' hval
    have hmd : (localDataV v).md (2 * algebraMap F _ (a i : F)) = 1 := by
      show Analysis.Weil.modK _ _ = 1
      have h2a : Valued.v (2 * algebraMap F (v.adicCompletion F) (a i : F)) = 1 := by rw [map_mul, h2', hval, one_mul]
      rw [modK_eq_norm v (by intro h; rw [h] at h2a; simp at h2a), norm_eq_one_of_valued h2a]
    rw [aV_val, hγ, hmd, Real.sqrt_one, Complex.ofReal_one, one_mul]
  rw [LocalData.gammaV, hχ', Finset.prod_eq_one fun i _ => hg i, inv_one, one_mul]

lemma GDatum.Adm.gW {Φ : GDatum F (2 * m)} (hΦ : Φ.Adm) : (gW a Φ).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  refine ⟨T ∪ (badW_finite a).toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
  have hv2 := hv.2
  simp only [badW, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hv2
  obtain ⟨hd, h2, hai, -⟩ := hv2
  show (localDataV v).opWf (aV a v) (Φ.fin v) = oneV v (2 * m)
  rw [hT v hv.1, oneV, opWf_ptensor (isOps_V v), gammaV_eq_one a hv.2, one_smul]
  congr 1; funext i
  refine Fa_ballIndV (by exact_mod_cast hd) ?_
  rw [map_mul, valued_two_eq_one h2]
  simpa [aV] using valued_eq_one_of_not_mem (a i).ne_zero (hai i).1 (hai i).2

/-! ### Sums over $F^n$ of pure tensors -/

/-- $\sum_{\xi\in\iota^n}\prod_iE_i(\xi_i) = \prod_i\sum_xE_i(x)$ for absolutely summable $E_i$. -/
theorem tsum_fin_prod {ι : Type*} : ∀ (n : ℕ) (E : Fin n → ι → ℂ), (∀ i, Summable fun x => ‖E i x‖) →
    (Summable fun ξ : Fin n → ι => ‖∏ i, E i (ξ i)‖) ∧ ∑' ξ : Fin n → ι, ∏ i, E i (ξ i) = ∏ i, ∑' x, E i x
  | 0, E, _ => by
    refine ⟨Summable.of_finite, ?_⟩
    simp
  | n + 1, E, hE => by
    obtain ⟨hs, ht⟩ := tsum_fin_prod n (fun i => E i.succ) (fun i => hE i.succ)
    set e := Fin.consEquiv (fun _ : Fin (n + 1) => ι)
    have hcomp : ∀ z : ι × (Fin n → ι), ∏ i, E i (e z i) = E 0 z.1 * ∏ i : Fin n, E i.succ (z.2 i) := by
      intro z; rw [Fin.prod_univ_succ]; rfl
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      have := (hE 0).mul_norm hs
      refine this.congr fun z => ?_
      simp only [Function.comp, hcomp, norm_mul]
    · rw [← e.tsum_eq]
      simp only [hcomp]
      rw [← tsum_mul_tsum_of_summable_norm (hE 0) hs, ht, Fin.prod_univ_succ]

/-! ### Fully factorizable data -/

/-- The datum $\big(c_0\bigotimes_if_{0,i},\ (c_v\bigotimes_if_{v,i})_v\big)$. -/
def pureD {n : ℕ} (c₀ : ℂ) (f₀ : Fin n → mixedSpace F → ℂ) (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (f : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F → ℂ) : GDatum F n :=
  ⟨c₀ • ptensor f₀, fun v => c v • ptensor (f v)⟩

section PureForm

variable {n : ℕ} {c₀ : ℂ} {f₀ : Fin n → mixedSpace F → ℂ} {c : HeightOneSpectrum (𝓞 F) → ℂ}
  {f : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F → ℂ} {T : Finset (HeightOneSpectrum (𝓞 F))}

lemma hasFiniteMulSupport_coord (hT : ∀ v ∉ T, c v = 1 ∧ ∀ i, f v i = ballIndV v 0 0) (i : Fin n) (x : F) :
    Function.HasFiniteMulSupport fun v => f v i (algebraMap F (v.adicCompletion F) x) := by
  refine (T.finite_toSet.union (HeightOneSpectrum.Support.finite (𝓞 F) x)).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, not_or] at h
  exact hv (by show f v i _ = 1; rw [(hT v h.1).2 i, ballIndV_algebraMap_eq_one h.2])

lemma hasFiniteMulSupport_const (hT : ∀ v ∉ T, c v = 1 ∧ ∀ i, f v i = ballIndV v 0 0) :
    Function.HasFiniteMulSupport c :=
  T.finite_toSet.subset fun v hv => by
    by_contra h; exact hv (hT v h).1

/-- **Expansion of a fully factorizable datum** at a rational point:
$\Phi(\xi) = \big(c_0\prod_vc_v\big)\prod_i\big(f_{0,i}(\xi_i)\prod_vf_{v,i}(\xi_i)\big)$. -/
lemma eval_pureD (hT : ∀ v ∉ T, c v = 1 ∧ ∀ i, f v i = ballIndV v 0 0) (ξ : Fin n → F) :
    (pureD c₀ f₀ c f).eval ξ = (c₀ * ∏ᶠ v, c v) *
      ∏ i, (f₀ i (mixedEmbedding F (ξ i)) * ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) (ξ i))) := by
  simp only [GDatum.eval, pureD, Pi.smul_apply, smul_eq_mul, ptensor, ιInf, ιV]
  have hprod : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ∏ i, f v i (algebraMap F (v.adicCompletion F) (ξ i)) := by
    exact Function.HasFiniteMulSupport.prod (fun i => hasFiniteMulSupport_coord hT i (ξ i)) Finset.univ
  rw [finprod_mul_distrib (hasFiniteMulSupport_const hT) hprod,
    finprod_prod_comm Finset.univ _ fun i _ => hasFiniteMulSupport_coord hT i (ξ i),
    Finset.prod_mul_distrib]
  ring

/-- **$\Theta$ of a fully factorizable datum** is $\big(c_0\prod_vc_v\big)\prod_i\Theta_1(f_i)$. -/
lemma thetaDist_pureD (hT : ∀ v ∉ T, c v = 1 ∧ ∀ i, f v i = ballIndV v 0 0)
    (hsum : ∀ i, Summable fun x : F =>
      f₀ i (mixedEmbedding F x) * ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) x)) :
    thetaDist (pureD c₀ f₀ c f) = (c₀ * ∏ᶠ v, c v) *
      ∏ i, ∑' x : F, f₀ i (mixedEmbedding F x) * ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) x) := by
  rw [thetaDist, tsum_congr fun ξ => eval_pureD hT ξ, tsum_mul_left]
  congr 1
  exact (tsum_fin_prod n _ fun i => summable_norm_iff.mpr (hsum i)).2

end PureForm

/-- **Fully factorizable data** (`IsPure`): $\Phi = (c_0\bigotimes_if_{0,i}, (c_v\bigotimes_if_{v,i})_v)$ with $f_{0,i}$
Schwartz on $F_\infty$, $f_{v,i}$ locally constant with compact support, and $c_v = 1$, $f_{v,i} = \mathbf 1_{\mathcal O_v}$
for $v \notin T$, a finite set. -/
def GDatum.IsPure {n : ℕ} (Φ : GDatum F n) : Prop :=
  ∃ (c₀ : ℂ) (f₀ : Fin n → mixedSpace F → ℂ) (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (f : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F → ℂ) (T : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ i, f₀ i ∈ schwartzInf) ∧ (∀ v i, f v i ∈ SBK (v.adicCompletion F)) ∧
      (∀ v ∉ T, c v = 1 ∧ ∀ i, f v i = ballIndV v 0 0) ∧ Φ = pureD c₀ f₀ c f

lemma GDatum.IsPure.adm {n : ℕ} {Φ : GDatum F n} (hΦ : Φ.IsPure) : Φ.Adm := by
  obtain ⟨c₀, f₀, c, f, T, -, -, hT, rfl⟩ := hΦ
  refine ⟨T, fun v hv => ?_⟩
  show c v • ptensor (f v) = oneV v n
  rw [(hT v hv).1, one_smul, oneV]
  congr 1; funext i; exact (hT v hv).2 i

lemma chirp_mem_schwartzInf (s : mixedSpace F) {g : mixedSpace F → ℂ} (hg : g ∈ schwartzInf) :
    (localDataInf (F := F)).chirp s g ∈ schwartzInf := by
  obtain ⟨G, rfl⟩ := hg
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : mixedSpace F => (psiInf (s * x * x) : ℂ)) G, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_chirpInf s), smul_eq_mul, LocalData.chirp,
    ψInf_eq, sq, mul_assoc]

lemma GDatum.IsPure.gN {Φ : GDatum F (2 * m)} (hΦ : Φ.IsPure) (b : F) : (gN a b Φ).IsPure := by
  obtain ⟨c₀, f₀, c, f, T, hf₀, hf, hT, rfl⟩ := hΦ
  have hfin : (⋃ i, (HeightOneSpectrum.Support (𝓞 F) (b * a i) : Set (HeightOneSpectrum (𝓞 F)))).Finite :=
    Set.finite_iUnion fun i => HeightOneSpectrum.Support.finite (𝓞 F) _
  refine ⟨c₀, fun i => (localDataInf (F := F)).chirp (mixedEmbedding F b * mixedEmbedding F (a i : F)) (f₀ i),
    c, fun v i => (localDataV v).chirp (algebraMap F _ b * algebraMap F _ (a i : F)) (f v i),
    T ∪ hfin.toFinset, fun i => chirp_mem_schwartzInf _ (hf₀ i),
    fun v i => chirp_mem_SBK (isStdChar_psiV v) (hf v i) _, fun v hv => ?_, ?_⟩
  · simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_iUnion, not_or, not_exists] at hv
    refine ⟨(hT v hv.1).1, fun i => ?_⟩
    show (localDataV v).chirp _ (f v i) = ballIndV v 0 0
    rw [(hT v hv.1).2 i]
    refine chirp_ballIndV ?_
    have := valued_le_one_of_not_mem_support (hv.2 i)
    simpa [map_mul] using this
  · show GDatum.mk _ _ = GDatum.mk _ _
    congr 1
    · dsimp only [pureD]; rw [LocalData.opNf_smul, LocalData.opNf_ptensor]; rfl
    · funext v; dsimp only [pureD]; rw [LocalData.opNf_smul, LocalData.opNf_ptensor]; rfl

/-! ### Rescaled Poisson summation in one variable -/

lemma sqrt_prod_modulus_eq_one {s : F} (hs : s ≠ 0) :
    ((Real.sqrt (mixedEmbedding.norm (mixedEmbedding F s)) : ℝ) : ℂ) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
        (algebraMap F (v.adicCompletion F) s)) : ℝ) : ℂ) = 1 := by
  have hfin := hasFiniteMulSupport_modK hs
  have hfs : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) :=
    hfin.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', Real.sqrt_one])
  have hmap := MonoidHom.map_finprod (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom hfs
  have hcast : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
        (algebraMap F (v.adicCompletion F) s)) : ℝ) : ℂ)) = ((∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) : ℝ) : ℂ) :=
    hmap.symm
  rw [hcast, ← Complex.ofReal_mul]
  have hnn : ∀ v : HeightOneSpectrum (𝓞 F),
      0 ≤ Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s) :=
    fun v => (Analysis.Weil.modK_pos ((map_ne_zero _).mpr hs)).le
  have hsq : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s))) ^ 2 =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s) := by
    rw [finprod_pow hfs]
    exact finprod_congr fun v => Real.sq_sqrt (hnn v)
  have hP : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) :=
    finprod_nonneg fun v => Real.sqrt_nonneg _
  have h := prod_modulus_eq_one hs
  have hA := mixedEmbedding.norm_nonneg (mixedEmbedding F s)
  have : Real.sqrt (mixedEmbedding.norm (mixedEmbedding F s)) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) = 1 := by
    have hsq' : (Real.sqrt (mixedEmbedding.norm (mixedEmbedding F s)) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s))) ^ 2 = 1 := by
      rw [mul_pow, hsq, Real.sq_sqrt hA, h]
    have hpos : 0 ≤ Real.sqrt (mixedEmbedding.norm (mixedEmbedding F s)) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) :=
      mul_nonneg (Real.sqrt_nonneg _) hP
    nlinarith [sq_nonneg (Real.sqrt (mixedEmbedding.norm (mixedEmbedding F s)) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) - 1)]
  rw [this, Complex.ofReal_one]

lemma sum_eq_sum_mul {G : F → ℂ} {s : F} (hs : s ≠ 0) : ∑' x : F, G (s * x) = ∑' y : F, G y :=
  (Equiv.mulLeft₀ s hs).tsum_eq G

/-- **Rescaled one-variable Poisson summation:** for $\alpha \in F^\times$, $g$ Schwartz and $f_v$ test functions with
$f_v = \mathbf 1_{\mathcal O_v}$ off $T$,
$\sum_{x\in F}F_\alpha g(x)\prod_vF_\alpha f_v(x) = \sum_{y\in F}g(y)\prod_vf_v(y)$, both absolutely convergent;
$F_\alpha = |2\alpha|^{1/2}D_{2\alpha}\mathcal F$ and $\prod_u|2\alpha|_u^{1/2} = 1$. -/
theorem poisson_Fa (g : SchwartzMap (mixedSpace F) ℂ) (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v, fv v ∈ SBK (v.adicCompletion F))
    (hout : ∀ v ∉ T, fv v = ballIndV v 0 0) (α : Fˣ) :
    (Summable fun x : F => (localDataInf (F := F)).Fa (mixedEmbedding F α) g (mixedEmbedding F x) *
      ∏ᶠ v, (localDataV v).Fa (algebraMap F _ α) (fv v) (algebraMap F _ x)) ∧
    ∑' x : F, (localDataInf (F := F)).Fa (mixedEmbedding F α) g (mixedEmbedding F x) *
      ∏ᶠ v, (localDataV v).Fa (algebraMap F _ α) (fv v) (algebraMap F _ x) =
    ∑' y : F, g (mixedEmbedding F y) * ∏ᶠ v, fv v (algebraMap F _ y) := by
  have hS' : ∀ v ∈ T, IsSchwartzBruhatV v (fv v) := fun v _ => isSchwartzBruhatV_of_mem_SBK v (hS v)
  set s : F := 2 * α with hsdef
  have hs : s ≠ 0 := mul_ne_zero two_ne_zero α.ne_zero
  set P : F → ℂ := fun y => fourierInf g (mixedEmbedding F y) * ∏ᶠ v, fourierV v (fv v) (algebraMap F _ y)
  have hP := summable_adelicPoisson_factorizable_rhs fv T hS' hout g
  -- the summand is `P (s x)`
  have hterm : ∀ x : F, (localDataInf (F := F)).Fa (mixedEmbedding F α) g (mixedEmbedding F x) *
      ∏ᶠ v, (localDataV v).Fa (algebraMap F _ α) (fv v) (algebraMap F _ x) = P (s * x) := by
    intro x
    have hfinF : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        fourierV v (fv v) (algebraMap F _ (s * x)) := by
      refine ((T.finite_toSet.union finite_support_diffExp).union
        (HeightOneSpectrum.Support.finite (𝓞 F) (s * x))).subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_union, Finset.mem_coe, Function.mem_support, not_or, not_not] at h
      exact hv (by
        show fourierV v (fv v) _ = 1
        rw [hout v h.1.1]
        exact fourierV_ballIndV_zero_eq_one v (by exact_mod_cast h.1.2)
          (valued_le_one_of_not_mem_support h.2))
    have hfinS : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) : ℝ) : ℂ) :=
      (hasFiniteMulSupport_modK hs).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
    have hloc : ∀ v : HeightOneSpectrum (𝓞 F), (localDataV v).Fa (algebraMap F _ α) (fv v) (algebraMap F _ x) =
        ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) s)) : ℝ) : ℂ) *
          fourierV v (fv v) (algebraMap F _ (s * x)) := by
      intro v
      simp only [LocalData.Fa, Pi.smul_apply, smul_eq_mul, dil, localDataV_four, hsdef, map_mul, map_ofNat]
      rfl
    have hinf : (localDataInf (F := F)).Fa (mixedEmbedding F α) g (mixedEmbedding F x) =
        ((Real.sqrt (mixedEmbedding.norm (mixedEmbedding F s)) : ℝ) : ℂ) *
          fourierInf g (mixedEmbedding F (s * x)) := by
      have e1 : (2 : mixedSpace F) * mixedEmbedding F α = mixedEmbedding F s := by rw [hsdef, map_mul, map_ofNat]
      have e2 : mixedEmbedding F s * mixedEmbedding F x = mixedEmbedding F (s * x) := (map_mul _ _ _).symm
      show ((Real.sqrt ((localDataInf (F := F)).md (2 * mixedEmbedding F α)) : ℝ) : ℂ) *
        (localDataInf (F := F)).four g (2 * mixedEmbedding F α * mixedEmbedding F x) = _
      rw [e1, e2]; rfl
    rw [hinf, finprod_congr hloc, finprod_mul_distrib hfinS hfinF]
    have hK := sqrt_prod_modulus_eq_one hs
    simp only [P]
    linear_combination (fourierInf g (mixedEmbedding F (s * x)) *
      ∏ᶠ v, fourierV v (fv v) (algebraMap F _ (s * x))) * hK
  refine ⟨?_, ?_⟩
  · rw [show (fun x : F => (localDataInf (F := F)).Fa (mixedEmbedding F α) g (mixedEmbedding F x) *
        ∏ᶠ v, (localDataV v).Fa (algebraMap F _ α) (fv v) (algebraMap F _ x)) = P ∘ (Equiv.mulLeft₀ s hs) from
      funext hterm]
    exact (Equiv.summable_iff _).mpr hP
  · rw [tsum_congr hterm, sum_eq_sum_mul hs]
    exact (adelicPoisson_factorizable fv T hS' hout g).symm

/-! ### The product formula for the Weil index -/

lemma hasFiniteMulSupport_gNV (t : Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gN (algebraMap F (v.adicCompletion F) t) := by
  have h1 := finite_weilV_ne_one (t : F) t.ne_zero
  have h2 := hasFiniteMulSupport_modK (mul_ne_zero (two_ne_zero : (2 : F) ≠ 0) t.ne_zero)
  refine (h1.union h2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, not_or, not_not] at h
  apply hv
  show weilV v (algebraMap F (v.adicCompletion F) (t : F)) * ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
    (2 * algebraMap F (v.adicCompletion F) (t : F))) : ℝ) : ℂ) = 1
  rw [h.1, show (2 : v.adicCompletion F) * algebraMap F _ (t : F) = algebraMap F _ (2 * t) by
    rw [map_mul, map_ofNat], h.2]
  simp

lemma gNV_prod (t : Fˣ) :
    (localDataInf (F := F)).gN (mixedEmbedding F t) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gN (algebraMap F (v.adicCompletion F) t) = 1 := by
  have hw := weilInf_mul_finprod_weilV (t : F) t.ne_zero
  have hs := sqrt_prod_modulus_eq_one (mul_ne_zero (two_ne_zero : (2 : F) ≠ 0) t.ne_zero)
  have hfinS : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (2 * t))) : ℝ) : ℂ) :=
    (hasFiniteMulSupport_modK (mul_ne_zero (two_ne_zero : (2 : F) ≠ 0) t.ne_zero)).subset
      fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), (localDataV v).gN (algebraMap F (v.adicCompletion F) t) =
      weilV v (algebraMap F _ (t : F)) *
        ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (2 * t))) : ℝ) : ℂ) := by
    intro v
    show weilV v (algebraMap F (v.adicCompletion F) (t : F)) * ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
      (2 * algebraMap F (v.adicCompletion F) (t : F))) : ℝ) : ℂ) = _
    rw [show (2 : v.adicCompletion F) * algebraMap F _ (t : F) = algebraMap F _ (2 * t) by rw [map_mul, map_ofNat]]
  rw [finprod_congr hloc, finprod_mul_distrib (finite_weilV_ne_one (t : F) t.ne_zero) hfinS]
  show weilInf (mixedEmbedding F t) * ((Real.sqrt (mixedEmbedding.norm (2 * mixedEmbedding F (t : F))) : ℝ) : ℂ) *
    _ = 1
  rw [show (2 : mixedSpace F) * mixedEmbedding F (t : F) = mixedEmbedding F (2 * t) by rw [map_mul, map_ofNat]]
  linear_combination (((Real.sqrt (mixedEmbedding.norm (mixedEmbedding F (2 * t))) : ℝ) : ℂ) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
        (algebraMap F (v.adicCompletion F) (2 * t))) : ℝ) : ℂ))) * hw + hs

lemma hasFiniteMulSupport_chiV_neg_one :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).chiV (aV a v) (-1) := by
  have h := hasFiniteMulSupport_chiV a (-1)
  simp only [Units.val_neg, Units.val_one, map_neg, map_one] at h
  exact h

/-- **The product formula for the Weil index of $V$:** $\gamma_{V,\infty}\prod_v\gamma_{V,v} = 1$. *Proof:*
$\gamma_{V,u} = \chi_{V,u}(-1)\prod_ig_u(a_i)^{-1}$; Hilbert reciprocity gives $\prod_u\chi_{V,u}(-1) = 1$, and
$\prod_ug_u(a_i) = \prod_u\gamma_u(a_i)\cdot\prod_u|2a_i|_u^{1/2} = 1$ by Weil's product formula and $|2a_i|_{\mathbb A} = 1$. -/
@[kb "weil1964" "§30, Prop. 5 (the global index is $1$) [unverified]"]
theorem prod_gammaV_eq_one :
    (localDataInf (F := F)).gammaV (aInf a) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gammaV (aV a v) = 1 := by
  have hG : ∀ i, Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    fun i => hasFiniteMulSupport_gNV (a i)
  have hGp : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ∏ i, (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    Function.HasFiniteMulSupport.prod hG Finset.univ
  have hGi : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (∏ i, (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ :=
    hGp.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', inv_one])
  simp only [LocalData.gammaV]
  rw [finprod_mul_distrib (hasFiniteMulSupport_chiV_neg_one a) hGi, finprod_inv_distrib,
    finprod_prod_comm Finset.univ _ fun i _ => hG i]
  have hχ := chiV_prod_eq_one a (-1)
  simp only [Units.val_neg, Units.val_one, map_neg, map_one] at hχ
  have hg : ∀ i, (localDataInf (F := F)).gN ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = 1 := fun i => gNV_prod (a i)
  have hprod : (∏ i, (localDataInf (F := F)).gN ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F)) *
      ∏ i, ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun i _ => hg i
  have hne : (∏ i, (localDataInf (F := F)).gN ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F)) ≠ 0 := by
    intro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have hne' : (∏ i, ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact zero_ne_one hprod
  field_simp
  linear_combination hχ - hprod

lemma gW_pureD {c₀ : ℂ} {f₀ : Fin (2 * m) → mixedSpace F → ℂ} {c : HeightOneSpectrum (𝓞 F) → ℂ}
    {f : ∀ v : HeightOneSpectrum (𝓞 F), Fin (2 * m) → v.adicCompletion F → ℂ} :
    gW a (pureD c₀ f₀ c f) = pureD (c₀ * (localDataInf (F := F)).gammaV (aInf a))
      (fun i => (localDataInf (F := F)).Fa (mixedEmbedding F (a i : F)) (f₀ i))
      (fun v => c v * (localDataV v).gammaV (aV a v))
      (fun v i => (localDataV v).Fa (algebraMap F _ (a i : F)) (f v i)) := by
  show GDatum.mk _ _ = GDatum.mk _ _
  congr 1
  · dsimp only [pureD]; rw [LocalData.opWf_smul, LocalData.opWf_ptensor', smul_smul]; rfl
  · funext v; dsimp only [pureD]
    rw [LocalData.opWf_smul, LocalData.opWf_ptensor (isOps_V v), smul_smul]; rfl

/-- **$\Theta$ is invariant under $\omega(w)$** on fully factorizable data: Poisson summation in each coordinate
(`poisson_Fa`) and $\prod_u\gamma_{V,u} = 1$ (`prod_gammaV_eq_one`). -/
@[kb "weil1964" "§29–§30 (Poisson summation formula) [unverified]"]
theorem thetaDist_gW {Φ : GDatum F (2 * m)} (hΦ : Φ.IsPure) : thetaDist (gW a Φ) = thetaDist Φ := by
  obtain ⟨c₀, f₀, c, f, T, hf₀, hf, hT, rfl⟩ := hΦ
  choose G hG using hf₀
  have hT' : ∀ v ∉ T ∪ (badW_finite a).toFinset, c v * (localDataV v).gammaV (aV a v) = 1 ∧
      ∀ i, (localDataV v).Fa (algebraMap F _ (a i : F)) (f v i) = ballIndV v 0 0 := by
    intro v hv
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
    have hv2 := hv.2
    simp only [badW, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hv2
    obtain ⟨hd, h2, hai, -⟩ := hv2
    refine ⟨by rw [(hT v hv.1).1, gammaV_eq_one a hv.2, one_mul], fun i => ?_⟩
    rw [(hT v hv.1).2 i]
    refine Fa_ballIndV (by exact_mod_cast hd) ?_
    rw [map_mul, valued_two_eq_one h2]
    simpa using valued_eq_one_of_not_mem (a i).ne_zero (hai i).1 (hai i).2
  have hP := fun i => poisson_Fa (G i) (fun v => f v i) T (fun v => hf v i) (fun v hv => (hT v hv).2 i) (a i)
  rw [gW_pureD, thetaDist_pureD hT' (fun i => by rw [← hG i]; exact (hP i).1),
    thetaDist_pureD hT (fun i => by
      rw [← hG i]
      exact summable_adelicPoisson_factorizable_lhs (fun v => f v i) T
        (fun v _ => isSchwartzBruhatV_of_mem_SBK v (hf v i)) (fun v hv => (hT v hv).2 i) (G i))]
  have hsum : ∀ i, ∑' x : F, (localDataInf (F := F)).Fa (mixedEmbedding F (a i : F)) (f₀ i) (mixedEmbedding F x) *
      ∏ᶠ v, (localDataV v).Fa (algebraMap F _ (a i : F)) (f v i) (algebraMap F _ x) =
      ∑' x : F, f₀ i (mixedEmbedding F x) * ∏ᶠ v, f v i (algebraMap F _ x) := by
    intro i; rw [← hG i]; exact (hP i).2
  simp only [hsum]
  have hγfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).gammaV (aV a v) :=
    (badW_finite a).subset fun v hv => by by_contra h; exact hv (gammaV_eq_one a h)
  rw [finprod_mul_distrib (hasFiniteMulSupport_const hT) hγfin]
  have := prod_gammaV_eq_one a
  linear_combination (c₀ * (∏ᶠ v, c v) * ∏ i, ∑' x : F, f₀ i (mixedEmbedding F x) *
    ∏ᶠ v, f v i (algebraMap F _ x)) * this

/-! ### The main theorem -/

/-- **The theta distribution is $\mathrm{SL}_2(F)$-invariant** (Weil 1964, §29–30): for every fully factorizable
datum $\Phi = c_\infty\bigotimes_if_{\infty,i}\otimes\bigotimes_v c_v\bigotimes_if_{v,i}$ (`IsPure`) and every
$\gamma \in \mathrm{SL}_2(F)$,
$$\Theta(\omega(\gamma)\Phi) = \sum_{\xi\in V(F)}(\omega(\gamma)\Phi)(\xi) = \sum_{\xi\in V(F)}\Phi(\xi) = \Theta(\Phi),$$
with $\omega(\gamma)$ acting at every place (`omegaG`; the finite components are the local representations
`weilRepV`). This is Poisson summation together with Hilbert reciprocity and Weil's product formula for the index:
the adelic form of the theta transformation law. -/
@[kb "weil1964" "§29–§30, Thm. 4 (the distribution is invariant under $\\mathrm{Sp}(X_k)$) [unverified]"]
theorem thetaDist_omegaG {Φ : GDatum F (2 * m)} (hΦ : Φ.IsPure) (γ : SL(2, F)) :
    thetaDist (omegaG a γ Φ) = thetaDist Φ := by
  unfold omegaG
  by_cases hc : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · rw [cellRep_of_c_eq_zero hc, Aof_of_ne (a_ne_zero_of_c_eq_zero hc)]
    show thetaDist (gM a _ (gN a _ Φ)) = _
    rw [thetaDist_gM a (hΦ.adm.gN a _), thetaDist_gN a hΦ.adm]
  · rw [cellRep_of_c_ne_zero hc, Aof_of_ne (unit_ne_zero_aux hc)]
    show thetaDist (gN a _ (gM a _ (gW a (gN a _ Φ)))) = _
    have h1 := hΦ.gN a ((γ : Matrix (Fin 2) (Fin 2) F) 1 1 / γ 1 0)
    rw [thetaDist_gN a ((h1.adm.gW a).gM a _), thetaDist_gM a (h1.adm.gW a), thetaDist_gW a h1,
      thetaDist_gN a hΦ.adm]

/-! ### At a finite place the global action is the local representation -/

/-- **Compatibility:** for $\gamma \in \mathrm{SL}_2(F)$ and $\Phi_v \in S(V_v)$, the $v$-component of $\omega(\gamma)\Phi$ is
$\omega_v(\gamma)\Phi_v$ for the local Weil representation `weilRepV` of $\mathrm{SL}_2(F_v)$. -/
theorem omegaG_fin_eq_weilRepV (γ : SL(2, F)) {Φ : GDatum F (2 * m)} (v : HeightOneSpectrum (𝓞 F))
    (hΦ : Φ.fin v ∈ (localDataV v).Sn (2 * m)) :
    (omegaG a γ Φ).fin v =
      (weilRepV v (aV a v) (Matrix.SpecialLinearGroup.map (algebraMap F (v.adicCompletion F)) γ) ⟨Φ.fin v, hΦ⟩ :
        (Fin (2 * m) → v.adicCompletion F) → ℂ) := by
  set ι := algebraMap F (v.adicCompletion F)
  have hinj : Function.Injective ι := ι.injective
  have hmap : ∀ i j, ((Matrix.SpecialLinearGroup.map ι γ : SL(2, v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j = ι ((γ : Matrix (Fin 2) (Fin 2) F) i j) := fun i j => rfl
  unfold omegaG weilRepV LocalData.weilRep
  rw [cellHom_apply]
  by_cases hc : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hc' : ((Matrix.SpecialLinearGroup.map ι γ : SL(2, v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by rw [hmap, hc, map_zero]
    rw [cellRep_of_c_eq_zero hc, cellRep_of_c_eq_zero hc', Aof_of_ne (a_ne_zero_of_c_eq_zero hc),
      Aof_of_ne (a_ne_zero_of_c_eq_zero hc')]
    show (localDataV v).opMf (aV a v) (ι _) ((localDataV v).opNf (aV a v) (ι _) (Φ.fin v)) =
      (localDataV v).opMf (aV a v) _ ((localDataV v).opNf (aV a v) _ (Φ.fin v))
    simp only [hmap, map_div₀, Units.val_mk0, Units.coe_map, RingHom.id_apply]
    rfl
  · have hc' : ((Matrix.SpecialLinearGroup.map ι γ : SL(2, v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 := by
      rw [hmap]; exact (map_ne_zero ι).mpr hc
    rw [cellRep_of_c_ne_zero hc, cellRep_of_c_ne_zero hc', Aof_of_ne (unit_ne_zero_aux hc),
      Aof_of_ne (unit_ne_zero_aux hc')]
    show (localDataV v).opNf (aV a v) (ι _) ((localDataV v).opMf (aV a v) (ι _) ((localDataV v).opWf (aV a v)
      ((localDataV v).opNf (aV a v) (ι _) (Φ.fin v)))) =
      (localDataV v).opNf (aV a v) _ ((localDataV v).opMf (aV a v) _ ((localDataV v).opWf (aV a v)
      ((localDataV v).opNf (aV a v) _ (Φ.fin v))))
    simp only [hmap, map_div₀, map_neg, map_inv₀, Units.val_mk0, Units.coe_map, RingHom.id_apply]
    rfl

end QuadFormsKB.WeilRep
