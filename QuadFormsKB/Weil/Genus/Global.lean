/-
# The genus-$g$ theta distribution and its invariance

**Layer:** global, over a number field $F$; the local operators are those of `Weil/Genus/Model.lean` at every place
(`localDataInf` at the archimedean block $F_\infty$, `localDataV v` at the finite places).

**Setting.** $V = F^{n}$, $n = 2m$, $Q = \langle a_0, \dots, a_{n-1}\rangle$, $a_i \in F^\times$, genus $g$. A **global datum of
genus $g$** (`GDatumG`) is a family $\Phi = (\Phi_\infty, (\Phi_v)_v)$ of functions on $V_\infty^g = M_{n\times g}(F_\infty)$ and
$V_v^g = M_{n\times g}(F_v)$, standing for $\Phi_\infty\otimes\bigotimes_v\Phi_v$ on $V(\mathbb A)^g$, and
$$\Theta(\Phi) = \sum_{\Xi\in M_{n\times g}(F)}\Phi_\infty(\Xi)\prod_v\Phi_v(\Xi)\qquad(\texttt{thetaDistG}).$$

**The global generators** (`gNG`, `gMG`, `gWG`): $\omega(n(B))$, $\omega(m(A))$, $\omega(w)$ at every place, for
$B \in M_g(F)$, $A \in \mathrm{GL}_g(F)$.

**Results.**
* `thetaDistG_gNG`: $\Theta(\omega(n(B))\Phi) = \Theta(\Phi)$ for every $B \in M_g(F)$ and admissible $\Phi$
  ($\Phi_v = \mathbf 1_{\mathcal O_v^{n\times g}}$ for almost all $v$): $\psi_{\mathbb A}$ is trivial on $F$.
* `thetaDistG_gMG`: $\Theta(\omega(m(A))\Phi) = \Theta(\Phi)$ for every $A \in \mathrm{GL}_g(F)$: Hilbert reciprocity for
  $\chi_V(\det A)$, $|\det A|_{\mathbb A} = 1$, and $\Xi \mapsto \Xi A$ on $M_{n\times g}(F)$.
* `thetaDistG_gWG`: $\Theta(\omega(w)\Phi) = \Theta(\Phi)$ for fully factorizable $\Phi$ (`IsPureG`): the genus-$g$ operator
  $\omega(w)$ is the genus-one $\omega(w)$ of the quadratic space $V^g = V\otimes F^g \cong \langle a_i\rangle_{(i,j)}$ of
  dimension $2mg$ (`flat`, `opWg_flat`; $\gamma_{V^g} = \gamma_V^g$), so this is `thetaDist_gW` for $V^g$.

**Not proved here.** Invariance under $\omega(w)$ for data that are not pure tensors in the coordinates (for instance
$\omega(n(B))\Phi$ with $B$ not diagonal) needs Poisson summation in $2mg$ variables for non-factorizable archimedean
components (the gap left open in genus one, now in genus $g$); with it, the three invariances and the
representation `weilRepSp` give $\Theta\circ\omega(\gamma) = \Theta$ for all $\gamma \in \mathrm{Sp}_{2g}(F)$.

Sources: Weil, Acta Math. 111 (1964), §§29–30 [unverified]; Kudla, *Notes on the local theta correspondence* (1996),
§I.4 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Global
import QuadFormsKB.Weil.ArchimedeanWeil
import QuadFormsKB.Weil.Genus.Model

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Matrix
open QuadFormsKB.Analysis
open scoped MatrixGroups Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

open WeilRep WeilRep.LocalData

variable {F : Type} [Field F] [NumberField F] {m g : ℕ}

variable (F m g) in
/-- **A global datum of genus $g$**: functions $\Phi_\infty$ on $M_{n\times g}(F_\infty)$ and $\Phi_v$ on $M_{n\times g}(F_v)$,
$n = 2m$, standing for the factorizable function $\Phi_\infty\otimes\bigotimes_v\Phi_v$ on $V(\mathbb A)^g$. -/
structure GDatumG where
  inf : PtG m g (mixedSpace F) → ℂ
  fin : ∀ v : HeightOneSpectrum (𝓞 F), PtG m g (v.adicCompletion F) → ℂ

/-- $\Xi \in M_{n\times g}(F)$ in $M_{n\times g}(F_\infty)$. -/
def ιInfG (Ξ : PtG m g F) : PtG m g (mixedSpace F) := Ξ.map (mixedEmbedding F)

/-- $\Xi \in M_{n\times g}(F)$ in $M_{n\times g}(F_v)$. -/
def ιVG (v : HeightOneSpectrum (𝓞 F)) (Ξ : PtG m g F) : PtG m g (v.adicCompletion F) :=
  Ξ.map (algebraMap F (v.adicCompletion F))

/-- The value $\Phi(\Xi) = \Phi_\infty(\Xi)\prod_v\Phi_v(\Xi)$ at a rational point. -/
def GDatumG.eval (Φ : GDatumG F m g) (Ξ : PtG m g F) : ℂ := Φ.inf (ιInfG Ξ) * ∏ᶠ v, Φ.fin v (ιVG v Ξ)

/-- **The theta distribution of genus $g$**: $\Theta(\Phi) = \sum_{\Xi\in M_{n\times g}(F)}\Phi(\Xi)$. -/
@[kb "weil1964" "§29–§30 (the distribution $\\sum_{\\xi\\in X_k}\\Phi(\\xi)$, $X = V^g$) [unverified]"]
def thetaDistG (Φ : GDatumG F m g) : ℂ := ∑' Ξ : PtG m g F, Φ.eval Ξ

/-- The standard local component $\mathbf 1_{\mathcal O_v^{n\times g}}$. -/
def oneVG (v : HeightOneSpectrum (𝓞 F)) (m g : ℕ) : PtG m g (v.adicCompletion F) → ℂ :=
  ptG fun _ _ => ballIndV v 0 0

/-- **Admissible data**: $\Phi_v = \mathbf 1_{\mathcal O_v^{n\times g}}$ for all but finitely many $v$. -/
def GDatumG.Adm (Φ : GDatumG F m g) : Prop :=
  ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ T, Φ.fin v = oneVG v m g

variable (a : Fin (2 * m) → Fˣ)

/-- **The global action of $n(B)$**, $B \in M_g(F)$. -/
def gNG (B : Matrix (Fin g) (Fin g) F) (Φ : GDatumG F m g) : GDatumG F m g :=
  ⟨opNg localDataInf (aInf a) (B.map (mixedEmbedding F)) Φ.inf,
    fun v => opNg (localDataV v) (aV a v) (B.map (algebraMap F _)) (Φ.fin v)⟩

/-- **The global action of $m(A)$**, $A \in \mathrm{GL}_g(F)$. -/
def gMG (A : GL (Fin g) F) (Φ : GDatumG F m g) : GDatumG F m g :=
  ⟨opMg localDataInf (aInf a) (Matrix.GeneralLinearGroup.map (mixedEmbedding F) A) Φ.inf,
    fun v => opMg (localDataV v) (aV a v) (Matrix.GeneralLinearGroup.map (algebraMap F _) A) (Φ.fin v)⟩

/-- **The global action of $w$.** -/
def gWG (Φ : GDatumG F m g) : GDatumG F m g :=
  ⟨opWg localDataInf (aInf a) Φ.inf, fun v => opWg (localDataV v) (aV a v) (Φ.fin v)⟩


/-- The finite places where some entry of $\Xi$ is not integral. -/
def badSetG (Ξ : PtG m g F) : Set (HeightOneSpectrum (𝓞 F)) :=
  ⋃ i, ⋃ j, (HeightOneSpectrum.Support (𝓞 F) (Ξ i j) : Set (HeightOneSpectrum (𝓞 F)))

lemma badSetG_finite (Ξ : PtG m g F) : (badSetG Ξ).Finite :=
  Set.finite_iUnion fun i => Set.finite_iUnion fun j => HeightOneSpectrum.Support.finite (𝓞 F) (Ξ i j)

lemma oneVG_eval_eq_one {v : HeightOneSpectrum (𝓞 F)} {Ξ : PtG m g F} (hv : v ∉ badSetG Ξ) :
    oneVG v m g (ιVG v Ξ) = 1 := by
  unfold oneVG ptG
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  exact ballIndV_algebraMap_eq_one fun h => hv (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, h⟩⟩)

lemma GDatumG.Adm.finite_mulSupport {Φ : GDatumG F m g} (hΦ : Φ.Adm) (Ξ : PtG m g F) :
    Function.HasFiniteMulSupport fun v => Φ.fin v (ιVG v Ξ) := by
  obtain ⟨T, hT⟩ := hΦ
  refine ((T.finite_toSet).union (badSetG_finite Ξ)).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, not_or] at h
  exact hv (by show Φ.fin v (ιVG v Ξ) = 1; rw [hT v h.1, oneVG_eval_eq_one h.2])

/-- $\operatorname{tr}(B\,Q[X])$ commutes with a ring map applied to everything. -/
lemma trace_QX_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (b : Fin (2 * m) → Kˣ)
    (b' : Fin (2 * m) → Lˣ) (hb : ∀ i, (b' i : L) = f (b i)) (B : Matrix (Fin g) (Fin g) K) (X : PtG m g K) :
    trace (B.map f * QX b' (X.map f)) = f (trace (B * QX b X)) := by
  rw [AddMonoidHom.map_trace f, Matrix.map_mul]
  congr 2
  simp only [QX, Matrix.map_mul, transpose_map]
  congr 2
  rw [diagonal_map (map_zero f)]
  congr 1; funext i; exact hb i

lemma eval_gNG {Φ : GDatumG F m g} (hΦ : Φ.Adm) (B : Matrix (Fin g) (Fin g) F) (Ξ : PtG m g F) :
    (gNG a B Φ).eval Ξ = Φ.eval Ξ := by
  have hInf := trace_QX_map (mixedEmbedding F) a (aInf a) (fun i => rfl) B Ξ
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), trace (B.map (algebraMap F (v.adicCompletion F)) *
      QX (aV a v) (ιVG v Ξ)) = algebraMap F _ (trace (B * QX a Ξ)) :=
    fun v => trace_QX_map _ a (aV a v) (fun i => rfl) B Ξ
  simp only [GDatumG.eval, gNG, opNg, ιInfG] at hInf ⊢
  simp only [hv, hInf, ψInf_eq, ψV_eq]
  rw [finprod_mul_distrib (hasFiniteMulSupport_psiV_coe _) (hΦ.finite_mulSupport Ξ)]
  have h := psiInf_mul_finprod_psiV (trace (B * QX a Ξ))
  rw [show ∀ x y z w : ℂ, x * y * (z * w) = (x * z) * (y * w) by intros; ring, h, one_mul]

/-- **$\Theta$ is invariant under $\omega(n(B))$**, $B \in M_g(F)$: $\psi_{\mathbb A}(\operatorname{tr}(B\,Q[\Xi])) = 1$. -/
@[kb "weil1964" "§29 ($\\psi$ is trivial on $F$) [unverified]"]
theorem thetaDistG_gNG {Φ : GDatumG F m g} (hΦ : Φ.Adm) (B : Matrix (Fin g) (Fin g) F) :
    thetaDistG (gNG a B Φ) = thetaDistG Φ :=
  tsum_congr fun Ξ => eval_gNG a hΦ B Ξ


/-- $\Xi \mapsto \Xi A$ on $M_{n\times g}(F)$. -/
def mulRightEquiv (A : GL (Fin g) F) : PtG m g F ≃ PtG m g F where
  toFun Ξ := Ξ * (A : Matrix (Fin g) (Fin g) F)
  invFun Ξ := Ξ * ((A⁻¹ : GL (Fin g) F) : Matrix (Fin g) (Fin g) F)
  left_inv Ξ := by simp [Matrix.mul_assoc]
  right_inv Ξ := by simp [Matrix.mul_assoc]

lemma eval_gMG {Φ : GDatumG F m g} (hΦ : Φ.Adm) (A : GL (Fin g) F) (Ξ : PtG m g F) :
    (gMG a A Φ).eval Ξ = Φ.eval (mulRightEquiv A Ξ) := by
  set t : Fˣ := Matrix.GeneralLinearGroup.det A with ht
  have hdetI : ((Matrix.GeneralLinearGroup.map (mixedEmbedding F) A : GL (Fin g) (mixedSpace F)) :
      Matrix (Fin g) (Fin g) (mixedSpace F)).det = mixedEmbedding F (t : F) := by
    rw [show ((Matrix.GeneralLinearGroup.map (mixedEmbedding F) A : GL (Fin g) (mixedSpace F)) :
      Matrix (Fin g) (Fin g) (mixedSpace F)) = (A : Matrix (Fin g) (Fin g) F).map (mixedEmbedding F) from rfl,
      ]
    exact (RingHom.map_det _ _).symm
  have hdetV : ∀ v : HeightOneSpectrum (𝓞 F), ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A :
      GL (Fin g) (v.adicCompletion F)) : Matrix (Fin g) (Fin g) (v.adicCompletion F)).det =
      algebraMap F (v.adicCompletion F) (t : F) := by
    intro v
    rw [show ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A : GL (Fin g) (v.adicCompletion F)) :
      Matrix (Fin g) (Fin g) (v.adicCompletion F)) = (A : Matrix (Fin g) (Fin g) F).map (algebraMap F _) from rfl,
      ]
    exact (RingHom.map_det _ _).symm
  have hι : ιInfG Ξ * ((Matrix.GeneralLinearGroup.map (mixedEmbedding F) A : GL (Fin g) (mixedSpace F)) :
      Matrix (Fin g) (Fin g) (mixedSpace F)) = ιInfG (mulRightEquiv A Ξ) := by
    simp only [ιInfG, mulRightEquiv, Equiv.coe_fn_mk, Matrix.map_mul]; rfl
  have hιv : ∀ v : HeightOneSpectrum (𝓞 F), ιVG v Ξ * ((Matrix.GeneralLinearGroup.map (algebraMap F
      (v.adicCompletion F)) A : GL (Fin g) (v.adicCompletion F)) : Matrix (Fin g) (Fin g) (v.adicCompletion F)) =
      ιVG v (mulRightEquiv A Ξ) := by
    intro v; simp only [ιVG, mulRightEquiv, Equiv.coe_fn_mk, Matrix.map_mul]; rfl
  simp only [GDatumG.eval, gMG, opMg, hdetI, hdetV, hι, hιv]
  have hcm : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).chiV (aV a v) (algebraMap F _ t) * ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m :=
    (hasFiniteMulSupport_chiV a t).mul (hasFiniteMulSupport_mdV_pow t)
  rw [finprod_mul_distrib hcm (hΦ.finite_mulSupport _), finprod_mul_distrib (hasFiniteMulSupport_chiV a t)
    (hasFiniteMulSupport_mdV_pow t)]
  have h1 := chiV_prod_eq_one a t
  have h2 := md_prod_eq_one (m := m) (F := F) t
  set P := (localDataInf (F := F)).chiV (aInf a) (mixedEmbedding F t)
  set Q := ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).chiV (aV a v) (algebraMap F _ t)
  set C := ((localDataInf (F := F)).md (mixedEmbedding F t) : ℂ) ^ m
  set E := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((localDataV v).md (algebraMap F _ t) : ℂ) ^ m
  calc P * C * Φ.inf (ιInfG (mulRightEquiv A Ξ)) * (Q * E * ∏ᶠ v, Φ.fin v (ιVG v (mulRightEquiv A Ξ)))
      = (P * Q) * (C * E) * (Φ.inf (ιInfG (mulRightEquiv A Ξ)) *
          ∏ᶠ v, Φ.fin v (ιVG v (mulRightEquiv A Ξ))) := by ring
    _ = _ := by rw [h1, h2, one_mul, one_mul]

/-- **$\Theta$ is invariant under $\omega(m(A))$**, $A \in \mathrm{GL}_g(F)$: Hilbert reciprocity for $\chi_V(\det A)$,
$|\det A|_{\mathbb A} = 1$, and $\Xi \mapsto \Xi A$. -/
@[kb "weil1964" "§29 (Hilbert reciprocity and $|t|_{\\mathbb A} = 1$) [unverified]"]
theorem thetaDistG_gMG {Φ : GDatumG F m g} (hΦ : Φ.Adm) (A : GL (Fin g) F) :
    thetaDistG (gMG a A Φ) = thetaDistG Φ := by
  rw [thetaDistG, tsum_congr fun Ξ => eval_gMG a hΦ A Ξ]
  exact (mulRightEquiv A).tsum_eq fun Ξ => Φ.eval Ξ

/-! ### Invariance under $w$: flattening $V^g$ to a quadratic space of dimension $2mg$ -/

variable (m g) in
/-- The index equivalence $\{0, \dots, 2mg-1\} \simeq \{0, \dots, 2m-1\}\times\{0, \dots, g-1\}$. -/
def eG : Fin (2 * (m * g)) ≃ Fin (2 * m) × Fin g :=
  (finCongr (Nat.mul_assoc 2 m g).symm).trans finProdFinEquiv.symm

/-- **Flattening** $M_{n\times g}(K) \simeq K^{ng}$, $X \mapsto (X_{ij})_{(i,j)}$. -/
def flatPt {K : Type*} : PtG m g K ≃ (Fin (2 * (m * g)) → K) where
  toFun X p := X (eG m g p).1 (eG m g p).2
  invFun x i j := x ((eG m g).symm (i, j))
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

@[simp] lemma flatPt_apply {K : Type*} (X : PtG m g K) (p : Fin (2 * (m * g))) :
    flatPt X p = X (eG m g p).1 (eG m g p).2 := rfl

@[simp] lemma flatPt_symm_apply {K : Type*} (x : Fin (2 * (m * g)) → K) (i : Fin (2 * m)) (j : Fin g) :
    flatPt.symm x i j = x ((eG m g).symm (i, j)) := rfl

/-- The coefficients of $V^g = V\otimes F^g$: $a'_{(i,j)} = a_i$. -/
def aFlat {K : Type*} [CommRing K] (b : Fin (2 * m) → Kˣ) : Fin (2 * (m * g)) → Kˣ := fun p => b (eG m g p).1

lemma prod_flat {M : Type*} [CommMonoid M] (h : Fin (2 * m) → Fin g → M) :
    ∏ p : Fin (2 * (m * g)), h (eG m g p).1 (eG m g p).2 = ∏ i, ∏ j, h i j := by
  rw [← Fintype.prod_prod_type']
  exact Fintype.prod_equiv (eG m g) _ _ fun p => rfl

lemma ptG_flat {K : Type*} (f : Fin (2 * m) → Fin g → K → ℂ) (X : PtG m g K) :
    ptG f X = ptensor (fun p => f (eG m g p).1 (eG m g p).2) (flatPt X) := by
  simp only [ptG, ptensor, flatPt, Equiv.coe_fn_mk]
  exact (prod_flat (fun i j => f i j (X i j))).symm

/-- **The Weil index of $V^g$:** $\gamma_{V^g} = \gamma_V^{\,g}$ (both are products of the normalized one-variable indices). -/
lemma gammaV_aFlat {K : Type*} [CommRing K] [MeasurableSpace K] {D : LocalData K} (hD : D.IsModel)
    (b : Fin (2 * m) → Kˣ) : D.gammaV (aFlat (g := g) b) = D.gammaV b ^ g := by
  rw [gammaV_eq_prod_gN hD, gammaV_eq_prod_gN hD]
  have h := prod_flat (m := m) (g := g) (M := ℂ) (fun i (_ : Fin g) => D.gN ((b i : Kˣ) : K))
  simp only [aFlat]
  rw [h, ← Finset.prod_pow]
  simp

/-- The flattened datum on $F^{2mg}$. -/
def flatD (Φ : GDatumG F m g) : GDatum F (2 * (m * g)) :=
  ⟨Φ.inf ∘ flatPt.symm, fun v => Φ.fin v ∘ flatPt.symm⟩

lemma thetaDistG_eq_flat (Φ : GDatumG F m g) : thetaDistG Φ = thetaDist (flatD Φ) := by
  rw [thetaDist, ← (flatPt (K := F)).tsum_eq]
  refine tsum_congr fun Ξ => ?_
  simp only [GDatumG.eval, GDatum.eval, flatD, Function.comp_apply]
  congr 2
  · congr 1; ext i j; simp [ιInfG, ιInf]
  · funext v; congr 1; ext i j; simp [ιVG, ιV]

/-- **Fully factorizable data of genus $g$**: the flattened datum is fully factorizable (`GDatum.IsPure`): pure tensors
in the $2mg$ coordinates at every place, Schwartz at $\infty$, standard at almost all $v$. -/
def GDatumG.IsPureG (Φ : GDatumG F m g) : Prop := (flatD Φ).IsPure

lemma flatD_gWG {Φ : GDatumG F m g} (hΦ : Φ.IsPureG) : flatD (gWG a Φ) = gW (aFlat a) (flatD Φ) := by
  obtain ⟨c₀, f₀, c, f, T, -, -, -, hΦe⟩ := hΦ
  have hinf : Φ.inf = c₀ • ptG (fun i j => f₀ ((eG m g).symm (i, j))) := by
    have := congrArg GDatum.inf hΦe
    funext X
    have h2 := congrFun this (flatPt X)
    simp only [flatD, Function.comp_apply, Equiv.symm_apply_apply, pureD] at h2
    rw [h2, Pi.smul_apply, Pi.smul_apply, ptG_flat]
    congr 2; funext p; simp
  have hfin : ∀ v, Φ.fin v = c v • ptG (fun i j => f v ((eG m g).symm (i, j))) := by
    intro v
    have := congrFun (congrArg GDatum.fin hΦe) v
    funext X
    have h2 := congrFun this (flatPt X)
    simp only [flatD, Function.comp_apply, Equiv.symm_apply_apply, pureD] at h2
    rw [h2, Pi.smul_apply, Pi.smul_apply, ptG_flat]
    congr 2; funext p; simp
  rw [hΦe]
  show GDatum.mk _ _ = GDatum.mk _ _
  congr 1
  · funext x
    simp only [flatD, gWG, Function.comp_apply, hinf, pureD, gW]
    rw [opWg_smul, opWg_ptG isOps_inf, LocalData.opWf_smul, LocalData.opWf_ptensor', smul_smul, smul_smul,
      Pi.smul_apply, Pi.smul_apply, ptG_flat, show aInf (aFlat (g := g) a) = aFlat (g := g) (aInf a) from rfl,
      gammaV_aFlat isModel_inf, Equiv.apply_symm_apply]
    congr 2
    funext p; simp [aFlat]
  · funext v x
    simp only [flatD, gWG, Function.comp_apply, hfin, pureD, gW]
    rw [opWg_smul, opWg_ptG (isOps_V v), LocalData.opWf_smul, LocalData.opWf_ptensor (isOps_V v), smul_smul,
      smul_smul, Pi.smul_apply, Pi.smul_apply, ptG_flat, show aV (aFlat (g := g) a) v = aFlat (g := g) (aV a v) from rfl,
      gammaV_aFlat (isModel_V v), Equiv.apply_symm_apply]
    congr 2
    funext p; simp [aFlat]

/-- **$\Theta$ is invariant under $\omega(w)$** on fully factorizable data of genus $g$: $\omega(w)$ on $V^g$ is the
genus-one $\omega(w)$ of the quadratic space $V^g \cong \langle a_i\rangle_{(i,j)}$ of dimension $2mg$
($\gamma_{V^g} = \gamma_V^g$ at every place), so this is `thetaDist_gW` (Poisson summation and Weil's product formula)
for $V^g$. -/
@[kb "weil1964" "§29–§30 (Poisson summation formula, $X = V^g$) [unverified]"]
theorem thetaDistG_gWG {Φ : GDatumG F m g} (hΦ : Φ.IsPureG) : thetaDistG (gWG a Φ) = thetaDistG Φ := by
  rw [thetaDistG_eq_flat, thetaDistG_eq_flat, flatD_gWG a hΦ]
  exact thetaDist_gW (aFlat a) hΦ

end QuadFormsKB.WeilRep.Genus
