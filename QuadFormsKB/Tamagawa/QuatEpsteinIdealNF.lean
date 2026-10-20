/-
# The Epstein sum of a left ideal class as the Epstein zeta function of a presented lattice

**Layer:** $F$ totally real (any class number), $D = (a,b)_F$ totally definite, $\mathcal O \subset D$ an order, $J$ a left ideal.
`QuatClassSum.epsteinSum J` is $E_J(s) = \sum_{\beta\in\mathcal O_F^\times\backslash((\mathcal O:J)\cap D^\times)}|N_{F/\mathbb Q}\operatorname{nrd}\beta|^{-s}$.
For $h_F > 1$ the lattice $(\mathcal O:J)$ is not free; it has a Steinitz presentation $(\mathcal O:J) = \{\sum_i\xi_if_i : \xi_i \in \mathfrak a_i\}$ with
$f$ an $F$-basis of $D$ and $\mathfrak a = (1,1,1,\mathfrak c)$ (`exists_presentation`). Then (`Gen.epsteinSum_eq_epsteinLat`)
$$E_J(s) = E_{(\mathfrak a, A_f)}(s) = \sum_{\xi\in\mathcal O_F^\times\backslash(L\setminus0)}|N_{F/\mathbb Q}Q_f(\xi)|^{-s},\qquad A_f = \mathrm{Gram}(\operatorname{nrd}; f)$$
(`epsteinLat`), and the Gram matrix is totally positive (`isTotPosGram_gramMat`). Only local freeness is used; no basis of $\mathcal O$, $J$ or $(\mathcal O:J)$
is chosen globally (the Steinitz presentation is a normal form of the lattice, not a basis of an ideal).

Source: Voight, *Quaternion Algebras* (2021), (26.5.8)–(26.5.9); Steinitz 1911 / O'Meara 81:5 (`Steinitz.exists_eq_glImage_steinitzLat`).
-/
import QuadFormsKB.Tamagawa.QuatEpsteinNF
import QuadFormsKB.Tamagawa.QuatClassSumNF
import QuadFormsKB.Tamagawa.QuatEichlerMass
import QuadFormsKB.Tamagawa.OrderNormFormNF
import QuadFormsKB.Lattices.Steinitz

open NumberField NumberField.InfinitePlace Quaternion
open scoped ENNReal Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.HilbertModular QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalUnfold QuadFormsKB.IdeleClass

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

namespace Gen

section Bridge

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

theorem exists_coe_of_mem_centralUnits_cls {u : (QuatF F a b)ˣ}
    (hu : u ∈ centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)) :
    ∃ c : F, c ≠ 0 ∧ (u : QuatF F a b) = (c : QuatF F a b) := by
  obtain ⟨w, rfl⟩ := hu
  exact ⟨algebraMap (𝓞 F) F (w : 𝓞 F), (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 w.ne_zero, rfl⟩

variable {J : Ideal O} {f : Fin 4 → QuatF F a b} {𝔞 : Fin 4 → FracIdeal F}
  (hmem : ∀ x : QuatF F a b, x ∈ colon J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i)
  (hli : LinearIndependent F f) (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0)

include hli in
theorem sum_smul_ne_zero_cls {ξ : Fin 4 → F} (hξ : ξ ≠ 0) : ∑ i, ξ i • f i ≠ 0 := by
  intro h
  exact hξ (funext fun i => Fintype.linearIndependent_iff.1 hli ξ h i)

include hmem hli hdiv in
/-- $\xi \mapsto \sum_i\xi_if_i$ as a unit of $D$ lying in $(\mathcal O : J)$. -/
def toColon (ξ : LatPt 𝔞) : ColonUnits J :=
  ⟨((isUnit_iff_nrd_ne_zero _).2 fun h => sum_smul_ne_zero_cls hli ξ.2.1 (hdiv _ h)).unit,
    (hmem _).2 ⟨ξ.1, ξ.2.2, rfl⟩⟩

include hmem hli hdiv in
theorem toColon_val (ξ : LatPt 𝔞) :
    (((toColon hmem hli hdiv ξ).1 : (QuatF F a b)ˣ) : QuatF F a b) = ∑ i, ξ.1 i • f i := rfl

include hmem hli hdiv in
theorem toColon_injective : Function.Injective (toColon (J := J) hmem hli hdiv) := by
  intro ξ ξ' h
  have h1 := congrArg (fun x : ColonUnits J => ((x.1 : (QuatF F a b)ˣ) : QuatF F a b)) h
  simp only [toColon_val] at h1
  apply Subtype.ext
  funext i
  have h0 : ∑ j, (ξ.1 j - ξ'.1 j) • f j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]; rw [h1, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

include hmem hli hdiv in
theorem toColon_surjective : Function.Surjective (toColon (J := J) hmem hli hdiv) := by
  intro x
  obtain ⟨ξ, hξ, hx⟩ := (hmem _).1 x.2
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply Units.ne_zero x.1
    rw [hx, h0]; simp
  refine ⟨⟨ξ, hξ0, hξ⟩, Subtype.ext (Units.ext ?_)⟩
  rw [toColon_val]; exact hx.symm

include hmem hli hdiv in
/-- **$\xi \mapsto \sum_i\xi_if_i$**: the nonzero points of the presented lattice are the units of $(\mathcal O : J)$. -/
def colonLatEquiv : LatPt 𝔞 ≃ ColonUnits J :=
  Equiv.ofBijective _ ⟨toColon_injective hmem hli hdiv, toColon_surjective hmem hli hdiv⟩

include hmem hli hdiv in
/-- **The orbits correspond** ($\mathcal O_F^\times$ acting on both sides). -/
def colonOrbitEquivLat :
    MulAction.orbitRel.Quotient (unitsF F) (LatPt 𝔞) ≃
      MulAction.orbitRel.Quotient (centralUnitsIn (R := 𝓞 F) J) (ColonUnits J) :=
  Quotient.congr (colonLatEquiv hmem hli hdiv) fun ξ ξ' => by
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨w, hw⟩ := u.2
      have hwc : (Units.map (algebraMap (𝓞 F) (QuatF F a b)).toMonoidHom w : (QuatF F a b)ˣ) ∈
          centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) := ⟨w, rfl⟩
      refine ⟨⟨⟨_, centralUnits_le_rStab J hwc⟩, Subgroup.mem_subgroupOf.2 hwc⟩, Subtype.ext (Units.ext ?_)⟩
      have hu' : u • ξ' = ξ := hu
      show (((Units.map (algebraMap (𝓞 F) (QuatF F a b)).toMonoidHom w : (QuatF F a b)ˣ) : QuatF F a b)) *
        (((colonLatEquiv hmem hli hdiv ξ').1 : (QuatF F a b)ˣ) : QuatF F a b) =
          (((colonLatEquiv hmem hli hdiv ξ).1 : (QuatF F a b)ˣ) : QuatF F a b)
      show _ * (∑ i, ξ'.1 i • f i) = ∑ i, ξ.1 i • f i
      rw [← hu', smul_latPt_val]
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hw, mul_smul, ← Algebra.smul_def]
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe]
      rw [algebraMap_smul]
    · rintro ⟨g, hg⟩
      obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 g.2)
      refine ⟨⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom w, w, rfl⟩, ?_⟩
      apply (colonLatEquiv hmem hli hdiv).injective
      have hg' : g • colonLatEquiv hmem hli hdiv ξ' = colonLatEquiv hmem hli hdiv ξ := hg
      rw [← hg']
      apply Subtype.ext; apply Units.ext
      show (((colonLatEquiv hmem hli hdiv ((⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom w, w, rfl⟩ : unitsF F) • ξ')).1 :
          (QuatF F a b)ˣ) : QuatF F a b) =
        (((g : rStab J) : (QuatF F a b)ˣ) : QuatF F a b) * (((colonLatEquiv hmem hli hdiv ξ').1 : (QuatF F a b)ˣ) : QuatF F a b)
      show ∑ i, ((((⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom w, w, rfl⟩ : unitsF F) • ξ') : LatPt 𝔞).1 i) • f i = _ * (∑ i, ξ'.1 i • f i)
      rw [smul_latPt_val]
      have hgval : (((g : rStab J) : (QuatF F a b)ˣ) : QuatF F a b) = algebraMap (𝓞 F) (QuatF F a b) (w : 𝓞 F) := by
        rw [← hw]; rfl
      rw [hgval, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Pi.smul_apply, smul_eq_mul]
      rw [mul_smul, ← Algebra.smul_def, algebraMap_smul]

omit hmem hli hdiv in
/-- $|N_{F/\mathbb Q}(w)| = 1$ for a unit $w$ of $\mathcal O_F$. -/
theorem abs_norm_unit_cls (w : (𝓞 F)ˣ) : |(Algebra.norm ℚ (algebraMap (𝓞 F) F (w : 𝓞 F)) : ℝ)| = 1 := by
  have h := w.isUnit.map (Algebra.norm ℤ : 𝓞 F →* ℤ)
  rw [Int.isUnit_iff_abs_eq] at h
  have h2 : ((Algebra.norm ℤ (w : 𝓞 F) : ℤ) : ℚ) = Algebra.norm ℚ ((w : 𝓞 F) : F) := Algebra.coe_norm_int _
  have h3 : |((Algebra.norm ℤ (w : 𝓞 F) : ℤ) : ℝ)| = 1 := by exact_mod_cast h
  rw [show (Algebra.norm ℚ (algebraMap (𝓞 F) F (w : 𝓞 F)) : ℝ) = ((Algebra.norm ℚ ((w : 𝓞 F) : F) : ℚ) : ℝ) from rfl,
    ← h2]
  exact_mod_cast h3

omit hmem hli hdiv in
theorem abs_norm_nrd_central_cls (u : centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b))
    (x : QuatF F a b) :
    |(Algebra.norm ℚ (nrd (((u : (QuatF F a b)ˣ) : QuatF F a b) * x)) : ℝ)| = |(Algebra.norm ℚ (nrd x) : ℝ)| := by
  obtain ⟨w, hw⟩ := u.2
  have hu : ((u : (QuatF F a b)ˣ) : QuatF F a b) = ((algebraMap (𝓞 F) F (w : 𝓞 F) : F) : QuatF F a b) := by
    rw [← hw]; rfl
  rw [hu, nrd_mul, show nrd ((algebraMap (𝓞 F) F (w : 𝓞 F) : F) : QuatF F a b) = (algebraMap (𝓞 F) F (w : 𝓞 F)) ^ 2 by
    simp [nrd], map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, abs_norm_unit_cls, one_pow, one_mul]

include hmem hli hdiv in
/-- **$E_J(t) = E_{(\mathfrak a, A_f)}(t)$**: the Epstein sum of the class of $J$ is the Epstein zeta function of the presented lattice
$(\mathcal O:J) = \{\sum_i\xi_if_i : \xi_i \in \mathfrak a_i\}$ with the Gram matrix $A_f$ of $\operatorname{nrd}$ in $f$. -/
theorem epsteinSum_eq_epsteinLat (t : ℝ) :
    epsteinSum J t = epsteinLat (gramMat f) 𝔞 t := by
  set e := colonOrbitEquivLat hmem hli hdiv
  unfold epsteinSum epsteinLat
  rw [← e.tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨g, hg⟩ : ∃ g : centralUnitsIn (R := 𝓞 F) J,
      g • colonLatEquiv hmem hli hdiv q.out = (e q).out := by
    have : (Quotient.mk _ (e q).out : MulAction.orbitRel.Quotient (centralUnitsIn (R := 𝓞 F) J) (ColonUnits J)) =
        Quotient.mk _ (colonLatEquiv hmem hli hdiv q.out) := by
      rw [Quotient.out_eq]
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    exact Quotient.exact this
  have hgc : ((g : rStab J) : (QuatF F a b)ˣ) ∈
      centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) := Subgroup.mem_subgroupOf.1 g.2
  have h1 : |(Algebra.norm ℚ (nrd (((e q).out.1 : (QuatF F a b)ˣ) : QuatF F a b)) : ℝ)| =
      |(Algebra.norm ℚ (qv (gramMat f) q.out.1) : ℝ)| := by
    rw [← hg]
    have hsm : ((((g • colonLatEquiv hmem hli hdiv q.out : ColonUnits J)).1 : (QuatF F a b)ˣ) : QuatF F a b) =
        (((g : rStab J) : (QuatF F a b)ˣ) : QuatF F a b) *
          (((colonLatEquiv hmem hli hdiv q.out).1 : (QuatF F a b)ˣ) : QuatF F a b) := rfl
    rw [hsm]
    rw [abs_norm_nrd_central_cls ⟨_, hgc⟩ _]
    have hv : (((colonLatEquiv hmem hli hdiv q.out).1 : (QuatF F a b)ˣ) : QuatF F a b) = ∑ i, q.out.1 i • f i := rfl
    rw [hv, ← qv_gramMat]
  rw [h1]

/-! ### The lattice $(\mathcal O : J)$ -/

section Colon

/-- **$(\mathcal O : J)$ as an $\mathcal O_F$-submodule of $D$.** -/
def colonLat (J : Ideal O) : Submodule (𝓞 F) (QuatF F a b) where
  carrier := colon J
  add_mem' := fun {β β'} hβ hβ' x hx => by rw [mul_add]; exact O.add_mem (hβ x hx) (hβ' x hx)
  zero_mem' := fun x hx => by rw [mul_zero]; exact O.zero_mem
  smul_mem' := fun c β hβ x hx => by
    rw [mul_smul_comm]; exact O.smul_mem (hβ x hx) c

theorem mem_colonLat {J : Ideal O} {β : QuatF F a b} : β ∈ colonLat J ↔ β ∈ colon J := Iff.rfl

theorem order_le_colonLat (J : Ideal O) : Subalgebra.toSubmodule O ≤ colonLat J := fun β hβ x hx =>
  O.mul_mem (idealSet_subset J hx) hβ


/-- $(\mathcal O : J)$ in the coordinates $1, i, j, k$, as an $\mathcal O_F$-submodule of $F^4$. -/
def colonSub (J : Ideal O) : Submodule (𝓞 F) (Fin 4 → F) :=
  (colonLat J).map ((tupEquiv a b).toLinearMap.restrictScalars (𝓞 F))

theorem mem_colonSub {J : Ideal O} {y : Fin 4 → F} : y ∈ colonSub J ↔ ∃ x ∈ colon J, tup x = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem isLattice_colonSub (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) :
    (colonSub J).IsLattice F where
  fg := by
    refine Submodule.FG.map _ ?_
    obtain ⟨n, hn𝔫, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have hnJ : algebraMap (𝓞 F) O n ∈ J := algebraMap_mem_of_mem_leftNrdIdeal hO J hn𝔫
    have hnF : algebraMap (𝓞 F) F n ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hn
    let g : QuatF F a b →ₗ[𝓞 F] QuatF F a b :=
      ((LinearMap.lsmul F (QuatF F a b)) ((algebraMap (𝓞 F) F n)⁻¹)).restrictScalars (𝓞 F)
    have hS : ((Subalgebra.toSubmodule O).map g).FG := hO.fg.map g
    refine Submodule.FG.of_le hS ?_
    intro β hβ
    have hx : algebraMap (𝓞 F) (QuatF F a b) n ∈ idealSet J := ⟨O.algebraMap_mem n, hnJ⟩
    have h1 := hβ _ hx
    refine ⟨algebraMap (𝓞 F) (QuatF F a b) n * β, h1, ?_⟩
    show (algebraMap (𝓞 F) F n)⁻¹ • (algebraMap (𝓞 F) (QuatF F a b) n * β) = β
    rw [← Algebra.smul_def, ← algebraMap_smul F n β, smul_smul, inv_mul_cancel₀ hnF, one_smul]
  span_eq_top := by
    have h1 := (isLattice_orderSub (O := O) hO).span_eq_top
    refine eq_top_iff.2 (h1.ge.trans (Submodule.span_mono ?_))
    exact Submodule.map_mono (order_le_colonLat J)

end Colon

/-! ### Steinitz presentations by fractional ideals -/

section Steinitz

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Steinitz Matrix

variable {m : ℕ}

theorem steinitzLat_eq_glImage_inv {M : Submodule (𝓞 F) (Fin (m + 1) → F)} {γ : GL (Fin (m + 1)) F}
    {𝔠 : Submodule (𝓞 F) F} (h : M = glImage γ (steinitzLat 𝔠)) : steinitzLat 𝔠 = glImage γ⁻¹ M := by
  ext y
  rw [mem_glImage]
  constructor
  · intro hy
    refine ⟨γ.val *ᵥ y, h ▸ mulVec_mem_glImage hy, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rintro ⟨x, hx, rfl⟩
    rw [h] at hx
    obtain ⟨z, hz, rfl⟩ := mem_glImage.1 hx
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem exists_fracIdeal_of_steinitz {M : Submodule (𝓞 F) (Fin (m + 1) → F)} (hM : M.IsLattice F)
    {γ : GL (Fin (m + 1)) F} {𝔠 : Submodule (𝓞 F) F} (h : M = glImage γ (steinitzLat 𝔠)) :
    ∃ I : FracIdeal F, ((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = 𝔠 := by
  have hst := steinitzLat_eq_glImage_inv h
  have hfgst : (steinitzLat (m := m) 𝔠).FG := by rw [hst]; exact hM.fg.map _
  have hc : 𝔠 = (steinitzLat (m := m) 𝔠).map
      ((LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).restrictScalars (𝓞 F)) := by
    ext c
    constructor
    · intro hc
      refine ⟨Pi.single (Fin.last m) c, ⟨fun i => ⟨0, ?_⟩, ?_⟩, by simp⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · simpa using hc
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩; exact hy
  have hfg : 𝔠.FG := by rw [hc]; exact hfgst.map _
  have hne : 𝔠 ≠ ⊥ := by
    intro h0
    -- the functional x ↦ (γ⁻¹ x)_last vanishes on M, hence on F^{m+1}
    let lamf : (Fin (m + 1) → F) →ₗ[F] F :=
      (LinearMap.proj (Fin.last m)).comp (Matrix.mulVecLin γ⁻¹.val)
    have hvan : ∀ x ∈ M, lamf x = 0 := by
      intro x hx
      rw [h] at hx
      obtain ⟨y, ⟨-, hy⟩, rfl⟩ := mem_glImage.1 hx
      have : lamf (γ.val *ᵥ y) = y (Fin.last m) := by
        simp only [lamf, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have hy0 : y (Fin.last m) = 0 := by
        rw [h0] at hy; exact (Submodule.mem_bot _).1 hy
      rw [this, hy0]
    have hspan : Submodule.span F (M : Set (Fin (m + 1) → F)) ≤ LinearMap.ker lamf :=
      Submodule.span_le.2 fun x hx => hvan x hx
    rw [hM.span_eq_top] at hspan
    have he : lamf (γ.val *ᵥ Pi.single (Fin.last m) 1) = 1 := by
      simp only [lamf, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      simp
    have h3 : γ.val *ᵥ Pi.single (Fin.last m) 1 ∈ LinearMap.ker lamf :=
      hspan (show γ.val *ᵥ Pi.single (Fin.last m) 1 ∈ (⊤ : Submodule F (Fin (m + 1) → F)) from Submodule.mem_top)
    rw [LinearMap.mem_ker, he] at h3
    exact one_ne_zero h3
  refine ⟨Units.mk0 ⟨𝔠, FractionalIdeal.isFractional_of_fg hfg⟩ ?_, rfl⟩
  intro h0
  apply hne
  have := congrArg (fun I : FractionalIdeal (𝓞 F)⁰ F => (I : Submodule (𝓞 F) F)) h0
  simpa using this

end Steinitz


section Presentation

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Steinitz Matrix

/-- The ideal vector $(1,1,1,\mathfrak c)$ of a Steinitz presentation. -/
def steinitzIdeals (I : FracIdeal F) : Fin 4 → FracIdeal F := fun i => if i = Fin.last 3 then I else 1

theorem latMem_steinitzIdeals_iff {I : FracIdeal F} {𝔠 : Submodule (𝓞 F) F}
    (hI : ((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = 𝔠) {ξ : Fin 4 → F} :
    LatMem (steinitzIdeals I) ξ ↔ ξ ∈ steinitzLat (m := 3) 𝔠 := by
  unfold LatMem steinitzIdeals
  rw [show (∀ i : Fin 4, ξ i ∈ ((((if i = Fin.last 3 then I else 1 : FracIdeal F)) :
      FractionalIdeal (𝓞 F)⁰ F) : Set F)) ↔ _ from Fin.forall_fin_succ']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, ?_⟩
    · have := h1 i
      rw [if_neg (Fin.castSucc_ne_last i)] at this
      have h' : ξ i.castSucc ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by simpa using this
      exact (FractionalIdeal.mem_one_iff (𝓞 F)⁰).1 h'
    · have := h2
      rw [if_pos rfl] at this
      rw [← hI]; exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [if_neg (Fin.castSucc_ne_last i)]
      exact (FractionalIdeal.mem_one_iff _).2 (h1 i)
    · rw [if_pos rfl]
      rw [← hI] at h2; exact h2

/-- **A Steinitz presentation of $(\mathcal O : J)$.** There are an $F$-basis $f$ of $D$ and fractional ideals $\mathfrak a_i$ ($=1,1,1,\mathfrak c$)
with $(\mathcal O : J) = \{\sum_i\xi_if_i : \xi_i \in \mathfrak a_i\}$ (Steinitz's normal form of the $\mathcal O_F$-lattice $(\mathcal O:J)$). -/
theorem exists_presentation (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) :
    ∃ (f : Fin 4 → QuatF F a b) (𝔞 : Fin 4 → FracIdeal F), LinearIndependent F f ∧
      ∀ x : QuatF F a b, x ∈ colon J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i := by
  classical
  have hlat := isLattice_colonSub hO hJ
  obtain ⟨γ, 𝔠, hγ⟩ := exists_eq_glImage_steinitzLat (m := 3) hlat
  obtain ⟨I, hI⟩ := exists_fracIdeal_of_steinitz hlat hγ
  let col : Fin 4 → (Fin 4 → F) := fun i => γ.val *ᵥ Pi.single i 1
  refine ⟨fun i => (tupEquiv a b).symm (col i), steinitzIdeals I, ?_, fun x => ?_⟩
  · have hli1 : LinearIndependent F col := by
      have := (Pi.basisFun F (Fin 4)).linearIndependent.map' (Matrix.mulVecLin γ.val) (by
        rw [LinearMap.ker_eq_bot]
        intro u v huv
        have h2 := congrArg (fun z => γ⁻¹.val *ᵥ z) huv
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2)
      convert this using 1
      funext i
      simp [col, Pi.basisFun_apply]
    exact hli1.map' (tupEquiv a b).symm.toLinearMap (by simp)
  · have hsum : ∀ ξ : Fin 4 → F, tupEquiv a b (∑ i, ξ i • (tupEquiv a b).symm (col i)) = γ.val *ᵥ ξ := by
      intro ξ
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply, col]
      have hξ : ξ = ∑ i, ξ i • (Pi.single i (1 : F) : Fin 4 → F) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hξ]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
    constructor
    · intro hx
      have h1 : tup x ∈ colonSub J := mem_colonSub.2 ⟨x, hx, rfl⟩
      rw [hγ] at h1
      obtain ⟨y, hy, hyx⟩ := mem_glImage.1 h1
      refine ⟨y, (latMem_steinitzIdeals_iff hI).2 hy, ?_⟩
      apply (tupEquiv a b).injective
      rw [hsum]; exact hyx.symm
    · rintro ⟨ξ, hξ, rfl⟩
      have hy := (latMem_steinitzIdeals_iff hI).1 hξ
      have h1 : γ.val *ᵥ ξ ∈ colonSub J := by
        rw [hγ]; exact mulVec_mem_glImage hy
      obtain ⟨x', hx', hxx⟩ := mem_colonSub.1 h1
      have : x' = ∑ i, ξ i • (tupEquiv a b).symm (col i) := by
        apply (tupEquiv a b).injective
        rw [hsum]; exact hxx
      rw [← this]; exact hx'

end Presentation


section Combined

/-- **The Epstein sum of a left ideal is the Epstein zeta function of a totally positive presented lattice** (any class number):
for a left ideal $J$ of an order $\mathcal O$ of a totally definite division quaternion algebra with $\operatorname{nrd}J \ne 0$ there are
an $F$-basis $f$ of $D$ and fractional ideals $\mathfrak a_i$ ($=1,1,1,\mathfrak c$) such that $(\mathcal O:J) = \bigoplus_i\mathfrak a_if_i$, the Gram matrix
$A_f$ of $\operatorname{nrd}$ is totally positive, and $E_J(t) = E_{(\mathfrak a, A_f)}(t)$ for every $t$. -/
@[kb "voight2021" "(26.5.8)–(26.5.9)"]
theorem epsteinSum_eq_epstein_presented (hdef : IsTotDefinite a b) (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0)
    (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) :
    ∃ (f : Fin 4 → QuatF F a b) (𝔞 : Fin 4 → FracIdeal F), LinearIndependent F f ∧ IsTotPosGram (gramMat f) ∧
      (∀ x : QuatF F a b, x ∈ colon J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i) ∧
      ∀ t : ℝ, epsteinSum J t = epsteinLat (gramMat f) 𝔞 t := by
  obtain ⟨f, 𝔞, hli, hmem⟩ := exists_presentation hO hJ
  exact ⟨f, 𝔞, hli, isTotPosGram_gramMat hdef hli, hmem, epsteinSum_eq_epsteinLat hmem hli hdiv⟩

end Combined

end Bridge

end Gen

end QuadFormsKB.QuatOrder
