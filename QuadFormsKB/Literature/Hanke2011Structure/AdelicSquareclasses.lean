/-
# Hanke 2011, §1.3 and §2: non-archimedean (idelic) squareclasses

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §1.3, p. 6, and §2, pp. 7–8.

For a number field $F$ with finite ideles $\mathbb A_{F,f}^\times$ (the units of Mathlib's finite adele ring
`FiniteAdeleRing (𝓞 F) F`, a restricted product of the completions $F_{\mathfrak p}$ with respect to the
$\mathcal O_{\mathfrak p}$) and $U_f = \prod_{\mathfrak p}\mathcal O_{\mathfrak p}^\times$:

* `FinIdele F` $= \mathbb A_{F,f}^\times$, `ideleComp v` its component at $\mathfrak p$, `Uf F` $= U_f$;
* `AdelicSqCl F` $= \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$, the group of *(integral) non-archimedean squareclasses*
  (§1.3, p. 6), with components `AdelicSqCl.comp v` $S \mapsto S_{\mathfrak p} \in \mathrm{SqCl}(F_{\mathfrak p}^\times,
  \mathcal O_{\mathfrak p}^\times)$, valuations `adelicOrd v` $= \operatorname{ord}_{\mathfrak p}(S)$ and support
  `supp S` $= \{\mathfrak p : \operatorname{ord}_{\mathfrak p}(S) \ne 0\}$, a finite set (`supp_finite`);
* **Lemma 2.2** (`lemma_2_2`, `lemma_2_2_rat`): $\mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f) \cong
  \prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ and
  $\mathrm{SqCl}(\mathbb A_{F,f}^\times) \cong \prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times)$, restricted products
  with respect to the images of $\mathcal O_{\mathfrak p}^\times$;
* the rational reduction $\rho_f$ (`rhoF`) and the diagonal map $\Delta$ (`diagSqCl`) of diagram (1), and
  **Definition 2.3** (`IsGloballyRational`): $\rho_f(S) \in \Delta(\mathrm{SqCl}(F^\times))$; equivalently there is
  $\alpha \in F^\times$ with $S_{\mathfrak p} \equiv \alpha$ modulo $(F_{\mathfrak p}^\times)^2$ for every $\mathfrak p$
  (`isGloballyRational_iff`);
* **Definition 2.4** (`assocIdeal`): $I(S) = \prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(S)}$.

The Hessian determinant squareclass of a lattice (Definition 2.1) and Lemma 2.10 are in `HessianSquareclass.lean`.
-/
import QuadFormsKB.Literature.Hanke2011Structure.Squareclasses

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField WithZero
open scoped RestrictedProduct nonZeroDivisors

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- **The finite ideles** $\mathbb A_{F,f}^\times$ of the number field $F$: the units of the finite adele ring
$\mathbb A_{F,f} = \prod'_{\mathfrak p}F_{\mathfrak p}$ (restricted product with respect to the $\mathcal O_{\mathfrak p}$), §1.3,
p. 5. -/
@[kb "hanke2011structure" "§1.3, p. 5 (A_{F,f}^×)"]
abbrev FinIdele : Type _ := (FiniteAdeleRing (𝓞 F) F)ˣ

variable {F}

/-- Evaluation of a finite adele at the prime $\mathfrak p$. -/
def adeleEval (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The component** $x_{\mathfrak p} \in F_{\mathfrak p}^\times$ of a finite idele $x$. -/
def ideleComp (v : HeightOneSpectrum (𝓞 F)) : FinIdele F →* (v.adicCompletion F)ˣ :=
  Units.map (adeleEval v).toMonoidHom

theorem ideleComp_val (v : HeightOneSpectrum (𝓞 F)) (x : FinIdele F) :
    ((ideleComp v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = (x : FiniteAdeleRing (𝓞 F) F) v := rfl

theorem FinIdele.ext {x y : FinIdele F} (h : ∀ v, ideleComp v x = ideleComp v y) : x = y := by
  exact Units.ext (Subtype.ext (funext fun v => congrArg Units.val (h v)))

variable (F)

/-- **The integral ideles** $U_f = \prod_{\mathfrak p}\mathcal O_{\mathfrak p}^\times$ (§1.3, p. 6): finite ideles all of whose
components are units of $\mathcal O_{\mathfrak p}$. -/
@[kb "hanke2011structure" "§1.3, p. 6 (U_f)"]
def Uf : Subgroup (FinIdele F) := ⨅ v, (localUnits v).comap (ideleComp v)

/-- **The group of (integral) non-archimedean squareclasses** $\mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f) =
\mathbb A_{F,f}^\times/U_f^2$ (§1.3, p. 6). -/
@[kb "hanke2011structure" "§1.3, p. 6 (SqCl(A_{F,f}^×, U_f))"]
abbrev AdelicSqCl : Type _ := SqCl (FinIdele F) (Uf F)

variable {F}

theorem mem_Uf {x : FinIdele F} : x ∈ Uf F ↔ ∀ v, ideleComp v x ∈ localUnits v := by
  simp [Uf, Subgroup.mem_iInf]

/-! ### Units of $\mathcal O_{\mathfrak p}$ -/

section LocalUnits

variable (v : HeightOneSpectrum (𝓞 F))

/-- $x \in F_{\mathfrak p}^\times$ lies in $\mathcal O_{\mathfrak p}^\times$ iff $|x|_{\mathfrak p} = 1$. -/
theorem mem_localUnits_iff {x : (v.adicCompletion F)ˣ} :
    x ∈ localUnits v ↔ Valued.v (x : v.adicCompletion F) = 1 := by
  constructor
  · intro hx
    have h := localUnits_le_ker v hx
    rw [MonoidHom.mem_ker] at h
    change Multiplicative.ofAdd (-log (Valued.v (x : v.adicCompletion F))) = 1 at h
    have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have hl : log (Valued.v (x : v.adicCompletion F)) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [← exp_log h0, hl, exp_zero]
  · intro hval
    have hinv : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
    let u : (v.adicCompletionIntegers F)ˣ :=
      { val := ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hval.le⟩
        inv := ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hinv.le⟩
        val_inv := Subtype.ext (Units.mul_inv x)
        inv_val := Subtype.ext (Units.inv_mul x) }
    exact ⟨u, Units.ext rfl⟩

theorem mem_localUnits_iff_ord {x : (v.adicCompletion F)ˣ} :
    x ∈ localUnits v ↔ localOrd v x = 1 := by
  rw [mem_localUnits_iff]
  have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  change _ ↔ Multiplicative.ofAdd (-log (Valued.v (x : v.adicCompletion F))) = 1
  constructor
  · intro h; simp [h]
  · intro h
    have hl : log (Valued.v (x : v.adicCompletion F)) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [← exp_log h0, hl, exp_zero]

/-- A unit of $\mathcal O_{\mathfrak p}$ that is a square in $F_{\mathfrak p}$ is the square of a unit of $\mathcal O_{\mathfrak p}$. -/
theorem sq_mem_localUnits {y : (v.adicCompletion F)ˣ} (h : y ^ 2 ∈ localUnits v) : y ∈ localUnits v := by
  rw [mem_localUnits_iff_ord] at h ⊢
  rw [map_pow] at h
  have := congrArg Multiplicative.toAdd h
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at this
  push_cast at this
  have h2 : Multiplicative.toAdd (localOrd v y) = 0 := by omega
  exact congrArg Multiplicative.ofAdd h2

/-- The units of $\mathcal O_{\mathfrak p}$ in $F_{\mathfrak p}^\times$ are the units of the submonoid $\mathcal O_{\mathfrak p}$
(the form used by Mathlib's restricted products). -/
theorem mem_localUnits_iff_units {x : (v.adicCompletion F)ˣ} :
    x ∈ localUnits v ↔ x ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units := by
  rw [mem_localUnits_iff]
  constructor
  · intro h
    have hinv : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hinv.le⟩
  · rintro ⟨h1, h2⟩
    have h1' : Valued.v (x : v.adicCompletion F) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1
    have h2' : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2'
    have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    exact le_antisymm h1' (by
      by_contra hlt
      push Not at hlt
      have := one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, hlt⟩
      exact absurd h2' (not_le.mpr this))

/-- A finite idele has unit components at all but finitely many primes. -/
theorem eventually_ideleComp_mem_localUnits (x : FinIdele F) :
    ∀ᶠ v in Filter.cofinite, ideleComp v x ∈ localUnits v := by
  filter_upwards [FiniteAdeleRing.unitsEquiv_finite_valued_eq_one x] with v hv
  rw [mem_localUnits_iff]
  exact hv

/-- **Constructing a finite idele** from components $x_{\mathfrak p} \in F_{\mathfrak p}^\times$ that lie in
$\mathcal O_{\mathfrak p}^\times$ for all but finitely many $\mathfrak p$. -/
def mkIdele (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hx : ∀ᶠ v in Filter.cofinite, x v ∈ localUnits v) : FinIdele F :=
  RestrictedProduct.mkUnit x (by
    filter_upwards [hx] with v hv
    exact (mem_localUnits_iff_units v).mp hv)

@[simp] theorem ideleComp_mkIdele (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hx : ∀ᶠ v in Filter.cofinite, x v ∈ localUnits v) (v : HeightOneSpectrum (𝓞 F)) :
    ideleComp v (mkIdele x hx) = x v := Units.ext rfl

end LocalUnits

/-! ### Components, valuations and support -/

/-- **The component** $S_{\mathfrak p} \in \mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ of a non-archimedean
squareclass $S$ (§1.3, p. 6). -/
@[kb "hanke2011structure" "§1.3, p. 6 (S_p)"]
def AdelicSqCl.comp (v : HeightOneSpectrum (𝓞 F)) : AdelicSqCl F →* LocalSqCl v :=
  QuotientGroup.map _ _ (ideleComp v) (by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨ideleComp v u, mem_Uf.mp hu v, by simp⟩)

@[simp] theorem AdelicSqCl.comp_mk (v : HeightOneSpectrum (𝓞 F)) (x : FinIdele F) :
    AdelicSqCl.comp v (SqCl.mk x) = SqCl.mk (ideleComp v x) := rfl

/-- **The valuation** $\operatorname{ord}_{\mathfrak p}(S) := \operatorname{ord}_{\mathfrak p}(S_{\mathfrak p})$ of a non-archimedean
squareclass (§1.3, p. 6). -/
@[kb "hanke2011structure" "§1.3, p. 6 (ord_p(S))"]
def adelicOrd (v : HeightOneSpectrum (𝓞 F)) (S : AdelicSqCl F) : ℤ :=
  SqCl.ordZ (localOrd v) (localUnits_le_ker v) (AdelicSqCl.comp v S)

theorem adelicOrd_mul (v : HeightOneSpectrum (𝓞 F)) (S T : AdelicSqCl F) :
    adelicOrd v (S * T) = adelicOrd v S + adelicOrd v T := by
  rw [adelicOrd, map_mul, SqCl.ordZ_mul]; rfl

/-- **The support** $\mathrm{Supp}(S) = \{\mathfrak p : \operatorname{ord}_{\mathfrak p}(S) \ne 0\}$ of a non-archimedean
squareclass (§1.3, p. 6). -/
@[kb "hanke2011structure" "§1.3, p. 6 (Supp(S))"]
def supp (S : AdelicSqCl F) : Set (HeightOneSpectrum (𝓞 F)) := {v | adelicOrd v S ≠ 0}

/-- **The support is finite**: $S_{\mathfrak p}$ is a unit class for all but finitely many $\mathfrak p$ (§1.3; Def. 2.4,
"this product is finite"). -/
@[kb "hanke2011structure" "§1.3, p. 6; Def. 2.4, p. 8 (finiteness)"]
theorem supp_finite (S : AdelicSqCl F) : (supp S).Finite := by
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  have h := eventually_ideleComp_mem_localUnits x
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  intro hu
  apply hv
  change SqCl.ordZ _ _ (SqCl.mk (ideleComp v x)) = 0
  rw [SqCl.ordZ_mk, (mem_localUnits_iff_ord v).mp hu]
  rfl

/-! ### Lemma 2.2: restricted product decompositions -/

variable (F) in
/-- The subgroup $\mathrm{SqCl}(\mathcal O_{\mathfrak p}^\times) \hookrightarrow \mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ of unit
classes. -/
def localUnitSqCl (v : HeightOneSpectrum (𝓞 F)) : Subgroup (LocalSqCl v) := (localUnits v).map SqCl.mk

variable (F) in
/-- **The restricted product** $\prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ with respect to
the subgroups $\mathrm{SqCl}(\mathcal O_{\mathfrak p}^\times)$ (Lemma 2.2). -/
abbrev RestrictedLocalSqCl : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [LocalSqCl v, localUnitSqCl F v]

theorem mk_mem_localUnitSqCl {v : HeightOneSpectrum (𝓞 F)} {x : (v.adicCompletion F)ˣ}
    (hx : x ∈ localUnits v) : (SqCl.mk x : LocalSqCl v) ∈ localUnitSqCl F v := ⟨x, hx, rfl⟩

/-- The components of a finite idele, as an element of the restricted product. -/
def toRestrictedAux : FinIdele F →* RestrictedLocalSqCl F where
  toFun x := ⟨fun v => SqCl.mk (ideleComp v x), by
    filter_upwards [eventually_ideleComp_mem_localUnits x] with v hv
    exact mk_mem_localUnitSqCl hv⟩
  map_one' := by ext v; simp
  map_mul' x y := by ext v; simp; rfl

/-- **The component map**$\mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f) \to
\prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$, $S \mapsto (S_{\mathfrak p})_{\mathfrak p}$. -/
def toRestricted : AdelicSqCl F →* RestrictedLocalSqCl F :=
  QuotientGroup.lift _ toRestrictedAux (by
    rintro _ ⟨u, hu, rfl⟩
    rw [MonoidHom.mem_ker]
    ext v
    change SqCl.mk (ideleComp v (u ^ 2)) = (1 : LocalSqCl v)
    rw [map_pow]
    exact SqCl.mk_sq_of_mem (mem_Uf.mp hu v))

theorem toRestricted_apply (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    toRestricted S v = AdelicSqCl.comp v S := by
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  rfl

theorem toRestricted_injective : Function.Injective (toRestricted (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro S hS
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  have hv : ∀ v, ∃ u ∈ localUnits v, u ^ 2 = ideleComp v x := by
    intro v
    have h := congrArg (fun T : RestrictedLocalSqCl F => T v) hS
    simp only [toRestricted_apply, AdelicSqCl.comp_mk] at h
    obtain ⟨u, hu, he⟩ := (QuotientGroup.eq_one_iff _).mp h
    exact ⟨u, hu, he⟩
  choose u hu hux using hv
  let y : FinIdele F := mkIdele u (Filter.Eventually.of_forall hu)
  have hy : y ∈ Uf F := mem_Uf.mpr fun v => by simp [y, hu v]
  have hxy : x = y ^ 2 := FinIdele.ext fun v => by simp [y, hux v]
  rw [hxy]
  exact SqCl.mk_sq_of_mem hy

theorem toRestricted_surjective : Function.Surjective (toRestricted (F := F)) := by
  intro s
  have hlift : ∀ v, ∃ x : (v.adicCompletion F)ˣ, SqCl.mk x = s v ∧ (s v ∈ localUnitSqCl F v → x ∈ localUnits v) := by
    intro v
    by_cases h : s v ∈ localUnitSqCl F v
    · obtain ⟨x, hx, he⟩ := h
      exact ⟨x, he, fun _ => hx⟩
    · obtain ⟨x, hx⟩ := SqCl.mk_surjective (s v)
      exact ⟨x, hx, fun h' => absurd h' h⟩
  choose x hx hxu using hlift
  have hev : ∀ᶠ v in Filter.cofinite, x v ∈ localUnits v := by
    filter_upwards [s.2] with v hv
    exact hxu v hv
  refine ⟨SqCl.mk (mkIdele x hev), ?_⟩
  ext v
  rw [toRestricted_apply, AdelicSqCl.comp_mk, ideleComp_mkIdele, hx]

/-- **Lemma 2.2** (integral form, p. 7): the non-archimedean integral squareclasses are the restricted product of the
local integral squareclasses,
$$\mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f) \cong \textstyle\prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times),
\qquad S \mapsto (S_{\mathfrak p})_{\mathfrak p},$$
with respect to the subgroups $\mathrm{SqCl}(\mathcal O_{\mathfrak p}^\times)$. -/
@[kb "hanke2011structure" "Lemma 2.2, p. 7 (integral squareclasses)"]
def lemma_2_2 : AdelicSqCl F ≃* RestrictedLocalSqCl F :=
  MulEquiv.ofBijective toRestricted ⟨toRestricted_injective, toRestricted_surjective⟩

@[simp] theorem lemma_2_2_apply (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    lemma_2_2 S v = AdelicSqCl.comp v S := toRestricted_apply S v

/-- A non-archimedean squareclass is determined by its components. -/
theorem AdelicSqCl.ext {S T : AdelicSqCl F} (h : ∀ v, AdelicSqCl.comp v S = AdelicSqCl.comp v T) : S = T :=
  toRestricted_injective (by ext v; rw [toRestricted_apply, toRestricted_apply, h])

/-- **Building a non-archimedean squareclass from local components** $S_{\mathfrak p}$ that are unit classes for all
but finitely many $\mathfrak p$ (the inverse of Lemma 2.2). -/
def AdelicSqCl.ofLocal (s : ∀ v : HeightOneSpectrum (𝓞 F), LocalSqCl v)
    (hs : ∀ᶠ v in Filter.cofinite, s v ∈ localUnitSqCl F v) : AdelicSqCl F :=
  lemma_2_2.symm (RestrictedProduct.mk s hs)

@[simp] theorem AdelicSqCl.comp_ofLocal (s : ∀ v : HeightOneSpectrum (𝓞 F), LocalSqCl v)
    (hs : ∀ᶠ v in Filter.cofinite, s v ∈ localUnitSqCl F v) (v : HeightOneSpectrum (𝓞 F)) :
    AdelicSqCl.comp v (AdelicSqCl.ofLocal s hs) = s v := by
  rw [← lemma_2_2_apply, AdelicSqCl.ofLocal, MulEquiv.apply_symm_apply]
  rfl

/-! ### The rational form of Lemma 2.2 -/

variable (F) in
/-- **The rational squareclasses of $F_{\mathfrak p}$**, $\mathrm{SqCl}(F_{\mathfrak p}^\times) = F_{\mathfrak p}^\times/(F_{\mathfrak p}^\times)^2$. -/
abbrev LocalRatSqCl (v : HeightOneSpectrum (𝓞 F)) : Type _ := SqCl (v.adicCompletion F)ˣ ⊤

variable (F) in
/-- The image of $\mathcal O_{\mathfrak p}^\times$ in $\mathrm{SqCl}(F_{\mathfrak p}^\times)$. -/
def localUnitRatSqCl (v : HeightOneSpectrum (𝓞 F)) : Subgroup (LocalRatSqCl F v) := (localUnits v).map SqCl.mk

variable (F) in
/-- **The restricted product** $\prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times)$ with respect to the images of
$\mathcal O_{\mathfrak p}^\times$ (Lemma 2.2). -/
abbrev RestrictedLocalRatSqCl : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [LocalRatSqCl F v, localUnitRatSqCl F v]

/-- The components of a finite idele modulo squares. -/
def toRestrictedRatAux : FinIdele F →* RestrictedLocalRatSqCl F where
  toFun x := ⟨fun v => SqCl.mk (ideleComp v x), by
    filter_upwards [eventually_ideleComp_mem_localUnits x] with v hv
    exact ⟨_, hv, rfl⟩⟩
  map_one' := by ext v; simp
  map_mul' x y := by ext v; simp; rfl

/-- The component map $\mathrm{SqCl}(\mathbb A_{F,f}^\times) \to \prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times)$. -/
def toRestrictedRat : SqCl (FinIdele F) ⊤ →* RestrictedLocalRatSqCl F :=
  QuotientGroup.lift _ toRestrictedRatAux (by
    rintro _ ⟨u, -, rfl⟩
    rw [MonoidHom.mem_ker]
    ext v
    change SqCl.mk (ideleComp v (u ^ 2)) = (1 : LocalRatSqCl F v)
    rw [map_pow]
    exact SqCl.mk_sq_of_mem (Subgroup.mem_top _))

theorem toRestrictedRat_mk (x : FinIdele F) (v : HeightOneSpectrum (𝓞 F)) :
    toRestrictedRat (SqCl.mk x) v = SqCl.mk (ideleComp v x) := rfl

theorem toRestrictedRat_injective : Function.Injective (toRestrictedRat (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro S hS
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  have hv : ∀ v, ∃ u : (v.adicCompletion F)ˣ, u ^ 2 = ideleComp v x := by
    intro v
    have h := congrArg (fun T : RestrictedLocalRatSqCl F => T v) hS
    simp only [toRestrictedRat_mk] at h
    obtain ⟨u, -, he⟩ := (QuotientGroup.eq_one_iff _).mp h
    exact ⟨u, he⟩
  choose u hux using hv
  have hev : ∀ᶠ v in Filter.cofinite, u v ∈ localUnits v := by
    filter_upwards [eventually_ideleComp_mem_localUnits x] with v hv
    exact sq_mem_localUnits v (by rw [hux v]; exact hv)
  let y : FinIdele F := mkIdele u hev
  have hxy : x = y ^ 2 := FinIdele.ext fun v => by simp [y, hux v]
  rw [hxy]
  exact SqCl.mk_sq_of_mem (Subgroup.mem_top _)

theorem toRestrictedRat_surjective : Function.Surjective (toRestrictedRat (F := F)) := by
  intro s
  have hlift : ∀ v, ∃ x : (v.adicCompletion F)ˣ, SqCl.mk x = s v ∧
      (s v ∈ localUnitRatSqCl F v → x ∈ localUnits v) := by
    intro v
    by_cases h : s v ∈ localUnitRatSqCl F v
    · obtain ⟨x, hx, he⟩ := h
      exact ⟨x, he, fun _ => hx⟩
    · obtain ⟨x, hx⟩ := SqCl.mk_surjective (s v)
      exact ⟨x, hx, fun h' => absurd h' h⟩
  choose x hx hxu using hlift
  have hev : ∀ᶠ v in Filter.cofinite, x v ∈ localUnits v := by
    filter_upwards [s.2] with v hv
    exact hxu v hv
  refine ⟨SqCl.mk (mkIdele x hev), ?_⟩
  ext v
  rw [toRestrictedRat_mk, ideleComp_mkIdele, hx]

/-- **Lemma 2.2** (rational form, p. 7): $\mathrm{SqCl}(\mathbb A_{F,f}^\times) \cong
\prod'_{\mathfrak p}\mathrm{SqCl}(F_{\mathfrak p}^\times)$, restricted product with respect to the images of
$\mathrm{SqCl}(\mathcal O_{\mathfrak p}^\times)$ under $\mathrm{SqCl}(\mathcal O_{\mathfrak p}^\times) \hookrightarrow \mathrm{SqCl}(F_{\mathfrak p}^\times)$. -/
@[kb "hanke2011structure" "Lemma 2.2, p. 7 (rational squareclasses)"]
def lemma_2_2_rat : SqCl (FinIdele F) ⊤ ≃* RestrictedLocalRatSqCl F :=
  MulEquiv.ofBijective toRestrictedRat ⟨toRestrictedRat_injective, toRestrictedRat_surjective⟩

/-! ### Rational reduction, the diagonal map and Definition 2.3 -/

/-- **The local rational reduction** $\rho_{\mathfrak p} : \mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times) \to
\mathrm{SqCl}(F_{\mathfrak p}^\times)$ (diagram (1), p. 7). -/
def rhoLocal (v : HeightOneSpectrum (𝓞 F)) : LocalSqCl v →* LocalRatSqCl F v :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, Subgroup.mem_top _, rfl⟩)

@[simp] theorem rhoLocal_mk (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    rhoLocal v (SqCl.mk x) = SqCl.mk x := rfl

/-- **The non-archimedean rational reduction** $\rho_f : \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f) \to
\mathrm{SqCl}(\mathbb A_{F,f}^\times)$ (diagram (1), p. 7). -/
@[kb "hanke2011structure" "§2, diagram (1), p. 7 (ρ_f)"]
def rhoF : AdelicSqCl F →* SqCl (FinIdele F) ⊤ :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, Subgroup.mem_top _, rfl⟩)

@[simp] theorem rhoF_mk (x : FinIdele F) : rhoF (SqCl.mk x) = SqCl.mk x := rfl

/-- $\rho_f = \prod_{\mathfrak p}\rho_{\mathfrak p}$ (p. 7): the components of $\rho_f(S)$ are the $\rho_{\mathfrak p}(S_{\mathfrak p})$. -/
theorem toRestrictedRat_rhoF (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    toRestrictedRat (rhoF S) v = rhoLocal v (AdelicSqCl.comp v S) := by
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  rfl

/-- **The diagonal map** $\Delta : \mathrm{SqCl}(F^\times) \to \mathrm{SqCl}(\mathbb A_{F,f}^\times)$, $x \mapsto (x, x, \dots)$
(diagram (1), p. 7). -/
@[kb "hanke2011structure" "§2, diagram (1), p. 7 (Δ)"]
def diagSqCl : SqCl Fˣ ⊤ →* SqCl (FinIdele F) ⊤ :=
  QuotientGroup.map _ _ (FiniteAdeleRing.unitEmbedding (𝓞 F) F) (by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨_, Subgroup.mem_top _, (map_pow _ u 2).symm⟩)

@[simp] theorem diagSqCl_mk (α : Fˣ) :
    diagSqCl (SqCl.mk α) = SqCl.mk (FiniteAdeleRing.unitEmbedding (𝓞 F) F α) := rfl

/-- The image of $\alpha \in F^\times$ in $F_{\mathfrak p}^\times$. -/
def unitsToLocal (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom

theorem ideleComp_unitEmbedding (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    ideleComp v (FiniteAdeleRing.unitEmbedding (𝓞 F) F α) = unitsToLocal v α := Units.ext rfl

/-- **Definition 2.3** (p. 8): a non-archimedean squareclass $S \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ is
*globally rational* if its rational reduction $\rho_f(S)$ lies in the image of $\mathrm{SqCl}(F^\times)$ under the
diagonal map $\Delta$. (The paper writes "in (13)"; the diagram meant is (1), p. 7.) -/
@[kb "hanke2011structure" "Def. 2.3, p. 8"]
def IsGloballyRational (S : AdelicSqCl F) : Prop := rhoF S ∈ diagSqCl.range

/-- **Global rationality, locally**: $S$ is globally rational iff there is $\alpha \in F^\times$ with
$S_{\mathfrak p} \equiv \alpha \pmod{(F_{\mathfrak p}^\times)^2}$ at every prime $\mathfrak p$ (by the rational form of Lemma 2.2). -/
@[kb "hanke2011structure" "Def. 2.3, p. 8; Lemma 2.2, p. 7"]
theorem isGloballyRational_iff (S : AdelicSqCl F) :
    IsGloballyRational S ↔ ∃ α : Fˣ, ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α) := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨α, rfl⟩ := SqCl.mk_surjective T
    refine ⟨α, fun v => ?_⟩
    have h := congrArg (fun U => toRestrictedRat U v) hT
    simp only [toRestrictedRat_rhoF, diagSqCl_mk, toRestrictedRat_mk, ideleComp_unitEmbedding] at h
    exact h.symm
  · rintro ⟨α, hα⟩
    refine ⟨SqCl.mk α, toRestrictedRat_injective ?_⟩
    ext v
    rw [toRestrictedRat_rhoF, hα v, diagSqCl_mk, toRestrictedRat_mk, ideleComp_unitEmbedding]

/-! ### Definition 2.4: the associated ideal -/

/-- **Definition 2.4** (p. 8): the associated (valuation) ideal
$I(S) = \prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(S_{\mathfrak p})}$ of a non-archimedean squareclass, a fractional
ideal of $F$ (a finite product, `supp_finite`). -/
@[kb "hanke2011structure" "Def. 2.4, p. 8"]
def assocIdeal (S : AdelicSqCl F) : FractionalIdeal (𝓞 F)⁰ F :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ^ adelicOrd v S

end

end QuadFormsKB.Hanke2011Structure
