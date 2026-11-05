/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at odd primes

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"): *a $p$-adic number is $p$-adically automorphous
for $f$ if and only if it is the product of an even number of norms of $p$-adic root vectors for $f$.*

**Layer.** As in `Section9Theorem18.lean`: $V_\mathfrak p = F_\mathfrak p^n$ for a finite prime $\mathfrak p$ of a
number field $F$ (Conway–Sloane: $F = \mathbb Q$), the form $Q$, a lattice $L$ with localization $L_\mathfrak p$
(`loc v L.1`), the integral automorphisms $O(L_\mathfrak p)$ (`locStabV`), the reflections $\tau_x$ (`symm`) and
$\theta(O^+(L_\mathfrak p))$ = `localSpinorNormGroup`.

**Route.** The book's remark after Theorem 18 (p. 391): *for odd $p$ it follows from [Cassels, p. 115, Corollary 1]
that every $p$-adically integral automorphism is the product of $p$-adically integral reflections.* The library has
this in two forms: Cassels' (`Cassels.intAut_eq_prod_tau`, matrices over $\mathbb Q_p$) and O'Meara's Theorem 92:4
(`OMeara.exists_symmetry_list`, lattices over any discrete valuation ring with $2$ a unit). O'Meara's is used: it is
stated for an arbitrary lattice on an abstract quadratic space, so it applies to $L_\mathfrak p \subseteq
F_\mathfrak p^n$ with $R = \mathfrak o_\mathfrak p$ directly. This file transports it to the coordinate layer:
* `glEquiv`: a matrix $g \in \mathrm{GL}_n(F_\mathfrak p)$ as a linear automorphism of $F_\mathfrak p^n$;
* `glEquiv_mem_orthLat`: $O(L_\mathfrak p)$ (`locStabV`) maps into O'Meara's $O(L_\mathfrak p)$ (`OMeara.orthLat`);
* `symmetry_apply_eq_symm_mulVec`: O'Meara's symmetry $\tau_u$ of the Mathlib form $x \mapsto Q(x)$ is the matrix
  `symm Q _ u`; so a symmetry in O'Meara's $O(L_\mathfrak p)$ is a reflection in a $p$-adic root vector.

**Proves**
* `exists_rootVectors_of_mem_locStabV` (Cassels Ch. 8, Cor. 1 to Lemma 3.3 / O'Meara 92:4 in the coordinate layer):
  for $\mathfrak p \nmid 2$, every $\sigma \in O(L_\mathfrak p)$ is $\tau_{x_1}\cdots\tau_{x_r}$ with $p$-adic root
  vectors $x_j$;
* `theorem18_odd` (**Theorem 18 at odd $p$, both directions**): for $\mathfrak p \nmid 2$, $A \in
  \theta(O^+(L_\mathfrak p))$ if and only if $A$ is, up to squares, the product of the norms of an even number of
  $p$-adic root vectors.
* `Theorem18Dyadic` (a **named statement**: the "only if" direction of Theorem 18 at the primes over $2$, Watson's
  Theorem 81 at $p = 2$; the book's remark: at $p = 2$ the integral automorphisms are "usually but not always"
  products of integral reflections [O'Meara 1958], so the route above does not apply) and
  `theorem18Statement_of_dyadic`: Conway–Sloane's `Theorem18Statement` follows from it.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18
import QuadFormsKB.Literature.OMeara.Sec92Sym

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Bridge

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- A matrix $g \in \mathrm{GL}_n(F_\mathfrak p)$ as the linear automorphism $x \mapsto gx$ of $F_\mathfrak p^n$. -/
def glEquiv (g : GL (Fin n) Fv) : (Fin n → Fv) ≃ₗ[Fv] (Fin n → Fv) where
  toFun x := g.val *ᵥ x
  invFun x := (g⁻¹).val *ᵥ x
  map_add' x y := mulVec_add _ x y
  map_smul' c x := mulVec_smul _ c x
  left_inv x := by
    change (g⁻¹).val *ᵥ (g.val *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv x := by
    change g.val *ᵥ ((g⁻¹).val *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem glEquiv_apply (g : GL (Fin n) Fv) (x : Fin n → Fv) : glEquiv g x = g.val *ᵥ x := rfl

/-- `locAct` is O'Meara's `latMap` for the linear automorphism of a matrix. -/
theorem latMap_glEquiv (g : GL (Fin n) Fv) (M : Submodule 𝔬 (Fin n → Fv)) :
    OMeara.latMap (R := 𝔬) (glEquiv g) M = locAct v g M := by
  ext x
  simp only [OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    glEquiv_apply]
  rfl

/-- If two linear automorphisms agree with a matrix pointwise, their images of a lattice agree. -/
theorem latMap_eq_locAct_of_apply {σ : (Fin n → Fv) ≃ₗ[Fv] (Fin n → Fv)} {g : GL (Fin n) Fv}
    (h : ∀ x, σ x = g.val *ᵥ x) (M : Submodule 𝔬 (Fin n → Fv)) :
    OMeara.latMap (R := 𝔬) σ M = locAct v g M := by
  rw [← latMap_glEquiv]
  have : σ = glEquiv g := LinearEquiv.ext fun x => (h x).trans (glEquiv_apply g x).symm
  rw [this]

/-- The Mathlib quadratic form $x \mapsto Q(x)$ on $F_\mathfrak p^n$ of a nondegenerate $Q$ is regular. -/
theorem associated_qk_nondegenerate (hQ : Q.Nondegenerate) :
    (QuadraticMap.associated (qk Q Fv)).Nondegenerate := by
  have hrefl : (QuadraticMap.associated (qk Q Fv)).IsRefl := fun x y h => by
    rw [← QuadraticMap.associated_isSymm Fv (qk Q Fv) x y]; exact h
  rw [hrefl.nondegenerate_iff_separatingLeft]
  intro x hx
  have hH : (Q.hessian.map (algebraMap F Fv)).det ≠ 0 := by
    rw [show Q.hessian.map (algebraMap F Fv) = (algebraMap F Fv).mapMatrix Q.hessian from rfl,
      ← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap F Fv).injective).mpr hQ
  have hv : ∀ y : Fin n → Fv, x ⬝ᵥ (Q.hessian.map (algebraMap F Fv) *ᵥ y) = 0 := by
    intro y
    have h := hx y
    have e : QuadraticMap.associated (qk Q Fv) x y = OMeara.bil (qk Q Fv) x y := rfl
    rw [e, OMeara.bil_eq_half,
      show (qk Q Fv) (x + y) - (qk Q Fv) x - (qk Q Fv) y = QuadraticMap.polar (qk Q Fv) x y from rfl,
      polar_qk] at h
    unfold qbil at h
    simpa using h
  have hvec : vecMul x (Q.hessian.map (algebraMap F Fv)) = 0 := by
    funext j
    have := hv (Pi.single j 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  exact Matrix.eq_zero_of_vecMul_eq_zero hH hvec

/-- **O'Meara's symmetry is the reflection matrix:** for $Q(u) \ne 0$, $\tau_u x$ computed with O'Meara's formula
$x - \frac{2B(x,u)}{Q(u)}u$ (for the Mathlib form $x \mapsto Q(x)$) equals `symm Q _ u` applied to $x$. -/
theorem symmetry_apply_eq_symm_mulVec {u : Fin n → Fv} (hu : qk Q Fv u ≠ 0) (x : Fin n → Fv) :
    OMeara.symmetry (qk Q Fv) u hu x = ((symm Q Fv u : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x := by
  have hu' : Q.evalIn Fv u ≠ 0 := by rwa [qk_apply] at hu
  rw [OMeara.symmetry_apply, symm_mulVec Q Fv hu' x, qk_apply]
  congr 1
  congr 1
  rw [OMeara.bil_eq_half,
    show (qk Q Fv) (x + u) - (qk Q Fv) x - (qk Q Fv) u = QuadraticMap.polar (qk Q Fv) x u from rfl,
    polar_qk, qbil_comm]
  unfold qbil
  field_simp

/-- $2$ is a unit of $\mathfrak o_\mathfrak p$ when $\mathfrak p \nmid 2$. -/
theorem isUnit_two_adicCompletionIntegers (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : IsUnit (2 : 𝔬) :=
  LocalDensity.DVR.dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) (LocalDensity.NF.π_not_dvd_two v h2)

/-- A product of O'Meara symmetries (in anisotropic vectors) is the matrix product of the reflections `symm`. -/
theorem prod_symmetryOrOne_apply (l : List (Fin n → Fv)) (hl : ∀ u ∈ l, qk Q Fv u ≠ 0) (x : Fin n → Fv) :
    (l.map (OMeara.symmetryOrOne (qk Q Fv))).prod x =
      ((symmProd Q Fv l : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x := by
  induction l generalizing x with
  | nil => simp [symmProd]
  | cons u l ih =>
    have hu := hl u (by simp)
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih (fun w hw => hl w (by simp [hw])),
      OMeara.sym4_symmetryOrOne_of_ne _ hu, symmetry_apply_eq_symm_mulVec Q hu]
    simp only [symmProd, List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]

/-- A symmetry of O'Meara's $O(L_\mathfrak p)$ is the reflection in a $p$-adic root vector. -/
theorem isRootVector_of_symmetry_mem (L : Lat F n) {u : Fin n → Fv} (hu : qk Q Fv u ≠ 0)
    (hτ : OMeara.symmetry (qk Q Fv) u hu ∈ OMeara.orthLat (R := 𝔬) (qk Q Fv) (loc v L.1)) :
    IsRootVector Q L v u := by
  refine ⟨by rwa [qk_apply] at hu, ?_⟩
  show locAct v _ (loc v L.1) = loc v L.1
  rw [← latMap_eq_locAct_of_apply (symmetry_apply_eq_symm_mulVec Q hu)]
  exact hτ.2

/-- An element of $O(L_\mathfrak p)$ (`locStabV`) is a unit of $L_\mathfrak p$ in O'Meara's sense. -/
theorem glEquiv_mem_orthLat (L : Lat F n) {σ : orthGroup Q Fv} (hσ : σ ∈ locStabV Q v L) :
    glEquiv (σ : GL (Fin n) Fv) ∈ OMeara.orthLat (R := 𝔬) (qk Q Fv) (loc v L.1) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [glEquiv_apply, qk_apply, qk_apply]
    exact evalIn_mulVec_of_mem Q σ.2 x
  · rw [latMap_glEquiv]
    exact hσ

/-- **Integral automorphisms are products of integral reflections** ($\mathfrak p \nmid 2$; Conway–Sloane's remark
after Theorem 18, p. 391, citing Cassels, p. 115, Cor. 1; here from O'Meara 92:4): every $\sigma \in
O(L_\mathfrak p)$ is $\tau_{x_1}\cdots\tau_{x_r}$ with $p$-adic root vectors $x_1, \dots, x_r$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark: for odd p every p-adically integral automorphism is a product of p-adically integral reflections)"]
theorem exists_rootVectors_of_mem_locStabV (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n)
    {σ : orthGroup Q Fv} (hσ : σ ∈ locStabV Q v L) :
    ∃ l : List (Fin n → Fv), (∀ u ∈ l, IsRootVector Q L v u) ∧ σ = symmProd Q Fv l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨[], by simp, ?_⟩
    exact Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))
  have hfin : 1 ≤ Module.finrank Fv (Fin n → Fv) := by
    rw [Module.finrank_fin_fun]; exact hn
  obtain ⟨l, -, hl, hσl⟩ := OMeara.exists_symmetry_list (R := 𝔬) (qk Q Fv)
    (isUnit_two_adicCompletionIntegers h2) (associated_qk_nondegenerate Q hQ) hfin
    (loc_isLattice v L.2) (glEquiv_mem_orthLat Q L hσ)
  have hl0 : ∀ u ∈ l, qk Q Fv u ≠ 0 := fun u hu => (hl u hu).1
  refine ⟨l, fun u hu => ?_, ?_⟩
  · obtain ⟨hu0, hτ⟩ := hl u hu
    exact isRootVector_of_symmetry_mem Q L hu0 hτ
  · have hpt : ∀ x, ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x =
        ((symmProd Q Fv l : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x := fun x => by
      rw [← glEquiv_apply, hσl, prod_symmetryOrOne_apply Q l hl0]
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have := congrFun (hpt (Pi.single j 1)) i
    simpa [mulVec_single] using this

/-- The determinant of a product of reflections in anisotropic vectors is $(-1)^r$. -/
theorem det_symmProd (l : List (Fin n → Fv)) (hl : ∀ u ∈ l, Q.evalIn Fv u ≠ 0) :
    ((symmProd Q Fv l : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det = (-1) ^ l.length := by
  induction l with
  | nil => simp [symmProd]
  | cons u l ih =>
    simp only [symmProd, List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul,
      List.length_cons, pow_succ] at ih ⊢
    rw [ih (fun w hw => hl w (by simp [hw])), symm_det Q Fv (hl u (by simp))]
    ring

/-- **Conway–Sloane, Theorem 18, at odd primes** (§9.5, p. 391; Watson Thm. 81), both directions: for
$\mathfrak p \nmid 2$ and $A \in F_\mathfrak p^\times$, $A$ is $p$-adically automorphous ($A \in
\theta(O^+(L_\mathfrak p))$) if and only if $A F_\mathfrak p^{\times 2} = Q(x_1)\cdots Q(x_r)F_\mathfrak p^{\times 2}$
for an even number $r$ of $p$-adic root vectors $x_1, \dots, x_r$. The "if" direction holds at every prime
(`mem_localSpinorNormGroup_of_rootVectors`); the "only if" direction uses that integral automorphisms are products of
integral reflections at odd $p$ (`exists_rootVectors_of_mem_locStabV`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (odd p, both directions)"]
theorem theorem18_odd (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n) (A : Fvˣ) :
    A ∈ localSpinorNormGroup Q hQ v L ↔
      ∃ xs : List (Fin n → Fv), Even xs.length ∧ (∀ x ∈ xs, IsRootVector Q L v x) ∧
        SqClass.mk A = sqClassOf (valProd Q Fv xs) := by
  constructor
  · intro hA
    rw [mem_localSpinorNormGroup] at hA
    obtain ⟨σ, ⟨hσL, hσ1⟩, hσθ⟩ := hA
    obtain ⟨l, hl, rfl⟩ := exists_rootVectors_of_mem_locStabV Q hQ h2 L hσL
    have hl0 : ∀ u ∈ l, Q.evalIn Fv u ≠ 0 := fun u hu => (hl u hu).1
    refine ⟨l, ?_, hl, ?_⟩
    · have hdet := Tamagawa.mem_soSub.mp hσ1
      rw [det_symmProd Q l hl0] at hdet
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      rw [hodd.neg_one_pow] at hdet
      exact absurd hdet (by norm_num)
    · rw [← hσθ, spinorNorm_symmProd Q Fv hQ l hl0]
  · rintro ⟨xs, hev, hr, hA⟩
    exact mem_localSpinorNormGroup_of_rootVectors hQ xs hev hr A hA

end Bridge

/-! ### $p = 2$: the remaining input -/

/-- **Theorem 18 at $p = 2$, the "only if" direction** (Conway–Sloane §9.5, p. 391, "based on Theorem 81 of [Wat3]",
G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every regular form $Q$ over
$\mathbb Q$, lattice $L$ and the prime $v$ over $2$, every $2$-adically automorphous number $A \in
\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root vectors.

It is the only part of Theorem 18 not proved in the library: the "if" direction holds at every prime
(`mem_localSpinorNormGroup_of_rootVectors`) and both directions hold at odd primes (`theorem18_odd`). The route used at
odd $p$ (integral automorphisms are products of integral reflections) fails at $p = 2$: the book's remark (p. 391) "for
$p = 2$ this is usually true but not always [O'Me4]" (O'Meara 1958; O'Meara–Pollak 1965 describe the exceptions).
Proving it needs Watson's argument or the computation of $\theta(O^+(L_2))$ by Earnest–Hsia (1975). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if'; stated; Watson 1960, Thm. 81)"]
structure Theorem18Dyadic : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ∀ A : (v.adicCompletion ℚ)ˣ,
      A ∈ localSpinorNormGroup Q hQ v L →
        ∃ xs : List (Fin n → v.adicCompletion ℚ), Even xs.length ∧ (∀ x ∈ xs, IsRootVector Q L v x) ∧
          SqClass.mk A = sqClassOf (valProd Q (v.adicCompletion ℚ) xs)

/-- The two $\mathbb Q$-algebra structures on $\mathbb Q_p$ (the completion's and the one of every characteristic-$0$
division ring) agree. -/
theorem instAlgebraAdicCompletion_rat_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v = DivisionRing.toRatAlgebra :=
  Algebra.algebra_ext _ _ fun r =>
    (eq_ratCast (@algebraMap ℚ _ _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v)) r).trans
      (eq_ratCast (@algebraMap ℚ _ _ _ DivisionRing.toRatAlgebra) r).symm

/-- **Conway–Sloane's Theorem 18 from its $p = 2$ case**: the full Theorem 18 (`Theorem18Statement`, all primes,
both directions) follows from the named statement `Theorem18Dyadic`; everything else is proved
(`theorem18_odd`, `mem_localSpinorNormGroup_of_rootVectors`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the p = 2 case)"]
theorem theorem18Statement_of_dyadic (h : Theorem18Dyadic) : Theorem18Statement where
  mem_iff n Q hQ L v A := by
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · refine ⟨h.exists_rootVectors n Q hQ L v h2 A, ?_⟩
      rintro ⟨xs, hev, hr, hA⟩
      exact mem_localSpinorNormGroup_of_rootVectors hQ xs hev hr A (by convert hA using 3; exact instAlgebraAdicCompletion_rat_eq v)
    · rw [← instAlgebraAdicCompletion_rat_eq v]; exact theorem18_odd Q hQ h2 L A

end QuadFormsKB.ConwaySloane
