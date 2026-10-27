import QuadFormsKB.Tamagawa.Measure.Weil.BinaryFiniteLocal
import QuadFormsKB.Tamagawa.BinaryCMAssembly
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusLocal

/-!
# The binary torus at a finite place, CM data: the index of the order $\mathfrak o_v[\sqrt{-D}]$ in the maximal order

**Layer:** $F$ a number field, $E/F$ quadratic with `SqrtData D E` ($\theta^2=-D$, $D\in\mathcal O_F\setminus0$), $v$ a finite place of $F$.
The basis $b=(1,\theta)$ (`sqrtBasis`) satisfies the hypotheses of `BinaryFiniteLocal.lean` with $d=-D$; there
$E_v=F_v[\omega]/(\omega^2+D)$ = `QuadraticAlgebra Fv (algebraMap F Fv (-D)) 0`, which is *definitionally* `QuadK D Fv` of
`BinaryTorusLocal.lean` (`quadK_eq`). Write $\mathcal O_{E,v}=\{z:\operatorname{tr}z,Nz\in\mathfrak o_v\}$ (`maxOrderCM`),
$R_v=\mathfrak o_v[\omega]$ (`coordOrder (-D) v`), $c_v$ = `BinaryCM.cv S v`, the exponent of `BinaryCM.LocData`
(the local data of the maximal order), $q=N(v)$.

**Proves**
* **`mem_loc_latE_iff`**: the localization $(\mathcal O_E)_v\subseteq F_v^2$ (`loc v (latE S)`), in the coordinates $y_0+y_1\theta$,
  is exactly $\mathcal O_{E,v}$ (using L1 of `BinaryFiniteLocal.lean`).
* **L2 (`relIndex_maxOrder_coordOrder`, `smul_mem_coordOrder`, `relIndex_unitWindow_cv`).** $[\mathcal O_{E,v}:R_v]=q^{c_v}$,
  $\varpi^{c_v}\mathcal O_{E,v}\subseteq R_v$ ($\varpi$ = `πF v` = `NF.π v`), and for $k\ge\max(1,c_v)$
  $[1+\varpi^k\mathcal O_{E,v}:1+\varpi^kR_v]=q^{c_v}$.
* **L4 (`discr_mul_prod_localIndex_sq`, `discr_mul_finprod_localIndex_sq`, `absNorm_conductor_eq_prod_localIndex`).** With
  $i_v=[\mathcal O_{E,v}:R_v]=q^{c_v}$ (equal to $1$ unless $\mathfrak p_v\mid2D$):
  $$|d_E|\Bigl(\prod_vi_v\Bigr)^2=4^{[F:\mathbb Q]}|d_F|^2\,|N_{F/\mathbb Q}D|,\qquad N(\mathfrak f)=\Bigl(\prod_vi_v\Bigr)^2,$$
  $\mathfrak f$ the conductor of $\mathcal O_F[\theta]$ in $\mathcal O_E$ (this restates `BinaryCM.discr_relation` and `absNorm_conductor`).
-/

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero Matrix QuadFormsKB.Lattices
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa LocalDensity QuadFormsKB.Tamagawa.BinaryCM

section CM

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)

/-- **The basis $(1,\theta)$ of $E/F$**, the image of the standard basis under the coordinate isomorphism
$F^2\simeq E$, $x\mapsto x_0 + x_1\theta$ (`coordEquiv`). -/
def sqrtBasis : Module.Basis (Fin 2) F E := (Pi.basisFun F (Fin 2)).map (BinaryCM.coordEquiv S)

/-- The $i$-th basis vector is $c(e_i)$, $c(x) = x_0+x_1\theta$. -/
theorem sqrtBasis_apply (i : Fin 2) : sqrtBasis S i = cE S (Pi.single i 1) := by
  simp [sqrtBasis, BinaryCM.coordEquiv_apply]

/-- The first basis vector is $1$. -/
theorem sqrtBasis_zero : sqrtBasis S 0 = 1 := by
  rw [sqrtBasis_apply]; simp [cE]

/-- The second basis vector is $\theta$. -/
theorem sqrtBasis_one : sqrtBasis S 1 = S.θ := by
  rw [sqrtBasis_apply]; simp [cE]

/-- $\theta^2 = -D$, in the form $\delta^2 = d$ with $d = -D\in\mathcal O_F$. -/
theorem sqrtBasis_mul_self :
    sqrtBasis S 1 * sqrtBasis S 1 = algebraMap F E (((-D : 𝓞 F) : 𝓞 F) : F) := by
  rw [sqrtBasis_one, θ_sq]
  simp

/-- The coordinates of $u\in E$ in the basis $(1,\theta)$ are `coordOf S u`. -/
theorem sqrtBasis_repr (u : E) (i : Fin 2) : (sqrtBasis S).repr u i = coordOf S u i := by
  simp [sqrtBasis, Module.Basis.map_repr, coordOf]

/-- The coordinates of an algebraic integer of $E$ lie in the lattice `latE` of the maximal order. -/
theorem coordOf_mem_latE (a : 𝓞 E) : coordOf S (a : E) ∈ latE S := by
  rw [mem_latE, cE_coordOf]
  exact a.isIntegral_coe

/-! ### The local maximal order $\Lambda = (\mathcal O_E)_v$ in coordinates -/

section Coords

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Ev" => QuadraticAlgebra (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (((-D : 𝓞 F) : 𝓞 F) : F)) 0

/-- **The maximal order $\mathcal O_{E,v}$** of $E_v=F_v[\omega]/(\omega^2+D)$ for the CM data `S`:
$\{z : \operatorname{tr}z, Nz\in\mathfrak o_v\}$ (`maxOrder`, basis $(1,\theta)$, $d=-D$). -/
abbrev maxOrderCM : Subring Ev := maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v

/-- **$E_v$ is `QuadK D Fv`**: the algebra $F_v[\omega]/(\omega^2-d)$, $d=-D$, of `BinaryTorusLocal.lean` is
(definitionally) the one used here, so every statement about `Ev` applies to elements of `QuadK D Fv`. -/
theorem quadK_eq :
    QuadK D (v.adicCompletion F) = Ev := rfl

/-- $d_D=-D$ of `BinaryTorusBase.lean` is the image of $-D\in\mathcal O_F$. -/
theorem dD_eq : dD D = (((-D : 𝓞 F) : 𝓞 F) : F) := by simp

/-- **The maximal order as a subring of `QuadK D Fv`.** -/
abbrev maxOrderK : Subring (QuadK D (v.adicCompletion F)) := maxOrderCM S v

/-- The $F_v$-coordinates (`coordsOf`) of a global integer are the image of its global coordinates under `locVec`. -/
theorem coordsOf_eq (a : 𝓞 E) : coordsOf (sqrtBasis S) v a = locVec v (coordOf S (a : E)) := by
  funext i
  simp [coordsOf, sqrtBasis_repr]

/-- **The localization of $\mathcal O_E$ is the local maximal order.** For $y\in F_v^2$ (the coordinates $y_0+y_1\theta$):
$y\in(\mathcal O_E)_v$ iff $y_0+y_1\omega\in\mathcal O_{E,v}=\{z:\operatorname{tr}z,Nz\in\mathfrak o_v\}$.
*Proof:* ($\Rightarrow$) global integers have integral trace and norm (`isMaxInt_coordsOf`) and $\mathcal O_{E,v}$ is an
$\mathfrak o_v$-module; ($\Leftarrow$) by L1 the coordinates have integral components, so a global integer
approximates them modulo $\mathfrak o_v^2\subseteq(\mathcal O_E)_v$ (`exists_integer_near`). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Lemma, (12.1), p. 61 [unverified]"]
theorem mem_loc_latE_iff (y : Fin 2 → Fv) :
    y ∈ loc v (latE S) ↔ (⟨y 0, y 1⟩ : Ev) ∈ maxOrderCM S v := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, (a : E) = cE S x := ⟨⟨cE S x, (mem_latE S).1 hx⟩, rfl⟩
      have h := isMaxInt_coordsOf (sqrtBasis_zero S) (sqrtBasis_mul_self S) v a
      have e : coordsOf (sqrtBasis S) v a = locVec v x := by
        rw [coordsOf_eq, ha, coordOf_cE]
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      rw [e0, e1] at h
      exact h
    | zero =>
      have : (⟨(0 : Fin 2 → Fv) 0, (0 : Fin 2 → Fv) 1⟩ : Ev) = 0 := by ext <;> simp
      rw [this]; exact Subring.zero_mem _
    | add y y' _ _ h h' =>
      have : (⟨(y + y') 0, (y + y') 1⟩ : Ev) = ⟨y 0, y 1⟩ + ⟨y' 0, y' 1⟩ := by ext <;> simp
      rw [this]; exact Subring.add_mem _ h h'
    | smul c y _ h =>
      have : (⟨(c • y) 0, (c • y) 1⟩ : Ev) = algebraMap Fv Ev (c : Fv) * ⟨y 0, y 1⟩ := by
        refine QuadraticAlgebra.ext ?_ ?_
        · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
            mul_zero, zero_mul, add_zero]
          exact smul_apply_coe v c y 0
        · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
            mul_zero, zero_mul, add_zero]
          exact smul_apply_coe v c y 1
      rw [this]
      exact Subring.mul_mem _ (algebraMap_mem_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v
        ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2)) h
  · intro hy
    have hint : localPi (sqrtBasis S) v y ∈ intPlace (K := E) v := by
      intro w
      have h1 := (mem_maxOrder_iff_forall (sqrtBasis_zero S) (sqrtBasis_mul_self S) v _).1 hy w
      have h2 := quadLocalHom_eq_localPi (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (⟨y 0, y 1⟩ : Ev) w
      have e : (![(⟨y 0, y 1⟩ : Ev).re, (⟨y 0, y 1⟩ : Ev).im] : Fin 2 → Fv) = y := by
        funext i; fin_cases i <;> rfl
      rw [e] at h2
      exact h2 ▸ h1
    obtain ⟨a, ha⟩ := exists_integer_near (sqrtBasis S) v hint
    have h1 : locVec v (coordOf S (a : E)) ∈ loc v (latE S) := locVec_mem_loc v (coordOf_mem_latE S a)
    have h2 : locVec v (coordOf S (a : E)) - y ∈ std v := by
      intro i
      have := ha i
      rw [coordsOf_eq] at this
      simpa using this
    have h3 : y = locVec v (coordOf S (a : E)) - (locVec v (coordOf S (a : E)) - y) := by abel
    rw [h3]
    exact Submodule.sub_mem _ h1 (std_le_loc_latE S v h2)

/-! ### The index $[\mathcal O_{E,v}:R_v]=N(v)^{c_v}$ -/

variable {S v} (L : LocData S v)

/-- **The coordinate map of $\Gamma=\mathfrak o_v[\omega']$ into $E_v$**, $\zeta\mapsto\zeta_0+\zeta_1\omega'$ with
$\omega'=(s\varpi^{-c},\varpi^{-c})$ in the coordinates of $(1,\omega)$ (the map `φ` of `LocData`, as an element of $E_v$). -/
def phiEv : Γ L →+ Ev where
  toFun ζ := ⟨(ζ.re : Fv) + (ζ.im : Fv) * (L.s : Fv) * τv v ^ L.c, (ζ.im : Fv) * τv v ^ L.c⟩
  map_zero' := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  map_add' ζ ζ' := by
    refine QuadraticAlgebra.ext ?_ ?_
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      push_cast
      ring
    · simp only [QuadraticAlgebra.im_add]
      push_cast
      ring

theorem phiEv_eq (ζ : Γ L) : phiEv L ζ = ⟨φ L ζ 0, φ L ζ 1⟩ := rfl

theorem phiEv_injective : Function.Injective (phiEv L) := by
  intro ζ ζ' h
  apply φ_injective L
  funext i
  fin_cases i
  · exact congrArg QuadraticAlgebra.re h
  · exact congrArg QuadraticAlgebra.im h

theorem phiEv_eq_iff (ζ : Γ L) (z : Ev) : phiEv L ζ = z ↔ φ L ζ = ![z.re, z.im] := by
  constructor
  · rintro rfl
    funext i; fin_cases i <;> rfl
  · intro h
    refine QuadraticAlgebra.ext ?_ ?_
    · exact congrFun h 0
    · exact congrFun h 1

theorem mem_maxOrderCM_iff_phiEv (z : Ev) : z ∈ maxOrderCM S v ↔ ∃ ζ : Γ L, phiEv L ζ = z := by
  have h := mem_loc_latE_iff S v ![z.re, z.im]
  have e : (⟨(![z.re, z.im] : Fin 2 → Fv) 0, (![z.re, z.im] : Fin 2 → Fv) 1⟩ : Ev) = z := rfl
  rw [e] at h
  rw [← h, mem_loc_iff_φ L]
  simp only [phiEv_eq_iff]

theorem mem_coordOrderCM_iff_phiEv (z : Ev) :
    z ∈ coordOrder (-D) v ↔ ∃ ζ : Γ L, Loc.πv v ^ L.c ∣ ζ.im ∧ phiEv L ζ = z := by
  constructor
  · intro hz
    obtain ⟨ζ, hζ⟩ := (mem_maxOrderCM_iff_phiEv L z).1
      (coordOrder_le_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hz)
    refine ⟨ζ, (φ_mem_std_iff L ζ).1 ?_, hζ⟩
    rw [(phiEv_eq_iff L ζ z).1 hζ]
    intro i
    have h := (mem_coordOrder_iff v z).1 hz
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  · rintro ⟨ζ, hζ, rfl⟩
    have h := (φ_mem_std_iff L ζ).2 hζ
    rw [mem_coordOrder_iff]
    exact ⟨(by simpa using h 0 : Valued.v (φ L ζ 0) ≤ 1), (by simpa using h 1 : Valued.v (φ L ζ 1) ≤ 1)⟩

/-- The class of the $\omega'$-coordinate modulo $\varpi^c$, $\Gamma\to\mathfrak o/\varpi^c$. -/
def gHom : Γ L →+ Loc.Ok v L.c :=
  AddMonoidHom.mk' (fun ζ => Ideal.Quotient.mk _ ζ.im) (fun ζ ζ' => by
    rw [QuadraticAlgebra.im_add, map_add])

theorem mem_ker_gHom (ζ : Γ L) : ζ ∈ (gHom L).ker ↔ Loc.πv v ^ L.c ∣ ζ.im := by
  rw [AddMonoidHom.mem_ker]
  show Ideal.Quotient.mk _ ζ.im = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem gHom_surjective : Function.Surjective (gHom L) := by
  intro q
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨0, t⟩, rfl⟩

theorem toAddSubgroup_maxOrderCM_eq :
    (maxOrderCM S v).toAddSubgroup = (⊤ : AddSubgroup (Γ L)).map (phiEv L) := by
  ext z
  simp only [Subring.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and,
    mem_maxOrderCM_iff_phiEv L]

theorem toAddSubgroup_coordOrderCM_eq :
    (coordOrder (-D) v).toAddSubgroup = (gHom L).ker.map (phiEv L) := by
  ext z
  simp only [Subring.mem_toAddSubgroup, AddSubgroup.mem_map, mem_ker_gHom L, mem_coordOrderCM_iff_phiEv L]

end Coords

section Index

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Ev" => QuadraticAlgebra (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (((-D : 𝓞 F) : 𝓞 F) : F)) 0

/-- **L2: the local index.** With $c_v$ = `BinaryCM.cv S v` (the exponent of `LocData`, $\Lambda=\mathfrak o_v+\mathfrak o_v\omega'$),
$$[\mathcal O_{E,v} : R_v] = N(v)^{c_v},\qquad R_v=\mathfrak o_v[\omega],\ \omega^2=-D,$$
where $\mathcal O_{E,v}=\{z\in E_v:\operatorname{tr}z, Nz\in\mathfrak o_v\}$ (`maxOrder`) and $R_v=\{x+y\omega : x,y\in\mathfrak o_v\}$
(`coordOrder`). *Proof:* $\mathcal O_{E,v}\leftrightarrow\Lambda$ (`mem_loc_latE_iff`), $\Lambda=\varphi(\mathfrak o_v[\omega'])$ and
$\mathfrak o_v^2=\varphi\{\zeta:\varpi^c\mid\zeta_1\}$, so the quotient is $\mathfrak o_v/\varpi^c$ of order $N(v)^c$. -/
@[kb "siegel1935" "Hilfssatz (local densities of binary forms), the index [L_{E,p} : o_p^2] = N(p)^c [unverified]"]
theorem relIndex_maxOrder_coordOrder :
    (coordOrder (-D) v).toAddSubgroup.relIndex (maxOrderCM S v).toAddSubgroup = Loc.qv v ^ BinaryCM.cv S v := by
  rw [toAddSubgroup_maxOrderCM_eq (BinaryCM.locD S v), toAddSubgroup_coordOrderCM_eq (BinaryCM.locD S v),
    AddSubgroup.relIndex_map_map_of_injective _ _ (phiEv_injective (BinaryCM.locD S v)), AddSubgroup.relIndex_top_right,
    AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (gHom_surjective (BinaryCM.locD S v)), AddSubgroup.card_top]
  exact Loc.card_Ok v (BinaryCM.locD S v).c

/-- **$\varpi^{c_v}\mathcal O_{E,v}\subseteq R_v$**, $\varpi$ = `πF v`, $c_v$ = `BinaryCM.cv S v`:
$\varpi^c(\zeta_0+\zeta_1\omega')$ has coordinates $\varpi^c\zeta_0+\zeta_1s,\ \zeta_1\in\mathfrak o_v$. -/
theorem smul_phiEv_mem (L : LocData S v) (ζ : Γ L) :
    algebraMap Fv Ev (πF v ^ L.c) * phiEv L ζ ∈ coordOrder (-D) v := by
  have hπ : πF v ^ L.c * τv v ^ L.c = 1 := by
    rw [τv, inv_pow]; exact mul_inv_cancel₀ (pow_ne_zero _ (πF_ne_zero v))
  have e : algebraMap Fv Ev (πF v ^ L.c) * phiEv L ζ =
      ⟨(((Loc.πv v ^ L.c * ζ.re + ζ.im * L.s : v.adicCompletionIntegers F)) : Fv), (ζ.im : Fv)⟩ := by
    refine QuadraticAlgebra.ext ?_ ?_
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
        mul_zero, zero_mul, add_zero]
      show πF v ^ L.c * ((ζ.re : Fv) + (ζ.im : Fv) * (L.s : Fv) * τv v ^ L.c) = _
      push_cast
      linear_combination ((ζ.im : Fv) * (L.s : Fv)) * hπ
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
        mul_zero, zero_mul, add_zero]
      show πF v ^ L.c * ((ζ.im : Fv) * τv v ^ L.c) = _
      linear_combination (ζ.im : Fv) * hπ
  rw [e, mem_coordOrder_iff v]
  exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (Loc.πv v ^ L.c * ζ.re + ζ.im * L.s).2,
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ζ.im.2⟩

theorem smul_mem_coordOrder {y : Ev} (hy : y ∈ maxOrderCM S v) :
    algebraMap Fv Ev (πF v ^ BinaryCM.cv S v) * y ∈ coordOrder (-D) v := by
  obtain ⟨ζ, rfl⟩ := (mem_maxOrderCM_iff_phiEv (BinaryCM.locD S v) y).1 hy
  exact smul_phiEv_mem S v (BinaryCM.locD S v) ζ

/-- **L2, the index of principal units.** For $k\ge\max(1,c_v)$,
$$[\,1+\varpi^k\mathcal O_{E,v} : 1+\varpi^kR_v\,] = N(v)^{c_v},$$
$\varpi$ = `πF v` (= `NF.π v`), via the isomorphism $1+\varpi^ky\mapsto y\bmod R_v$ onto $\mathcal O_{E,v}/R_v$
(`relIndex_unitWindow`, `relIndex_maxOrder_coordOrder`, `smul_mem_coordOrder`). -/
@[kb "siegel1935" "Hilfssatz (local densities of binary forms), conductor index [unverified]"]
theorem relIndex_unitWindow_cv {k : ℕ} (hk : 1 ≤ k) (hkc : BinaryCM.cv S v ≤ k) :
    (unitWindow (-D) v (πF v) k (coordOrder (-D) v)).relIndex
        (unitWindow (-D) v (πF v) k (maxOrderCM S v)) = Loc.qv v ^ BinaryCM.cv S v := by
  rw [relIndex_unitWindow (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (valued_πF v) hk ?_,
    relIndex_maxOrder_coordOrder S v]
  intro y hy
  have h1 := smul_mem_coordOrder S v hy
  have h2 : πF v ^ k = πF v ^ (k - BinaryCM.cv S v) * πF v ^ BinaryCM.cv S v := by
    rw [← pow_add]; congr 1; omega
  have h3 : algebraMap Fv Ev (πF v ^ (k - BinaryCM.cv S v)) ∈ coordOrder (-D) v := by
    refine CL.algebraMap (k := 0) ?_
    rw [map_pow, valued_πF, ← WithZero.exp_nsmul]
    exact (exp_le_exp.2 (by simp)).trans_eq exp_zero
  rw [h2, map_mul, mul_assoc]
  exact Subring.mul_mem _ h3 h1

/-- Away from $2D$ the local order is maximal: $[\mathcal O_{E,v}:R_v] = 1$ if $2D\notin\mathfrak p_v$. -/
theorem relIndex_maxOrder_coordOrder_eq_one (hv : (2 * D : 𝓞 F) ∉ v.asIdeal) :
    (coordOrder (-D) v).toAddSubgroup.relIndex (maxOrderCM S v).toAddSubgroup = 1 := by
  rw [relIndex_maxOrder_coordOrder, cv_eq_zero S (loc_latE_of_not_mem S v hv), pow_zero]

end Index

/-! ### L4: the product of the local indices and the discriminant -/

section Global

/-- **The local index** $i_v = [\mathcal O_{E,v}:R_v]$, as a natural number: $1$ for $2D\notin\mathfrak p_v$, $N(v)^{c_v}$ always. -/
def localIndex (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (coordOrder (-D) v).toAddSubgroup.relIndex (maxOrderCM S v).toAddSubgroup

theorem localIndex_eq (v : HeightOneSpectrum (𝓞 F)) : localIndex S v = Loc.qv v ^ BinaryCM.cv S v :=
  relIndex_maxOrder_coordOrder S v

theorem localIndex_eq_one {v : HeightOneSpectrum (𝓞 F)} (hv : (2 * D : 𝓞 F) ∉ v.asIdeal) : localIndex S v = 1 :=
  relIndex_maxOrder_coordOrder_eq_one S v hv

/-- **L4, the conductor.** For a finite set $U$ of places containing every $\mathfrak p_v\ni2D$, the conductor
$\mathfrak f$ of $\mathcal O_F[\theta]$ in $\mathcal O_E$ has absolute norm $\bigl(\prod_{v\in U}[\mathcal O_{E,v}:R_v]\bigr)^2$. -/
theorem absNorm_conductor_eq_prod_localIndex {U : Finset (HeightOneSpectrum (𝓞 F))}
    (hU : ∀ v ∉ U, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    Ideal.absNorm (conductor (𝓞 F) (θO S)) = (∏ v ∈ U, localIndex S v) ^ 2 := by
  have hcU : ∀ v ∉ U, BinaryCM.cv S v = 0 := fun v hv =>
    cv_eq_zero S (loc_latE_of_not_mem S v (hU v hv))
  rw [absNorm_conductor hcU]
  simp only [localIndex_eq]

/-- **L4: $|d_E|\,\bigl(\prod_vq^{c_v}\bigr)^2 = 4^{[F:\mathbb Q]}|d_F|^2|N_{F/\mathbb Q}D|$**, with
$\prod_vq^{c_v}=\prod_v[\mathcal O_{E,v}:R_v]$ over any finite set $U$ containing the places dividing $2D$
(the other factors are $1$, `localIndex_eq_one`). Here $d_E$, $d_F$ are the absolute discriminants, $R_v=\mathfrak o_v[\sqrt{-D}]$
and $\mathcal O_{E,v}=\{z:\operatorname{tr}z,Nz\in\mathfrak o_v\}$. -/
@[kb "neukirch1999" "Ch. III §2, Prop. 2.4, Thm. 2.9 (discriminant of an order) [unverified]"]
theorem discr_mul_prod_localIndex_sq {U : Finset (HeightOneSpectrum (𝓞 F))}
    (hU : ∀ v ∉ U, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    |(discr E : ℝ)| * ((∏ v ∈ U, localIndex S v : ℕ) : ℝ) ^ 2 =
      4 ^ Module.finrank ℚ F * |(discr F : ℝ)| ^ 2 * |(Algebra.norm ℚ (dF D) : ℝ)| := by
  have h := discr_relation (S := S) hU
  simp only [localIndex_eq]
  push_cast
  exact h

/-- **L4 with the product over all finite places** (a finite product, as $i_v=1$ off $2D$). -/
theorem discr_mul_finprod_localIndex_sq :
    |(discr E : ℝ)| * ((∏ᶠ v : HeightOneSpectrum (𝓞 F), localIndex S v : ℕ) : ℝ) ^ 2 =
      4 ^ Module.finrank ℚ F * |(discr F : ℝ)| ^ 2 * |(Algebra.norm ℚ (dF D) : ℝ)| := by
  classical
  have hne : (2 * D : 𝓞 F) ≠ 0 := two_mul_ne_zero S
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (2 * D : 𝓞 F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {2 * D}) (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)).subset (fun v hv => ?_)
    show v.asIdeal ∣ Ideal.span {2 * D}
    rw [Ideal.dvd_span_singleton]
    exact hv
  have hU : ∀ v ∉ hfin.toFinset, (2 * D : 𝓞 F) ∉ v.asIdeal := fun v hv h =>
    hv (hfin.mem_toFinset.2 h)
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => localIndex S v) ⊆ hfin.toFinset := by
    intro v hv
    by_contra hvU
    exact hv (localIndex_eq_one S (hU v hvU))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact discr_mul_prod_localIndex_sq S hU

end Global

end CM

end QuadFormsKB.Tamagawa.Measure.Weil
