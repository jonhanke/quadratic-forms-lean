import QuadFormsKB.Tamagawa.Measure.Weil.BinaryComparisonGlue
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryFiniteLocalCM
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryCongruence
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryWindow
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.ChartMeasures
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchRatio
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSAssembly

/-!
# The finite factor of the measure comparison for the binary torus: the fibre function

**Layer:** $F$ a number field, $D\in\mathcal O_F\setminus\{0\}$, $d=-D$ (`dD D`), $E=F(\theta)$ with $\theta^2=-D$ (`SqrtData D E`),
the basis $(1,\theta)$ of $E/F$ (`sqrtBasis`), $Q_0=\langle1,D\rangle$ (`diagForm1 D`). Indices are 0-based. For a finite
set $S$ of finite places of $F$ and levels $k_v\ge1$ ($v\in S$) we compare the finite part of the fibration over the norm-one
torus: the finite idele box $A_f\subseteq\mathbb A_{E,f}^\times$, the idele box $N_F\subseteq\mathbb A_{F,f}^\times$ and the box
$K'\subseteq SO(V)(\mathbb A_f)$.

**Defines**
* `winF k v` $=1+\varpi_v^{k_v}\mathfrak o_v$ and `boxF S k` $=N_F=\prod_{v\in S}(1+\varpi_v^{k_v}\mathfrak o_v)\times\prod_{v\notin S}\mathfrak o_v^\times$
  (an idele box of $F$, `ideleBox`);
* `winE E k w` $=\{r : v_w(r-1)\le v_w(\varpi_v)^{k_v}\}$ at a place $w\mid v$ of $E$ and `boxE E S k` $=A_f$: this window at the places
  of $E$ over $S$, units $\mathcal O_w^\times$ elsewhere;
* the local groups in $E_v^\times=(F_v[\omega])^\times$: `winO S k v` $=1+\varpi_v^{k_v}\mathcal O_{E,v}$ (`unitWindow` of the
  maximal order), `umax S v` $=\mathcal O_{E,v}^\times$ (the units whose components at all places over $v$ are units), and
  `Tloc S Sfin k v` $=T_v$ (the window if $v\in S$, `umax` otherwise);
* `Uloc S k v` $=U_v=\mathrm{tor}(1+\varpi_v^{k_v}\mathcal O_{E,v})\subseteq SO(V)(F_v)$ and
  `Kp S Sfin k` $=K'=\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)$ (`boxSO`).

**Proves**
* `mem_boxE_iff`: for $g\in(E\otimes\mathbb A_{F,f})^\times$ and $c\in\mathbb A_{F,f}^\times$, the product $\Theta(g)\,\iota(c)$
  lies in $A_f$ iff $g_v\,c_v\in T_v$ for every finite place $v$ of $F$ (the $w$-component of $\Theta(g)\,\iota(c)$ is
  $\varphi_w(g_vc_v)$, `unitAt_comp`; windows via `window_iff`, units via `isMaxInt_and_norm_eq_one_iff`);
* `scalar_mem_Tloc_iff`: a scalar $r\in F_v^\times$ lies in $T_v$ iff $r\in1+\varpi_v^{k_v}\mathfrak o_v$ ($v\in S$), resp.
  $r\in\mathfrak o_v^\times$ ($v\notin S$) (because $\mathcal O_{E,v}\cap F_v=\mathfrak o_v$);
* `exists_lift`: every $x\in K'$ is $\mathrm{tor}(g)$ with $g_v\in T_v$ for all $v$ (local lifts: the definition of $U_v$ at
  $v\in S$, integral Hilbert 90 `exists_integral_lift` at $v\notin S$ where $2D\notin\mathfrak p_v$; glued by
  `exists_quadFin_unit`);
* **`fibFinSO_eq`**:$K_f(x)=\mu_{f,F}\{c:\Theta(g)\iota(c)\in A_f\}=\mu_{f,F}(N_F)\cdot\mathbf 1_{K'}(x)$ for
  $\mathrm{tor}(g)=x$ (a translate of $N_F$ if $x\in K'$, empty otherwise: `torFin_mem_Kp_of_mem_boxE`).

The values of the measures and the finite ratio are in `BinaryFiniteGlueValues.lean`.
Source: Weil, *Adeles and Algebraic Groups*, §2.3 and Thm 2.3.1 [unverified locators];
Cassels–Fröhlich, Ch. II (Cassels), §10 (10.2), §12 Lemma [unverified].
-/

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero Matrix QuadFormsKB.Lattices
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa LocalDensity QuadFormsKB.Tamagawa.BinaryCM QuadFormsKB.Tamagawa.BinaryNormOne
  QuadFormsKB.HilbertModular

theorem ite_of_cond {α : Type*} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp only [h, ↓reduceIte]

theorem ite_of_not_cond {α : Type*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp only [h, ↓reduceIte]

section Setup

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)

/-- The relation $\delta^2 = d_D$ for the basis $(1,\theta)$, in the form `quadFinBC` wants. -/
theorem hdD : sqrtBasis S 1 * sqrtBasis S 1 = algebraMap F E (dD D) := by
  rw [sqrtBasis_one, θ_sq, dD, map_neg]

variable (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)

/-- The window $1+\varpi_v^{k_v}\mathfrak o_v$ in $F_v^\times$. -/
def winF (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F)ˣ :=
  {r | Valued.v ((r : v.adicCompletion F) - 1) ≤ exp (-(k v : ℤ))}

/-- The box $N_F$ in $\mathbb A_{F,f}^\times$: windows at $v \in S$, units elsewhere. -/
def boxF : Set (FiniteAdeleRing (𝓞 F) F)ˣ := ideleBox Sfin (winF k)

variable (E) in
/-- The window at a place $w$ of $E$, over $v$: $\{r : v_w(r-1)\le v_w(\varpi_v)^{k_v}\}$. -/
def winE (w : HeightOneSpectrum (𝓞 E)) : Set (w.adicCompletion E)ˣ :=
  {r | Valued.v ((r : w.adicCompletion E) - 1) ≤
    Valued.v (localRingHom (underPlace (k := F) w) w rfl (πF (underPlace (k := F) w))) ^ k (underPlace (k := F) w)}

variable (E) in
/-- The box $A_f$ in $\mathbb A_{E,f}^\times$: windows at the places of $E$ over $S$ (`nsBadK`), units elsewhere. -/
def boxE : Set (FiniteAdeleRing (𝓞 E) E)ˣ := ideleBox (nsBadK (K := E) Sfin) (winE E k)

end Setup

section Local

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)
  (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **The local map $\varphi_w : E_v = F_v[\omega]\to E_w$** ($w\mid v$), $x+y\omega\mapsto\varphi_w(x)+\theta\varphi_w(y)$
(`qlh`), with source written as `QuadK D Fv`. -/
def qh (w : PlaceSet (K := E) v) : QuadK D Fv →+* w.1.adicCompletion E :=
  qlh (sqrtBasis_mul_self S) v w

theorem qh_unit_inv (w : PlaceSet (K := E) v) (a : (QuadK D Fv)ˣ) :
    qh S v w (((a⁻¹ : (QuadK D Fv)ˣ)) : QuadK D Fv) = (qh S v w (a : QuadK D Fv))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

/-- **The units $\mathcal O_{E,v}^\times$ of the maximal order**, as the units all of whose components $\varphi_w(z)$ have
absolute value $1$ (`mem_umax_iff`: $z\in\mathcal O_{E,v}$ and $Nz\in\mathfrak o_v^\times$). -/
def umax : Subgroup (QuadK D Fv)ˣ where
  carrier := {z | ∀ w : PlaceSet (K := E) v, Valued.v (qh S v w (z : QuadK D Fv)) = 1}
  mul_mem' := by
    intro a b ha hb w
    rw [Units.val_mul, map_mul, map_mul, ha w, hb w, one_mul]
  one_mem' := by
    intro w
    rw [Units.val_one, map_one, map_one]
  inv_mem' := by
    intro a ha w
    rw [qh_unit_inv, map_inv₀, ha w, inv_one]

theorem mem_umax_iff (z : (QuadK D Fv)ˣ) :
    z ∈ umax S v ↔ IsMaxInt (-D) v (z : QuadK D Fv) ∧ Valued.v (QuadraticAlgebra.norm (z : QuadK D Fv)) = 1 :=
  (isMaxInt_and_norm_eq_one_iff (sqrtBasis_zero S) (sqrtBasis_mul_self S) v).symm

/-- **The window subgroup $1+\varpi^kO_{E,v}$**. -/
def winO : Subgroup (QuadK D Fv)ˣ := unitWindow (-D) v (πF v) (k v) (maxOrderCM S v)

open Classical in
/-- **The local factor of the box $A_f$** at $v$ (a subgroup of $E_v^\times$): the window at $v \in S$, $\mathcal O_{E,v}^\times$
elsewhere. -/
def Tloc : Subgroup (QuadK D Fv)ˣ := if v ∈ Sfin then winO S k v else umax S v

/-- **The unit version of $\varphi_w$** ($w\mid v$): $E_v^\times\to E_w^\times$. -/
def phiU (w : HeightOneSpectrum (𝓞 E)) (h : underPlace (k := F) w = v) : (QuadK D Fv)ˣ →* (w.adicCompletion E)ˣ :=
  Units.map (quadLocalHom (sqrtBasis_mul_self S) v w h : QuadK D Fv →+* w.adicCompletion E).toMonoidHom

theorem phiU_val (w : HeightOneSpectrum (𝓞 E)) (h : underPlace (k := F) w = v) (z : (QuadK D Fv)ˣ) :
    ((phiU S v w h z : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      quadLocalHom (sqrtBasis_mul_self S) v w h (z : QuadK D Fv) := rfl

/-- **The $w$-component of $\Theta(g)$** ($g\in(E\otimes\mathbb A_{F,f})^\times$, $\Theta$ = `quadFinBC`) is $\varphi_w$ of the
$v$-component of $g$. -/
theorem unitAt_quadFinBC (g : (QuadFin F (dD D))ˣ) (w : HeightOneSpectrum (𝓞 E)) (h : underPlace (k := F) w = v) :
    unitAt (Units.map (quadFinBC (hdD S)).toMonoidHom g) w = phiU S v w h (unitAtD (dD D) v g) := by
  apply Units.ext
  rw [unitAt_val]
  show (finMap F E (g : QuadFin F (dD D)).re) w +
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (sqrtBasis S 1)) w) * (finMap F E (g : QuadFin F (dD D)).im) w = _
  rw [finMap_apply_over v w h, finMap_apply_over v w h]
  rfl

/-- **The $w$-component of $\iota(c)$** ($c\in\mathbb A_{F,f}^\times$) is $\varphi_w$ of the scalar $c_v$. -/
theorem unitAt_finMap (c : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 E)) (h : underPlace (k := F) w = v) :
    unitAt (Units.map (finMap F E).toMonoidHom c) w =
      phiU S v w h (Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom (unitAt c v)) := by
  apply Units.ext
  rw [unitAt_val, phiU_val]
  change (finMap F E (c : FiniteAdeleRing (𝓞 F) F)) w = _
  rw [finMap_apply_over v w h]
  exact (quadLocalHom_algebraMap (sqrtBasis_mul_self S) v w h _).symm

/-- **The window subgroup in terms of the places** ($k_v\ge1$): $z\in1+\varpi^kO_{E,v}$ iff every component
$\varphi_w(z)$, $w\mid v$, lies in $1+\varpi^k\mathcal O_w$ (L3, `window_iff`). -/
theorem mem_win_iff (hk : 1 ≤ k v) (z : (QuadK D Fv)ˣ) :
    z ∈ winO S k v ↔ ∀ w : PlaceSet (K := E) v,
      Valued.v (qh S v w (z : QuadK D Fv) - 1) ≤ Valued.v (localRingHom v w.1 w.2 (πF v)) ^ k v := by
  have hw := window_iff (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (valued_πF v) (k v) (z : QuadK D Fv)
  constructor
  · rintro ⟨-, -, y, hy, hyu⟩
    exact hw.2 ⟨y, hy, by rw [← hyu]; ring⟩
  · intro h
    obtain ⟨y, hy, hzy⟩ := hw.1 h
    obtain ⟨u, hu, hue⟩ := exists_mem_unitWindow (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (valued_πF v) hk hy
    have : u = z := Units.ext (hue.trans hzy.symm)
    rw [← this]; exact hu

theorem unitAt_comp (g : (QuadFin F (dD D))ˣ) (c : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 E))
    (h : underPlace (k := F) w = v) :
    unitAt (Units.map (quadFinBC (hdD S)).toMonoidHom g * Units.map (finMap F E).toMonoidHom c) w =
      phiU S v w h (unitAtD (dD D) v g * Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom (unitAt c v)) := by
  rw [unitAt_mul, unitAt_quadFinBC S v g w h, unitAt_finMap S v c w h, map_mul]

/-- **Membership in the box $A_f$ of a product $\Theta(g)\,\iota(c)$ is a local condition**: for every $v$, the unit
$g_v\,c_v\in E_v^\times$ lies in `Tloc` (window at $v\in S$, $\mathcal O_{E,v}^\times$ elsewhere). -/
theorem mem_boxE_iff (hk : ∀ v ∈ Sfin, 1 ≤ k v) (g : (QuadFin F (dD D))ˣ) (c : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Units.map (quadFinBC (hdD S)).toMonoidHom g * Units.map (finMap F E).toMonoidHom c ∈ boxE E Sfin k ↔
      ∀ v : HeightOneSpectrum (𝓞 F), unitAtD (dD D) v g *
        Units.map (algebraMap (v.adicCompletion F) (QuadK D (v.adicCompletion F))).toMonoidHom (unitAt c v) ∈
          Tloc S Sfin k v := by
  classical
  constructor
  · intro H v
    by_cases hv : v ∈ Sfin
    · rw [Tloc, ite_of_cond hv, mem_win_iff S k v (hk v hv)]
      rintro ⟨w, hw⟩
      have hH : unitAt (Units.map (quadFinBC (hdD S)).toMonoidHom g * Units.map (finMap F E).toMonoidHom c) w ∈
          (if w ∈ nsBadK (K := E) Sfin then winE E k w else unitsVSub w) := H w
      subst hw
      rw [ite_of_cond (mem_nsBadK.2 hv), unitAt_comp S _ g c w rfl] at hH
      exact hH
    · rw [Tloc, ite_of_not_cond hv]
      intro w
      have hH : unitAt (Units.map (quadFinBC (hdD S)).toMonoidHom g * Units.map (finMap F E).toMonoidHom c) w.1 ∈
          (if w.1 ∈ nsBadK (K := E) Sfin then winE E k w.1 else unitsVSub w.1) := H w.1
      obtain ⟨w, hw⟩ := w
      subst hw
      rw [ite_of_not_cond (fun h => hv (mem_nsBadK.1 h)), unitAt_comp S _ g c w rfl] at hH
      exact hH
  · intro H w
    have hz := H (underPlace (k := F) w)
    by_cases hv : underPlace (k := F) w ∈ Sfin
    · rw [ite_of_cond (mem_nsBadK.2 hv)]
      rw [Tloc, ite_of_cond hv, mem_win_iff S k _ (hk _ hv)] at hz
      rw [unitAt_comp S _ g c w rfl]
      exact hz ⟨w, rfl⟩
    · rw [ite_of_not_cond (fun h => hv (mem_nsBadK.1 h))]
      rw [Tloc, ite_of_not_cond hv] at hz
      rw [unitAt_comp S _ g c w rfl]
      exact hz ⟨w, rfl⟩

end Local

/-! ### Scalars: $N_F$ against `Tloc` -/

section Scalars

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)
  (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem le_one_of_mul_self_le_one {x : ℤᵐ⁰} (h : x * x ≤ 1) : x ≤ 1 := by
  by_contra hx
  push Not at hx
  exact absurd h (not_le.2 (one_lt_mul_of_lt_of_le hx hx.le))

theorem eq_one_of_mul_self_eq_one {x : ℤᵐ⁰} (h : x * x = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (mul_lt_one_of_lt_of_le hlt hlt.le))
  · exact heq
  · exact absurd h (ne_of_gt (one_lt_mul_of_lt_of_le hgt hgt.le))

/-- The scalar $r\in F_v^\times$ as a unit of $E_v = F_v[\omega]$. -/
abbrev scalU (r : Fv) : QuadK D Fv := algebraMap Fv (QuadK D Fv) r

theorem norm_scal (r : Fv) : QuadraticAlgebra.norm (algebraMap Fv (QuadK D Fv) r) = r * r := by
  rw [QuadraticAlgebra.norm_algebraMap, sq]

/-- **A scalar lies in $\mathcal O_{E,v}^\times$ iff it is a unit of $\mathfrak o_v$.** -/
theorem scalar_mem_umax_iff (r : (v.adicCompletion F)ˣ) :
    Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r ∈ umax S v ↔ r ∈ unitsVSub v := by
  rw [mem_umax_iff]
  have hn : QuadraticAlgebra.norm ((Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r : (QuadK D Fv)ˣ) : QuadK D Fv) =
      (r : Fv) * (r : Fv) := norm_scal v (r : Fv)
  rw [hn, map_mul]
  constructor
  · rintro ⟨-, h⟩
    exact eq_one_of_mul_self_eq_one h
  · intro h
    have h' : Valued.v (r : Fv) = 1 := h
    refine ⟨?_, by rw [h', one_mul]⟩
    have hz : ((Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r : (QuadK D Fv)ˣ) : QuadK D Fv) =
        (⟨(r : Fv), 0⟩ : QuadK D Fv) := by
      refine QuadraticAlgebra.ext ?_ ?_ <;> simp
    rw [hz]
    refine (isMaxInt_mk_iff (d := -D) v (r : Fv) 0).2 ⟨?_, ?_⟩
    · rw [map_mul, h', mul_one]; exact valued_two_le_one v
    · simp only [mul_zero, sub_zero, map_mul, h', mul_one, le_refl]

/-- **The scalar condition at a place of $S$**: $\iota(r)\in1+\varpi^kO_{E,v}$ iff $r\in1+\varpi^k\mathfrak o_v$
(because $O_{E,v}\cap F_v = \mathfrak o_v$). -/
theorem scalar_mem_win_iff (hk : 1 ≤ k v) (r : (v.adicCompletion F)ˣ) :
    Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r ∈ winO S k v ↔ r ∈ winF k v := by
  have hϖ0 : πF v ≠ 0 := πF_ne_zero v
  have hπk : Valued.v (πF v ^ k v) = exp (-(k v : ℤ)) := valued_πF_pow v (k v)
  constructor
  · rintro ⟨-, -, y, hy, hyu⟩
    have hre := congrArg QuadraticAlgebra.re hyu
    have him := congrArg QuadraticAlgebra.im hyu
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero, sub_zero] at hre him
    have himy : y.im = 0 := by
      have : (πF v ^ k v) * y.im = 0 := him.symm
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (pow_ne_zero _ hϖ0)
      · exact h
    have hy2 : (y : QuadK D Fv) = ⟨y.re, 0⟩ := QuadraticAlgebra.ext rfl himy
    rw [hy2] at hy
    have hy3 := ((isMaxInt_mk_iff (d := -D) v y.re 0).1 hy).2
    simp only [mul_zero, sub_zero] at hy3
    have hyre : Valued.v y.re ≤ 1 := le_one_of_mul_self_le_one (by rwa [← map_mul])
    have hr : (r : Fv) - 1 = πF v ^ k v * y.re := by
      have h2 : ((Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r : (QuadK D Fv)ˣ) : QuadK D Fv).re = r := rfl
      rw [h2] at hre
      exact hre
    show Valued.v ((r : Fv) - 1) ≤ exp (-(k v : ℤ))
    rw [hr, map_mul, hπk]
    calc exp (-(k v : ℤ)) * Valued.v y.re ≤ exp (-(k v : ℤ)) * 1 := mul_le_mul' le_rfl hyre
      _ = _ := mul_one _
  · intro hr
    set y0 : Fv := (πF v ^ k v)⁻¹ * ((r : Fv) - 1) with hy0
    have hy0v : Valued.v y0 ≤ 1 := by
      rw [hy0, map_mul, map_inv₀, hπk]
      calc (exp (-(k v : ℤ)))⁻¹ * Valued.v ((r : Fv) - 1) ≤ (exp (-(k v : ℤ)))⁻¹ * exp (-(k v : ℤ)) :=
            mul_le_mul' le_rfl hr
        _ = 1 := inv_mul_cancel₀ exp_ne_zero
    obtain ⟨u, hu, hue⟩ := exists_mem_unitWindow (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (valued_πF v) hk
      (algebraMap_mem_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hy0v)
    have hprod : πF v ^ k v * y0 = (r : Fv) - 1 := by
      rw [hy0, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), one_mul]
    have hur : u = Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r := by
      apply Units.ext
      rw [hue]
      show _ = algebraMap Fv (QuadK D Fv) (r : Fv)
      rw [← map_mul, hprod, map_sub, map_one, add_sub_cancel]
      rfl
    rw [← hur]
    exact hu

open Classical in
/-- **The scalar condition for `Tloc`**: $\iota(r)\in T_v$ iff $r$ lies in the window ($v\in S$) or is a unit ($v\notin S$). -/
theorem scalar_mem_Tloc_iff (hk : ∀ v ∈ Sfin, 1 ≤ k v) (r : (v.adicCompletion F)ˣ) :
    Units.map (algebraMap Fv (QuadK D Fv)).toMonoidHom r ∈ Tloc S Sfin k v ↔
      r ∈ (if v ∈ Sfin then winF k v else unitsVSub v) := by
  by_cases hv : v ∈ Sfin
  · rw [Tloc, ite_of_cond hv, ite_of_cond hv]
    exact scalar_mem_win_iff S k v (hk v hv) r
  · rw [Tloc, ite_of_not_cond hv, ite_of_not_cond hv]
    exact scalar_mem_umax_iff S v r

end Scalars

/-! ### The torus side: $K'$, good places, lifts -/

section TorusSide

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)
  (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- A integer outside $\mathfrak p_v$ has absolute value $1$ at $v$. -/
theorem valued_eq_one_of_not_mem {x : 𝓞 F} (h : x ∉ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1 := by
  have h1 := valued_algebraMap_le_one x v
  have h2 : ¬ v.valuation F (x : F) < 1 := fun hlt => h ((v.valuation_lt_one_iff_mem (K := F) x).1 hlt)
  rw [valued_algebraMap] at h1 ⊢
  exact le_antisymm h1 (not_lt.1 h2)

/-- At a place with $2D\notin\mathfrak p_v$: $|2|_v = 1$ and $|D|_v = 1$. -/
theorem valued_two_D_eq_one (hv : (2 * D : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (2 : Fv) = 1 ∧ Valued.v (dIn D Fv) = 1 := by
  refine ⟨?_, valued_eq_one_of_not_mem v (fun h => hv (v.asIdeal.mul_mem_left _ h))⟩
  have := valued_eq_one_of_not_mem v (x := 2) (fun h => hv (v.asIdeal.mul_mem_right _ h))
  rwa [show (((2 : 𝓞 F)) : F) = 2 from rfl, map_ofNat] at this

/-- **Coordinates of an element of $\mathcal O_{E,v}^\times$ at a place with $2D\notin\mathfrak p_v$ are integral.** -/
theorem coords_le_one_of_umax (h2 : Valued.v (2 : Fv) = 1) (hDv : Valued.v (dIn D Fv) = 1) {z : (QuadK D Fv)ˣ}
    (hz : z ∈ umax S v) : Valued.v (z : QuadK D Fv).re ≤ 1 ∧ Valued.v (z : QuadK D Fv).im ≤ 1 := by
  obtain ⟨hI, -⟩ := (mem_umax_iff S v z).1 hz
  have hm := (isMaxInt_mk_iff (d := -D) v (z : QuadK D Fv).re (z : QuadK D Fv).im).1 hI
  have hre : Valued.v (z : QuadK D Fv).re ≤ 1 := by
    have := hm.1
    rwa [map_mul, h2, one_mul] at this
  refine ⟨hre, ?_⟩
  have hdv : Valued.v (algebraMap F Fv (((-D : 𝓞 F) : 𝓞 F) : F)) = 1 := by
    change Valued.v (algebraMap F Fv (dD D)) = 1
    rw [dD_algebraMap, Valuation.map_neg, hDv]
  set x := (z : QuadK D Fv).re
  set y := (z : QuadK D Fv).im
  have hxx : Valued.v (x * x) ≤ 1 := by rw [map_mul]; exact mul_le_one' hre hre
  have hdyy : Valued.v (algebraMap F Fv (((-D : 𝓞 F) : 𝓞 F) : F) * y * y) ≤ 1 := by
    have e : algebraMap F Fv (((-D : 𝓞 F) : 𝓞 F) : F) * y * y =
        x * x - (x * x - algebraMap F Fv (((-D : 𝓞 F) : 𝓞 F) : F) * y * y) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hxx hm.2)
  rw [map_mul, map_mul, hdv, one_mul] at hdyy
  exact le_one_of_mul_self_le_one hdyy

/-- **`torSOK` of a unit of $\mathcal O_{E,v}^\times$ stabilizes $\mathfrak o_v^2$** (at a place with $2D\notin\mathfrak p_v$). -/
theorem torSOK_umax_mem_stdStab (h2 : Valued.v (2 : Fv) = 1) (hDv : Valued.v (dIn D Fv) = 1) {z : (QuadK D Fv)ˣ}
    (hz : z ∈ umax S v) :
    ((torSOK D Fv z : soSub (formF (diagForm1 D)) Fv) : orthGroup (formF (diagForm1 D)) Fv) ∈
      stdStab (formF (diagForm1 D)) v := by
  obtain ⟨h1, h2'⟩ := coords_le_one_of_umax S v h2 hDv hz
  obtain ⟨h3, h4⟩ := coords_le_one_of_umax S v h2 hDv (inv_mem hz)
  exact torOrthK_mem_stdStab D v h1 h2' h3 h4

/-- **Integral lifts at a good place**: an element of $SO(L_v)$ is $\mathrm{tor}(z)$ for some $z\in\mathcal O_{E,v}^\times$. -/
theorem exists_umax_lift (h2 : Valued.v (2 : Fv) = 1) (hDv : Valued.v (dIn D Fv) = 1)
    (g : soSub (formF (diagForm1 D)) Fv)
    (hg : (g : orthGroup (formF (diagForm1 D)) Fv) ∈ stdStab (formF (diagForm1 D)) v) :
    ∃ z ∈ umax S v, torSOK D Fv z = g := by
  obtain ⟨z, hz, h1, h2', h3, h4⟩ := exists_integral_lift D v h2 hDv g hg
  refine ⟨z, ?_, hz⟩
  rw [mem_umax_iff]
  refine ⟨⟨?_, valued_norm_le_one D v h1 h2'⟩, valued_norm_eq_one D v h1 h2' h3 h4⟩
  show Valued.v (QuadraticAlgebra.trace (z : QuadK D Fv)) ≤ 1
  rw [QuadraticAlgebra.trace_def, zero_mul, add_zero, map_mul]
  exact mul_le_one' (valued_two_le_one v) h1

/-- **A unit of $E\otimes\mathbb A_{F,f}$ with prescribed local components**, given integral coordinates of $t_v$ and $t_v^{-1}$
for almost all $v$. -/
theorem exists_quadFin_unit (t : ∀ v : HeightOneSpectrum (𝓞 F), (QuadK D (v.adicCompletion F))ˣ)
    (hev : ∀ᶠ v in Filter.cofinite, Valued.v (t v : QuadK D (v.adicCompletion F)).re ≤ 1 ∧
      Valued.v (t v : QuadK D (v.adicCompletion F)).im ≤ 1 ∧
      Valued.v ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.re ≤ 1 ∧
      Valued.v ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.im ≤ 1) :
    ∃ g : (QuadFin F (dD D))ˣ, ∀ v, unitAtD (dD D) v g = t v := by
  have hO : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F), Valued.v y ≤ 1 →
      y ∈ v.adicCompletionIntegers F :=
    fun v y hy => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hy
  let x : QuadFin F (dD D) :=
    ⟨mkAF (fun v => (t v : QuadK D (v.adicCompletion F)).re) (by filter_upwards [hev] with v hv; exact hO v _ hv.1),
     mkAF (fun v => (t v : QuadK D (v.adicCompletion F)).im) (by filter_upwards [hev] with v hv; exact hO v _ hv.2.1)⟩
  let y : QuadFin F (dD D) :=
    ⟨mkAF (fun v => ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.re)
        (by filter_upwards [hev] with v hv; exact hO v _ hv.2.2.1),
     mkAF (fun v => ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.im)
        (by filter_upwards [hev] with v hv; exact hO v _ hv.2.2.2)⟩
  have hx : ∀ v, projQV (dD D) v x = t v := fun v => QuadraticAlgebra.ext rfl rfl
  have hy : ∀ v, projQV (dD D) v y = ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val :=
    fun v => QuadraticAlgebra.ext rfl rfl
  have hxy : x * y = 1 := quadFin_ext fun v => by rw [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := quadFin_ext fun v => by rw [map_mul, map_one, hx, hy, Units.inv_mul]
  exact ⟨⟨x, y, hxy, hyx⟩, fun v => Units.ext (hx v)⟩

/-- **The local sets $U_v = \mathrm{tor}(1+\varpi^kO_{E,v})$ of the box $K'$.** -/
def Uloc (v : HeightOneSpectrum (𝓞 F)) : Set (SOv v (diagForm1 D)) :=
  (torSOK D (v.adicCompletion F)) '' (winO S k v : Set (QuadK D (v.adicCompletion F))ˣ)

/-- **The box $K' = \prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)\subseteq SO(V)(\mathbb A_f)$.** -/
def Kp : Set (SOAf (diagForm1 D)) := boxSO (diagForm1 D) Sfin (Uloc S k)

theorem evalSO_torFin (g : (QuadFin F (dD D))ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    evalSO (diagForm1 D) v (torFin D g) = torSOK D (v.adicCompletion F) (unitAtD (dD D) v g) := rfl

/-- **Lifts of elements of $K'$:** if $x\in K'$ there is $g\in(E\otimes\mathbb A_{F,f})^\times$ with $\mathrm{tor}(g) = x$
and $g_v\in T_v$ for every $v$ (lifting each local component and gluing). -/
theorem exists_lift (hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal) {x : SOAf (diagForm1 D)}
    (hx : x ∈ Kp S Sfin k) :
    ∃ g : (QuadFin F (dD D))ˣ, torFin D g = x ∧ ∀ v, unitAtD (dD D) v g ∈ Tloc S Sfin k v := by
  classical
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : (QuadK D (v.adicCompletion F))ˣ,
      t ∈ Tloc S Sfin k v ∧ torSOK D (v.adicCompletion F) t = evalSO (diagForm1 D) v x := by
    intro v
    by_cases hv : v ∈ Sfin
    · obtain ⟨t, ht, hte⟩ := hx.1 v hv
      exact ⟨t, by rw [Tloc, ite_of_cond hv]; exact ht, hte⟩
    · obtain ⟨h2, hDv⟩ := valued_two_D_eq_one v (hS v hv)
      obtain ⟨t, ht, hte⟩ := exists_umax_lift S v h2 hDv (evalSO (diagForm1 D) v x) (hx.2 v hv)
      exact ⟨t, by rw [Tloc, ite_of_not_cond hv]; exact ht, hte⟩
  choose t ht1 ht2 using hloc
  have hcof : ∀ᶠ v in Filter.cofinite, v ∉ Sfin := by
    rw [Filter.eventually_cofinite]
    exact (Sfin.finite_toSet).subset (fun v hv => by simpa using hv)
  have hev : ∀ᶠ v in Filter.cofinite, Valued.v (t v : QuadK D (v.adicCompletion F)).re ≤ 1 ∧
      Valued.v (t v : QuadK D (v.adicCompletion F)).im ≤ 1 ∧
      Valued.v ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.re ≤ 1 ∧
      Valued.v ((t v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.im ≤ 1 := by
    filter_upwards [hcof] with v hv
    obtain ⟨h2, hDv⟩ := valued_two_D_eq_one v (hS v hv)
    have hu : t v ∈ umax S v := by have := ht1 v; rwa [Tloc, ite_of_not_cond hv] at this
    obtain ⟨a, b⟩ := coords_le_one_of_umax S v h2 hDv hu
    obtain ⟨c, d⟩ := coords_le_one_of_umax S v h2 hDv (inv_mem hu)
    exact ⟨a, b, c, d⟩
  obtain ⟨g, hg⟩ := exists_quadFin_unit t hev
  refine ⟨g, ?_, fun v => by rw [hg v]; exact ht1 v⟩
  refine Subtype.ext ?_
  ext v : 1
  have := congrArg (fun s : SOv v (diagForm1 D) => (s : orthGroup (formF (diagForm1 D)) (v.adicCompletion F)))
    (ht2 v)
  rw [← hg v] at this
  exact this

/-- **A product $\Theta(g)\iota(c)\in A_f$ forces $\mathrm{tor}(g)\in K'$.** -/
theorem torFin_mem_Kp_of_mem_boxE (hk : ∀ v ∈ Sfin, 1 ≤ k v) (hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal)
    {g : (QuadFin F (dD D))ˣ} {c : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hc : Units.map (quadFinBC (hdD S)).toMonoidHom g * Units.map (finMap F E).toMonoidHom c ∈ boxE E Sfin k) :
    torFin D g ∈ Kp S Sfin k := by
  classical
  have H := (mem_boxE_iff S Sfin k hk g c).1 hc
  have hscal : ∀ v : HeightOneSpectrum (𝓞 F),
      torSOK D (v.adicCompletion F) (Units.map (algebraMap (v.adicCompletion F) (QuadK D (v.adicCompletion F))).toMonoidHom
        (unitAt c v)) = 1 := fun v => by
    rw [torSOK_eq_one_iff]
    simp
  have hkey : ∀ v : HeightOneSpectrum (𝓞 F), evalSO (diagForm1 D) v (torFin D g) =
      torSOK D (v.adicCompletion F) (unitAtD (dD D) v g *
        Units.map (algebraMap (v.adicCompletion F) (QuadK D (v.adicCompletion F))).toMonoidHom (unitAt c v)) := by
    intro v
    rw [map_mul, hscal v, mul_one]
    rfl
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · refine ⟨_, ?_, (hkey v).symm⟩
    have := H v
    rwa [Tloc, ite_of_cond hv] at this
  · obtain ⟨h2, hDv⟩ := valued_two_D_eq_one v (hS v hv)
    have hu : unitAtD (dD D) v g *
        Units.map (algebraMap (v.adicCompletion F) (QuadK D (v.adicCompletion F))).toMonoidHom (unitAt c v) ∈ umax S v := by
      have := H v
      rwa [Tloc, ite_of_not_cond hv] at this
    rw [hkey v]
    exact torSOK_umax_mem_stdStab S v h2 hDv hu

/-- **The finite fibre function**: for $x\in SO(V)(\mathbb A_f)$,
$$K_f(x) = \mu_{f,F}\{c : \Theta(g)\,\iota(c)\in A_f\} = \mu_{f,F}(N_F)\cdot\mathbf 1_{K'}(x)\qquad(\mathrm{tor}(g) = x).$$ -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem fibFinSO_eq (hD : D ≠ 0) (hk : ∀ v ∈ Sfin, 1 ≤ k v) (hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal)
    (x : SOAf (diagForm1 D)) :
    fibFinSO E (hdD S) hD (boxE E Sfin k) x = muFinUnits F (boxF Sfin k) * (Kp S Sfin k).indicator 1 x := by
  classical
  obtain ⟨g, rfl⟩ := torFin_surjective D hD x
  rw [fibFinSO_torFin]
  by_cases hx : torFin D g ∈ Kp S Sfin k
  · obtain ⟨g', hg'x, hg'T⟩ := exists_lift S Sfin k hS hx
    rw [fibreFin_eq_of_torFin_eq (hdD S) _ hg'x.symm, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    unfold fibreFin
    congr 1
    ext c
    simp only [mem_ofPred_eq]
    rw [mem_boxE_iff S Sfin k hk g' c]
    change _ ↔ ∀ v, unitAt c v ∈ (if v ∈ Sfin then winF k v else unitsVSub v)
    refine forall_congr' fun v => ?_
    rw [Subgroup.mul_mem_cancel_left _ (hg'T v)]
    exact scalar_mem_Tloc_iff S Sfin k v hk _
  · rw [Set.indicator_of_notMem hx, mul_zero]
    unfold fibreFin
    have : {c : (FiniteAdeleRing (𝓞 F) F)ˣ | Units.map (quadFinBC (hdD S)).toMonoidHom g *
        Units.map (finMap F E).toMonoidHom c ∈ boxE E Sfin k} = ∅ := by
      ext c
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun hc => hx (torFin_mem_Kp_of_mem_boxE S Sfin k hk hS hc)
    rw [this, measure_empty]

end TorusSide

end QuadFormsKB.Tamagawa.Measure.Weil
