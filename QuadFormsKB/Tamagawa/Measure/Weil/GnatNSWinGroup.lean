/-
# $[U^{(M)}_v : K_N] = [\mathfrak L : \mathfrak L_N]\cdot[T : T_0]$

**Layer:** a number field $F$, $K = F(\delta)$ with basis $(1,\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$ in $\mathcal O_K$; a finite
place $v$ of $F$ (any: split, inert, ramified, dyadic), the places $w\mid v$; $Y = Y^{(M)}$ = `nsLocSub` at levels
$M_w\ge e_wn + s_w + e_\alpha(w) + e_\beta(w)$.

* `etaY y` $=\operatorname{re}(y)^{-1}\operatorname{imvE}(y)$: every $y\in Y$ is $\operatorname{re}(y)\,(1+\operatorname{pureE}\eta)$ with $\operatorname{re}(y)$ a unit
  at every $w\mid v$ and $\eta\in\mathfrak L$ = `LSub` $=\{\eta : (\varphi_w(\eta_l))_l\in\Lambda'_{M_w}\ \forall w\mid v\}$.
* `LwinSub` $=\mathfrak L_N$ (`Lwin`) as an additive subgroup; $\mathfrak L_N\subseteq\mathfrak L$ when $M_w\le e_w(N - s - e_a)$.

Source: Weil 1982, §2.2-2.3 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWindow

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section Place

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))

include hb₀ in
theorem qlh_injective {z z' : E} (h : ∀ w : PlaceSet (K := K) v, qlh hb₁ v w z =
    qlh hb₁ v w z') : z = z' :=
  quadLocalHom_injective hb₀ hb₁ v h

include hb₀ in
theorem exists_qlh_eq (t : PlaceProd (K := K) v) :
    ∃ z : E, ∀ w : PlaceSet (K := K) v, qlh hb₁ v w z = t w :=
  exists_quadLocalHom_eq hb₀ hb₁ v t

include hb₀ in
/-- An element of $E$ that is a unit at every $w\mid v$ is a unit of $E$. -/
theorem isUnit_of_qlh_ne_zero {z : E} (hz : ∀ w : PlaceSet (K := K) v, qlh hb₁ v w z ≠ 0) :
    IsUnit z := by
  obtain ⟨z', hz'⟩ := exists_qlh_eq hb₀ hb₁ (fun w => (qlh hb₁ v w z)⁻¹)
  have : z * z' = 1 := qlh_injective hb₀ hb₁ fun w => by
    rw [qlh_mul, hz', qlh_one, mul_inv_cancel₀ (hz w)]
  exact ⟨⟨z, z', this, by rw [mul_comm]; exact this⟩, rfl⟩

theorem qlh_ring_inverse {z : E} (hz : IsUnit z) (w : PlaceSet (K := K) v) :
    qlh hb₁ v w (Ring.inverse z) = (qlh hb₁ v w z)⁻¹ := by
  have h1 : qlh hb₁ v w z * qlh hb₁ v w (Ring.inverse z) = 1 :=
    (qlh_mul hb₁ w z _).symm.trans ((congrArg (qlh hb₁ v w)
      (Ring.mul_inverse_cancel z hz)).trans (qlh_one hb₁ w))
  exact (eq_inv_of_mul_eq_one_right h1)

end Place

section Lattices

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

theorem latP_add {k : Type} [Field k] [NumberField k] {u : HeightOneSpectrum (𝓞 k)} {m : ℕ}
    {A B : u.adicCompletion k} {x y : Fin 3 → u.adicCompletion k} (hx : x ∈ latP u m A B) (hy : y ∈ latP u m A B) :
    x + y ∈ latP u m A B := by
  obtain ⟨x0, x1, x2, x3⟩ := hx
  obtain ⟨y0, y1, y2, y3⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Pi.add_apply, mul_add] <;>
    exact (Valuation.map_add _ _ _).trans (max_le ‹_› ‹_›)

theorem latP_neg {k : Type} [Field k] [NumberField k] {u : HeightOneSpectrum (𝓞 k)} {m : ℕ}
    {A B : u.adicCompletion k} {x : Fin 3 → u.adicCompletion k} (hx : x ∈ latP u m A B) :
    -x ∈ latP u m A B := by
  obtain ⟨x0, x1, x2, x3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Pi.neg_apply, mul_neg, Valuation.map_neg] <;> assumption

theorem latP_zero {k : Type} [Field k] [NumberField k] {u : HeightOneSpectrum (𝓞 k)} {m : ℕ}
    {A B : u.adicCompletion k} : (0 : Fin 3 → u.adicCompletion k) ∈ latP u m A B := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

variable (M : HeightOneSpectrum (𝓞 K) → ℕ)

variable (α β) in
/-- **$\mathfrak L = \{\eta\in E^3 : (\varphi_w(\eta_l))_l\in\Lambda'_{M_w}\ \forall w\mid v\}$.** -/
def LSub : AddSubgroup (Fin 3 → E) where
  carrier := {η | ∀ w : PlaceSet (K := K) v, (fun l => qlh hb₁ v w (η l)) ∈
    latP w.1 (M w.1) (algebraMap K (w.1.adicCompletion K) (α : K)) (algebraMap K (w.1.adicCompletion K) (β : K))}
  add_mem' {x y} hx hy w := by
    have := latP_add (hx w) (hy w)
    show (fun l => qlh hb₁ v w (x l + y l)) ∈ _
    simp only [qlh_add]
    exact this
  zero_mem' w := by
    have := latP_zero (u := w.1) (m := M w.1) (A := algebraMap K (w.1.adicCompletion K) (α : K))
      (B := algebraMap K (w.1.adicCompletion K) (β : K))
    convert this using 1
    funext l; exact map_zero _
  neg_mem' {x} hx w := by
    have := latP_neg (hx w)
    convert this using 1
    funext l; exact map_neg (qlh hb₁ v w) (x l)

variable (a b d) in
/-- **$\mathfrak L_N$** = `Lwin v a b d N` as an additive subgroup. -/
def LwinSub (N : ℕ) : AddSubgroup (Fin 3 → E) where
  carrier := Lwin v a b d N
  add_mem' {x y} hx hy := by
    refine ⟨?_, fun l => ?_⟩
    · have := latP_add hx.1 hy.1
      show (fun l => (x l + y l).re) ∈ _
      simp only [QuadraticAlgebra.re_add]
      exact this
    · rw [Pi.add_apply, QuadraticAlgebra.im_add, mul_add]
      exact (Valuation.map_add _ _ _).trans (max_le (hx.2 l) (hy.2 l))
  zero_mem' := ⟨latP_zero, fun l => by simp⟩
  neg_mem' {x} hx := by
    refine ⟨?_, fun l => ?_⟩
    · have := latP_neg hx.1
      show (fun l => (-x l).re) ∈ _
      simp only [QuadraticAlgebra.re_neg]
      exact this
    · rw [Pi.neg_apply, QuadraticAlgebra.im_neg, mul_neg, Valuation.map_neg]; exact hx.2 l

theorem mem_lwin_of_cl {N : ℕ} {η : Fin 3 → E} (h : ∀ l, CL v N (η l)) : η ∈ LwinSub a b d v N := by
  have hA := valued_algebraMap_le_one a v
  have hB := valued_algebraMap_le_one b v
  have h2 : Valued.v (2 : Fv) ≤ 1 := by rw [valued_two_eq v, ← exp_zero, exp_le_exp]; omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun l => valued_mul_le_of_le h2 (h l).2⟩
  · exact valued_mul_le_of_le h2 (h 0).1
  · exact valued_mul_le_of_le h2 (h 1).1
  · rw [mul_assoc]; exact valued_mul_le_of_le h2 (valued_mul_le_of_le hA (h 2).1)
  · rw [mul_assoc]; exact valued_mul_le_of_le h2 (valued_mul_le_of_le hB (h 2).1)

/-- Elements of $\mathfrak L_N$ have coordinate level $N - s - e_a$. -/
theorem cl_of_mem_lwin {N : ℕ} {η : Fin 3 → E} (h : η ∈ LwinSub a b d v N) (ha0 : a ≠ 0) (l : Fin 3) :
    CL v ((N : ℤ) - sExp v - eExp a ha0 v) (η l) := by
  have hs := valued_two_eq v
  have hA := valued_eExp a ha0 v
  have hB := valued_algebraMap_le_one b v
  obtain ⟨⟨p0, p1, p2, p3⟩, q⟩ := h
  have key : ∀ {x : Fv} {j : ℤ}, Valued.v (2 * x) ≤ exp (-(N : ℤ)) → Valued.v x ≤ exp (-((N : ℤ) - sExp v - j))
      → Valued.v x ≤ exp (-((N : ℤ) - sExp v - j)) := fun _ h => h
  have h2x : ∀ {x : Fv}, Valued.v (2 * x) ≤ exp (-(N : ℤ)) → Valued.v x ≤ exp (-((N : ℤ) - sExp v)) := by
    intro x hx
    rw [map_mul, hs] at hx
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]; exact zero_le
    obtain ⟨k, hk⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hx0
    rw [hk, ← exp_add, exp_le_exp] at hx
    rw [hk, exp_le_exp]; omega
  have hmono : ∀ {x : Fv}, Valued.v x ≤ exp (-((N : ℤ) - sExp v)) →
      Valued.v x ≤ exp (-((N : ℤ) - sExp v - eExp a ha0 v)) := fun hx => hx.trans (exp_le_exp.2 (by omega))
  refine ⟨?_, hmono (h2x (q l))⟩
  fin_cases l
  · exact hmono (h2x p0)
  · exact hmono (h2x p1)
  · -- `|2 a x| ≤ q^{-N}` gives `|x| ≤ q^{-(N - s - e_a)}`
    change Valued.v (η 2).re ≤ _
    have hx := p2
    rw [map_mul, map_mul, hs, hA] at hx
    by_cases hx0 : (η 2).re = 0
    · rw [hx0, map_zero]; exact zero_le
    obtain ⟨k, hk⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hx0
    rw [hk, ← exp_add, ← exp_add, exp_le_exp] at hx
    rw [hk, exp_le_exp]; omega

/-- **Valuations on $\Lambda'_m$**: for $t\in\Lambda'_m$ ($K_w$, levels $m\ge s_w + e_\alpha(w) + j$) every coordinate has
$|t_l|_w\le q_w^{-j}$. -/
theorem valued_le_of_latP (w : HeightOneSpectrum (𝓞 K)) {m j : ℕ}
    (hm : sExp w + eExp α hα0 w + j ≤ m) {t : Fin 3 → w.adicCompletion K}
    (ht : t ∈ latP w m (algebraMap K (w.adicCompletion K) (α : K)) (algebraMap K (w.adicCompletion K) (β : K)))
    (l : Fin 3) : Valued.v (t l) ≤ exp (-(j : ℤ)) := by
  have hs := valued_two_eq w
  have hA := valued_eExp α hα0 w
  obtain ⟨p0, p1, p2, -⟩ := ht
  have h2x : ∀ {x : w.adicCompletion K}, Valued.v (2 * x) ≤ exp (-(m : ℤ)) → Valued.v x ≤ exp (-(j : ℤ)) := by
    intro x hx
    rw [map_mul, hs] at hx
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]; exact zero_le
    obtain ⟨k, hk⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp w hx0
    rw [hk, ← exp_add, exp_le_exp] at hx
    rw [hk, exp_le_exp]; omega
  fin_cases l
  · exact h2x p0
  · exact h2x p1
  · change Valued.v (t 2) ≤ _
    rw [map_mul, map_mul, hs, hA] at p2
    by_cases hx0 : t 2 = 0
    · rw [hx0, map_zero]; exact zero_le
    obtain ⟨k, hk⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp w hx0
    rw [hk, ← exp_add, ← exp_add, exp_le_exp] at p2
    rw [hk, exp_le_exp]; omega

/-- Elements of $\mathfrak L$ have place level $n$ when $M_w\ge s_w + e_\alpha(w) + e_wn$. -/
theorem pl_of_mem_L {n : ℕ} (hMn : ∀ w : PlaceSet (K := K) v, sExp w.1 + eExp α hα0 w.1 + ramE v w.1 * n ≤ M w.1)
    {η : Fin 3 → E} (h : η ∈ LSub hb₁ α β v M) (l : Fin 3) : PL hb₁ v n (η l) := by
  intro w
  have := valued_le_of_latP hα0 w.1 (hMn w) (h w) l
  simpa using this

include hb₀ in
/-- $\mathfrak L_N\subseteq\mathfrak L$ when $M_w\le e_w(N - s - e_a)$. -/
theorem lwin_le_L (ha0 : a ≠ 0) {N : ℕ} (hMN : ∀ w : PlaceSet (K := K) v,
    (M w.1 : ℤ) ≤ ramE v w.1 * ((N : ℤ) - sExp v - eExp a ha0 v)) :
    LwinSub a b d v N ≤ LSub hb₁ α β v M := by
  intro η hη w
  have hcl := fun l => cl_of_mem_lwin v hη ha0 l
  have hpl := fun l => pl_of_cl hb₀ hb₁ (hcl l) w
  have h2 : Valued.v (2 : w.1.adicCompletion K) ≤ 1 := by
    rw [valued_two_eq w.1, ← exp_zero, exp_le_exp]; omega
  have hA : Valued.v (algebraMap K (w.1.adicCompletion K) (α : K)) ≤ 1 := valued_algebraMap_le_one α w.1
  have hB : Valued.v (algebraMap K (w.1.adicCompletion K) (β : K)) ≤ 1 := valued_algebraMap_le_one β w.1
  have hle : ∀ l, Valued.v (qlh hb₁ v w (η l)) ≤ exp (-(M w.1 : ℤ)) := fun l =>
    (hpl l).trans (exp_le_exp.2 (by have := hMN w; linarith))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact valued_mul_le_of_le h2 (hle 0)
  · exact valued_mul_le_of_le h2 (hle 1)
  · rw [mul_assoc]; exact valued_mul_le_of_le h2 (valued_mul_le_of_le hA (hle 2))
  · rw [mul_assoc]; exact valued_mul_le_of_le h2 (valued_mul_le_of_le hB (hle 2))

end Lattices

end QuadFormsKB.Tamagawa.Measure.Weil

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section YGroup

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (v : HeightOneSpectrum (𝓞 F))
  (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w)

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

/-- The element of $D_E$ underlying $y\in G^\natural(F_v)$. -/
abbrev yv {u : HeightOneSpectrum (𝓞 F)} (y : GnK (u.adicCompletion F) a b d) : DEr (u.adicCompletion F) a b d :=
  ((y : DEK (u.adicCompletion F) a b d) : DEr (u.adicCompletion F) a b d)

/-- $\eta(x) = \operatorname{re}(x)^{-1}\operatorname{imvE}(x)$. -/
def etaY {u : HeightOneSpectrum (𝓞 F)} (x : DEr (u.adicCompletion F) a b d) :
    Fin 3 → QE (algebraMap F (u.adicCompletion F) (d : F)) := Ring.inverse x.re • imvE x

theorem imv_quatLocalHom (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) (x : DEr Fv a b d) :
    imv (quatLocalHom hb₁ hα hβ v w h x) = fun l => quadLocalHom hb₁ v w h (imvE x l) := by
  funext l; fin_cases l <;> rfl

/-- **Membership in $Y^{(M)}$** at deep levels: $\operatorname{re}(y)$ is a unit at every $w\mid v$ and
$(\varphi_w(\operatorname{imvE}(y)_l))_l\in\Lambda'_{M_w}$. -/
theorem mem_nsLocSub_iff (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) (y : GnK Fv a b d) :
    y ∈ nsLocSub hb₁ hα hβ v M hM1 ↔ ∀ w : PlaceSet (K := K) v,
      Valued.v (qlh hb₁ v w (yv y).re) = 1 ∧
      (fun l => qlh hb₁ v w (imvE (yv y) l)) ∈
        latP w.1 (M w.1) (algebraMap K (w.1.adicCompletion K) (α : K)) (algebraMap K (w.1.adicCompletion K) (β : K)) := by
  have key : ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
      quatLocalUnit hb₁ hα hβ v w h (y : DEK Fv a b d) ∈ lamCong w α β (M w) (hM1 w) ↔
      Valued.v (quadLocalHom hb₁ v w h (yv y).re) = 1 ∧
      (fun l => quadLocalHom hb₁ v w h (imvE (yv y) l)) ∈
        latP w (M w) (algebraMap K (w.adicCompletion K) (α : K)) (algebraMap K (w.adicCompletion K) (β : K)) := by
    intro w h
    have hm := hMdeep w
    unfold nsLevK at hm
    rw [mem_lamCong_iff w α β (valued_two_eq w) (valued_eExp α hα0 w) (by omega) (by omega) (hM1 w)]
    change Valued.v (quatLocalHom hb₁ hα hβ v w h (yv y)).re = 1 ∧
      imv (quatLocalHom hb₁ hα hβ v w h (yv y)) ∈ _ ↔ _
    rw [imv_quatLocalHom, quatLocalHom_re]
  constructor
  · intro hy w; exact (key w.1 w.2).1 (hy w.1 w.2)
  · intro hy w h; exact (key w h).2 (hy ⟨w, h⟩)

variable {v M hM1}

include hb₀ in
theorem isUnit_re_of_mem (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) {y : GnK Fv a b d}
    (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) : IsUnit (yv y).re :=
  isUnit_of_qlh_ne_zero hb₀ hb₁ fun w h0 => by
    have := ((mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hMdeep y).1 hy w).1
    rw [h0, map_zero] at this; exact zero_ne_one this

include hb₀ in
theorem etaY_mem_L (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) {y : GnK Fv a b d}
    (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) : etaY (yv y) ∈ LSub hb₁ α β v M := by
  intro w
  obtain ⟨h1, h2⟩ := (mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hMdeep y).1 hy w
  have hu := isUnit_re_of_mem hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hy
  have hinv : Valued.v (qlh hb₁ v w (yv y).re)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  have := (smul_mem_latP_iff (a := α) (b := β) hinv _).2 h2
  convert this using 1
  funext l
  change qlh hb₁ v w (Ring.inverse (yv y).re * imvE (yv y) l) = _
  rw [qlh_mul]
  exact congrArg (· * qlh hb₁ v w (imvE (yv y) l)) (qlh_ring_inverse hb₁ hu w)

include hb₀ in
/-- **$y = \operatorname{re}(y)\,(1+\operatorname{pureE}\eta(y))$** for $y\in Y^{(M)}$. -/
theorem yv_eq (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) {y : GnK Fv a b d}
    (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) :
    yv y = ((yv y).re : DEr Fv a b d) * (1 + pureE (etaY (yv y))) :=
  coe_mul_one_add _ (Ring.mul_inverse_cancel _ (isUnit_re_of_mem hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hy))

variable {c₀ n : ℕ}

include hb₀ in
theorem cl_of_mem_L (hc₀ : ∀ (k : ℤ) (z : E), PL hb₁ v k z → CL v (k - c₀) z)
    (hMn : ∀ w : PlaceSet (K := K) v, sExp w.1 + eExp α hα0 w.1 + ramE v w.1 * n ≤ M w.1)
    {η : Fin 3 → E} (h : η ∈ LSub hb₁ α β v M) (l : Fin 3) : CL v ((n : ℤ) - c₀) (η l) :=
  hc₀ _ _ (pl_of_mem_L hb₁ hα0 v M hMn h l)

theorem pl_zero_of_valued (z : E) (hz : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) = 1) :
    PL hb₁ v 0 z := fun w => by rw [hz w, mul_zero, neg_zero, exp_zero]

set_option maxHeartbeats 1000000 in
include hb₀ in
/-- **The window homomorphism property**: $\eta(yy')\equiv\eta(y) + \eta(y')\bmod\mathfrak L_N$ for $y, y'\in Y^{(M)}$
($N\le2(n - c_0) - c_0$). -/
theorem etaY_mul_sub_mem (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w)
    (hc₀ : ∀ (k : ℤ) (z : E), PL hb₁ v k z → CL v (k - c₀) z)
    (hMn : ∀ w : PlaceSet (K := K) v, sExp w.1 + eExp α hα0 w.1 + ramE v w.1 * n ≤ M w.1)
    {N : ℕ} (hwin : (N : ℤ) ≤ 2 * ((n : ℤ) - c₀) - c₀) (hn : (c₀ : ℤ) ≤ n)
    {y y' : GnK Fv a b d} (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) (hy' : y' ∈ nsLocSub hb₁ hα hβ v M hM1) :
    etaY (yv (y * y')) - etaY (yv y) - etaY (yv y') ∈ LwinSub a b d v N := by
  have hyy' : y * y' ∈ nsLocSub hb₁ hα hβ v M hM1 := (nsLocSub hb₁ hα hβ v M hM1).mul_mem hy hy'
  set r := (yv y).re
  set r' := (yv y').re
  set η := etaY (yv y)
  set η' := etaY (yv y')
  have e1 : yv (y * y') = yv y * yv y' := rfl
  have hprod := re_imvE_mul (a := Av) (b := Bv) r r' η η'
  rw [← yv_eq hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hy, ← yv_eq hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hy', ← e1] at hprod
  obtain ⟨hre, him⟩ := hprod
  set ε := (pureE η * pureE η' : DEr Fv a b d).re
  set χ := imvE (pureE η * pureE η' : DEr Fv a b d)
  set u := (yv (y * y')).re
  have hu := isUnit_re_of_mem hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hyy'
  set ι := Ring.inverse u * (r * r')
  have hι : ι * (1 + ε) = 1 := by
    simp only [ι]; rw [mul_assoc, ← hre]; exact Ring.inverse_mul_cancel u hu
  have heta : etaY (yv (y * y')) = ι • (η + η' + χ) := by
    unfold etaY; rw [him, smul_smul]
  have key : etaY (yv (y * y')) - η - η' = fun l => ι * χ l - ι * ε * (η l + η' l) := by
    rw [heta]; funext l
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (η l + η' l) * hι
  rw [key]
  -- the levels
  have hk0 : ∀ l, CL v ((n : ℤ) - c₀) (η l) := cl_of_mem_L hb₀ hb₁ hα0 hc₀ hMn
    (etaY_mem_L hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hy)
  have hk0' : ∀ l, CL v ((n : ℤ) - c₀) (η' l) := cl_of_mem_L hb₀ hb₁ hα0 hc₀ hMn
    (etaY_mem_L hb₀ hb₁ hα hβ hα0 hβ0 hMdeep hy')
  have hQ := (QL_pureE (v := v) (a := a) (b := b) hk0).mul (QL_pureE hk0')
  have hval : ∀ {y₀ : GnK Fv a b d}, y₀ ∈ nsLocSub hb₁ hα hβ v M hM1 → ∀ w : PlaceSet (K := K) v,
      Valued.v (qlh hb₁ v w (yv y₀).re) = 1 := fun h w =>
    ((mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hMdeep _).1 h w).1
  have hιpl : PL hb₁ v 0 ι := pl_zero_of_valued hb₁ ι fun w => by
    simp only [ι]
    rw [qlh_mul, qlh_mul, Valuation.map_mul, Valuation.map_mul, hval hy w, hval hy' w, mul_one, mul_one]
    have := congrArg Valued.v (qlh_ring_inverse hb₁ hu w)
    rw [this, map_inv₀, hval hyy' w, inv_one]
  have hιcl : CL v (0 - c₀) ι := hc₀ _ _ hιpl
  refine mem_lwin_of_cl v fun l => ?_
  have hχ : CL v (((n : ℤ) - c₀) + ((n : ℤ) - c₀)) (χ l) := by
    fin_cases l
    · exact hQ.2.1
    · exact hQ.2.2.1
    · exact hQ.2.2.2
  have h1 := hιcl.mul hχ
  have h2 := (hιcl.mul hQ.1).mul ((hk0 l).add (hk0' l))
  exact (h1.mono (by omega)).sub (h2.mono (by omega))

include hb₀ in
/-- **Square roots near $1$ in $E$**: if $|z|\le q^{-2k}$ ($k > s$) there is $\varepsilon\in E$, a unit at every $w\mid v$, with
$\varepsilon^2(1+z) = 1$. -/
theorem exists_sq_mul_one_add_eq_one {k : ℕ} (hk : sExp v < k) {z : E} (hz : CL v (2 * (k : ℤ)) z) :
    ∃ ε : E, ε ^ 2 * (1 + z) = 1 ∧ ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w ε) = 1 := by
  have key : ∀ w : PlaceSet (K := K) v, ∃ r : w.1.adicCompletion K,
      r ^ 2 * (1 + qlh hb₁ v w z) = 1 ∧ Valued.v r = 1 := by
    intro w
    set x := qlh hb₁ v w z
    have hx : Valued.v x ≤ exp (-((ramE v w.1 : ℤ) * (2 * (k : ℤ)))) := pl_of_cl hb₀ hb₁ hz w
    have he := one_le_ramE v w.1 w.2
    have hsw := sExp_over v w.1 w.2
    have hx1 : Valued.v x < 1 := hx.trans_lt (by
      rw [← exp_zero, exp_lt_exp]; have : (1 : ℤ) ≤ ramE v w.1 := by exact_mod_cast he
      nlinarith)
    have h1x : Valued.v (1 + x) = 1 := by
      have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := 1) (y := x) (by rwa [map_one])
      rwa [map_one] at this
    have h1x0 : 1 + x ≠ 0 := by intro h0; rw [h0, map_zero] at h1x; exact zero_ne_one h1x
    set m : ℕ := ramE v w.1 * (2 * k) - sExp w.1
    have hsm : sExp w.1 < m := by
      simp only [m, hsw]
      have : ramE v w.1 * sExp v < ramE v w.1 * k := Nat.mul_lt_mul_of_pos_left hk (by omega)
      have : ramE v w.1 * (2 * k) = 2 * (ramE v w.1 * k) := by ring
      omega
    have hmt : ((m + sExp w.1 : ℕ) : ℤ) = (ramE v w.1 : ℤ) * (2 * (k : ℤ)) := by
      have : sExp w.1 ≤ ramE v w.1 * (2 * k) := by
        rw [hsw]; have := Nat.mul_le_mul_left (ramE v w.1) hk.le; nlinarith
      simp only [m]; push_cast [Nat.sub_add_cancel this]; ring
    have ht : Valued.v ((1 + x)⁻¹ - 1) ≤ exp (-((m + sExp w.1 : ℕ) : ℤ)) := by
      have e : (1 + x)⁻¹ - 1 = -x * (1 + x)⁻¹ := by field_simp; ring
      rw [e, map_mul, Valuation.map_neg, map_inv₀, h1x, inv_one, mul_one, hmt]; exact hx
    obtain ⟨r, hr, hr1⟩ := exists_sq_eq_near_one w.1 (valued_two_eq w.1) hsm ht
    refine ⟨r, by rw [hr, inv_mul_cancel₀ h1x0], ?_⟩
    have hlt : Valued.v (r - 1) < 1 := hr1.trans_lt (by rw [← exp_zero, exp_lt_exp]; omega)
    have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := 1) (y := r - 1) (by rwa [map_one])
    rwa [add_sub_cancel, map_one] at this
  choose r hr using key
  obtain ⟨ε, hε⟩ := exists_qlh_eq hb₀ hb₁ r
  refine ⟨ε, qlh_injective hb₀ hb₁ fun w => ?_, fun w => by rw [hε w]; exact (hr w).2⟩
  rw [map_mul, map_pow, map_add, map_one, hε w]; exact (hr w).1

include hb₀ in
/-- **Every $\eta\in\mathfrak L$ is $\eta(y)$ for some $y\in Y^{(M)}$**: $y = \varepsilon(1+\operatorname{pureE}\eta)$ with
$\varepsilon^2\operatorname{nrd}(1+\operatorname{pureE}\eta) = 1$. -/
theorem exists_mem_etaY_eq (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w)
    (hc₀ : ∀ (k : ℤ) (z : E), PL hb₁ v k z → CL v (k - c₀) z)
    (hMn : ∀ w : PlaceSet (K := K) v, sExp w.1 + eExp α hα0 w.1 + ramE v w.1 * n ≤ M w.1)
    (hn : c₀ + sExp v < n) {η : Fin 3 → E} (hη : η ∈ LSub hb₁ α β v M) :
    ∃ y : GnK Fv a b d, y ∈ nsLocSub hb₁ hα hβ v M hM1 ∧ etaY (yv y) = η := by
  have hk : ∀ l, CL v ((n - c₀ : ℕ) : ℤ) (η l) := fun l => by
    have := cl_of_mem_L hb₀ hb₁ hα0 hc₀ hMn hη l
    rwa [show ((n - c₀ : ℕ) : ℤ) = (n : ℤ) - c₀ by omega]
  set z := nrdE (pureE η : DEr Fv a b d)
  have hz : CL v (2 * ((n - c₀ : ℕ) : ℤ)) z := by
    have hQ := (QL_pureE (v := v) (a := a) (b := b) hk).mul (QL_pureE hk).neg
    rw [← star_pureE] at hQ
    rw [show z = _ from nrdE_eq_re_mul_star _]
    exact hQ.1.mono (by omega)
  obtain ⟨ε, hε, hεw⟩ := exists_sq_mul_one_add_eq_one hb₀ hb₁ (k := n - c₀) (by omega) hz
  set y0 : DEr Fv a b d := (ε : DEr Fv a b d) * (1 + pureE η)
  have hn0 : nrdE y0 = algebraMap Fv (QE (algebraMap F Fv (d : F))) 1 := by
    rw [nrdE_coe_mul_one_add, map_one]; exact hε
  set y : GnK Fv a b d := ⟨QuadFormsKB.Quat.Gnat.unitOfNrd y0 1 one_ne_zero hn0,
    QuadFormsKB.Quat.Gnat.unitOfNrd_mem y0 1 one_ne_zero hn0⟩
  have hyv : yv y = y0 := rfl
  have hre : (yv y).re = ε := by rw [hyv, re_coe_mul, re_one_add_pureE, mul_one]
  have him : imvE (yv y) = ε • η := by rw [hyv, imvE_coe_mul, imvE_one_add_pureE]
  have hεu : IsUnit ε := by
    have h1 : ε * (ε * (1 + z)) = 1 := by rw [← mul_assoc, ← pow_two]; exact hε
    exact ⟨⟨ε, ε * (1 + z), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨y, (mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hMdeep y).2 fun w => ⟨by rw [hre]; exact hεw w, ?_⟩, ?_⟩
  · have := (smul_mem_latP_iff (a := α) (b := β) (hεw w) _).2 (hη w)
    convert this using 1
    funext l
    rw [him, Pi.smul_apply, smul_eq_mul, map_mul]; rfl
  · unfold etaY; rw [hre, him, smul_smul, Ring.inverse_mul_cancel ε hεu, one_smul]

end YGroup

end QuadFormsKB.Tamagawa.Measure.Weil
