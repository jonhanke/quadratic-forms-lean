/-
# $\Phi(\pi(S_0))$ is a box

**Layer:** a number field $F$, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$ in $\mathcal O_K$; a finite place $v$ of $F$ and a
place $w\mid v$ of $K$.

* **`quatLocalHom`**: $D_E\otimes F_v\to D'\otimes K_w$, coordinatewise `quadLocalHom`
  ($x + y\omega\mapsto\varphi_w(x) + \delta\varphi_w(y)$).
* **`unitAtA_eq_quatLocalHom`**: the $w$-component of $g_1\in(D'\otimes\mathbb A_K)^\times$ is `quatLocalHom` of the $v$-component of
  $\Theta^{-1}(g_1)$ (the compatibility of the global base change with the local maps, `quadBaseChange_snd_apply_over`).
* **`quatLocalUnit_mem_lamLocUnits`** ($\Lambda_E^\times\to\Lambda_w^\times$) and, where $\operatorname{disc}(1,\delta)$ is a $v$-unit,
  **`mem_lamEUnits_of_forall`** (the converse, from `localPi_image_integers`).
* **`nsU`**: $U_v = \varphi\{y\in G^\natural(F_v) : y_w\in\Lambda^{(m_w)}_w\ \forall w\mid v\}\subseteq SO(V)(F_v)$, and
  **`nsAdele_image_nsS0`**: $\Phi(\pi(S_0)) = G_\infty\times\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)$ for
  $S_0 = \{g : g_1\in H_S\}$, $S_K$ = the places over $S$.

Source: Weil 1982, §3.7, pp. 64-65 [unverified page]; Cassels–Fröhlich Ch. II §14 [unverified].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFib

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain Filter
open scoped ENNReal NNReal Quaternion RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat

noncomputable section

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))

/-! ### The local quaternion maps -/

section Local

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v)

local notation "Fv" => v.adicCompletion F

theorem quadLocalHom_algebraMap (c : Fv) :
    quadLocalHom hb₁ v w h (algebraMap Fv (QE (algebraMap F Fv (d : F))) c) = localRingHom v w h c := by
  show localRingHom v w h c + ((bK 1 : K) : w.adicCompletion K) * localRingHom v w h 0 = _
  rw [map_zero, mul_zero, add_zero]

include hα in
theorem quadLocalHom_a :
    quadLocalHom hb₁ v w h (algebraMap Fv (QE (algebraMap F Fv (d : F))) (algebraMap F Fv (a : F))) =
      algebraMap K (w.adicCompletion K) (α : K) := by
  rw [quadLocalHom_algebraMap, show algebraMap F Fv (a : F) = ((a : F) : Fv) from rfl, localRingHom_algebraMap, ← hα]
  rfl

include hα hβ in
/-- **$D_E\otimes F_v\to D'\otimes K_w$** for $w\mid v$. -/
def quatLocalHom : DEr Fv a b d →+* QuatV (α : K) (β : K) w :=
  QuaternionAlgebra.mapRingHom (quadLocalHom hb₁ v w h) (quadLocalHom_a hb₁ hα v w h) (map_zero _)
    (quadLocalHom_a hb₁ hβ v w h)

@[simp] theorem quatLocalHom_re (y : DEr Fv a b d) :
    (quatLocalHom hb₁ hα hβ v w h y).re = quadLocalHom hb₁ v w h y.re := rfl
@[simp] theorem quatLocalHom_imI (y : DEr Fv a b d) :
    (quatLocalHom hb₁ hα hβ v w h y).imI = quadLocalHom hb₁ v w h y.imI := rfl
@[simp] theorem quatLocalHom_imJ (y : DEr Fv a b d) :
    (quatLocalHom hb₁ hα hβ v w h y).imJ = quadLocalHom hb₁ v w h y.imJ := rfl
@[simp] theorem quatLocalHom_imK (y : DEr Fv a b d) :
    (quatLocalHom hb₁ hα hβ v w h y).imK = quadLocalHom hb₁ v w h y.imK := rfl

/-- The units version. -/
abbrev quatLocalUnit : DEK Fv a b d →* (QuatV (α : K) (β : K) w)ˣ :=
  Units.map (quatLocalHom hb₁ hα hβ v w h).toMonoidHom

/-- **The $w$-component of $x$ is `quatLocalHom` of the $v$-component of $\Theta^{-1}(x)$.** -/
theorem unitAtA_eq_quatLocalHom (x : (QuatAdele (α : K) (β : K))ˣ) :
    ((unitAtA (α : K) (β : K) w x : (QuatV (α : K) (β : K) w)ˣ) : QuatV (α : K) (β : K) w) =
      quatLocalHom hb₁ hα hβ v w h (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
        ((bcHom hb₀ hb₁ hα hβ x : (QuatQuadAdele F (d : F) (a : F) (b : F))ˣ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := by
  have e : quatBaseChange hb₀ hb₁ (a : F) (b : F)
      ((bcHom hb₀ hb₁ hα hβ x : (QuatQuadAdele F (d : F) (a : F) (b : F))ˣ) : QuatQuadAdele F (d : F) (a : F) (b : F)) =
      quatParamEquiv (diag_eq_of_eq hα) (diag_eq_of_eq hβ) (x : QuatAdele (α : K) (β : K)) :=
    RingEquiv.apply_symm_apply _ _
  set y := ((bcHom hb₀ hb₁ hα hβ x : (QuatQuadAdele F (d : F) (a : F) (b : F))ˣ) : QuatQuadAdele F (d : F) (a : F) (b : F))
  have hre := congrArg QuaternionAlgebra.re e
  have hI := congrArg QuaternionAlgebra.imI e
  have hJ := congrArg QuaternionAlgebra.imJ e
  have hK := congrArg QuaternionAlgebra.imK e
  simp only [quatBaseChange_re, quatBaseChange_imI, quatBaseChange_imJ, quatBaseChange_imK, quatParamEquiv_re,
    quatParamEquiv_imI, quatParamEquiv_imJ, quatParamEquiv_imK] at hre hI hJ hK
  rw [unitAtA_val]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · change (x : QuatAdele (α : K) (β : K)).re.2 w = _
    rw [← hre, quadBaseChange_snd_apply_over hb₀ hb₁ v w h]; rfl
  · change (x : QuatAdele (α : K) (β : K)).imI.2 w = _
    rw [← hI, quadBaseChange_snd_apply_over hb₀ hb₁ v w h]; rfl
  · change (x : QuatAdele (α : K) (β : K)).imJ.2 w = _
    rw [← hJ, quadBaseChange_snd_apply_over hb₀ hb₁ v w h]; rfl
  · change (x : QuatAdele (α : K) (β : K)).imK.2 w = _
    rw [← hK, quadBaseChange_snd_apply_over hb₀ hb₁ v w h]; rfl

/-! ### Integrality -/

include hb₁ in
theorem valued_delta_le_one : Valued.v ((bK 1 : K) : w.adicCompletion K) ≤ 1 := by
  have hd := valued_algebraMap_int_le_one w (algebraMap (𝓞 F) (𝓞 K) d)
  have e : (((algebraMap (𝓞 F) (𝓞 K) d : 𝓞 K) : K)) = bK 1 * bK 1 := hb₁.symm
  rw [e, map_mul, map_mul] at hd
  change Valued.v (algebraMap K (w.adicCompletion K) (bK 1)) ≤ 1
  by_contra hlt
  push_neg at hlt
  exact absurd hd (not_le.2 (one_lt_mul_of_lt_of_le hlt hlt.le))

theorem valued_quadLocalHom_le_one {z : QE (algebraMap F Fv (d : F))}
    (hz : QEInt (v.adicCompletionIntegers F).toSubring z) : Valued.v (quadLocalHom hb₁ v w h z) ≤ 1 := by
  show Valued.v (localRingHom v w h z.re + ((bK 1 : K) : w.adicCompletion K) * localRingHom v w h z.im) ≤ 1
  refine (Valued.v.map_add _ _).trans (max_le ?_ ?_)
  · exact localRingHom_valued_le_one v w h _ hz.1
  · rw [map_mul]
    exact mul_le_one' (valued_delta_le_one hb₁ w) (localRingHom_valued_le_one v w h _ hz.2)

theorem quatLocalHom_mem_lamLoc {y : DEr Fv a b d} (hy : DEInt (v.adicCompletionIntegers F).toSubring y) :
    quatLocalHom hb₁ hα hβ v w h y ∈ lamLoc (α : K) (β : K) w := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] <;>
    exact valued_quadLocalHom_le_one hb₁ v w h (by assumption)

/-- **$\Lambda_E^\times\to\Lambda_w^\times$.** -/
theorem quatLocalUnit_mem_lamLocUnits {y : DEK Fv a b d} (hy : y ∈ lamEUnits v a b d) :
    quatLocalUnit hb₁ hα hβ v w h y ∈ lamLocUnits (α : K) (β : K) w :=
  ⟨quatLocalHom_mem_lamLoc hb₁ hα hβ v w h hy.1, by
    rw [← map_inv]; exact quatLocalHom_mem_lamLoc hb₁ hα hβ v w h hy.2⟩

include hb₀ in
/-- **The converse where $\operatorname{disc}(1,\delta)$ is a $v$-unit**: if all $\varphi_w(z)$, $w\mid v$, are integral, so is $z$
(`localPi_image_integers`). -/
theorem qeInt_of_forall (hint : ∀ i, IsIntegral ℤ (bK i)) (hdisc : v.valuation F (Algebra.discr F bK) = 1)
    {z : QE (algebraMap F Fv (d : F))}
    (hz : ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v), Valued.v (quadLocalHom hb₁ v w h z) ≤ 1) :
    QEInt (v.adicCompletionIntegers F).toSubring z := by
  set c : Fin 2 → Fv := ![z.re, z.im]
  have hc : localPi bK v c ∈ intPlace (K := K) v := by
    intro w
    rw [localPi_apply, Fin.sum_univ_two, hb₀]
    have := hz w.1 w.2
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ((1 : K) : w.1.adicCompletion K) = algebraMap K (w.1.adicCompletion K) 1 from rfl, map_one, one_mul]
    exact this
  rw [← localPi_image_integers bK v hint hdisc] at hc
  obtain ⟨c', hc', hcc⟩ := hc
  have := localPi_injective bK v hcc
  rw [this] at hc'
  exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc' 0),
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc' 1)⟩

include hb₀ in
theorem DEInt_of_forall (hint : ∀ i, IsIntegral ℤ (bK i)) (hdisc : v.valuation F (Algebra.discr F bK) = 1)
    {y : DEr Fv a b d}
    (hy : ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
      quatLocalHom hb₁ hα hβ v w h y ∈ lamLoc (α : K) (β : K) w) :
    DEInt (v.adicCompletionIntegers F).toSubring y := by
  refine ⟨qeInt_of_forall hb₀ hb₁ v hint hdisc fun w h => ?_, qeInt_of_forall hb₀ hb₁ v hint hdisc fun w h => ?_,
    qeInt_of_forall hb₀ hb₁ v hint hdisc fun w h => ?_, qeInt_of_forall hb₀ hb₁ v hint hdisc fun w h => ?_⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy w h).1
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy w h).2.1
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy w h).2.2.1
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy w h).2.2.2

include hb₀ in
/-- **$y\in\Lambda_E^\times$ iff $y_w\in\Lambda_w^\times$ for all $w\mid v$** (where $\operatorname{disc}(1,\delta)$ is a $v$-unit). -/
theorem mem_lamEUnits_of_forall (hint : ∀ i, IsIntegral ℤ (bK i)) (hdisc : v.valuation F (Algebra.discr F bK) = 1)
    {y : DEK Fv a b d}
    (hy : ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
      quatLocalUnit hb₁ hα hβ v w h y ∈ lamLocUnits (α : K) (β : K) w) : y ∈ lamEUnits v a b d :=
  ⟨DEInt_of_forall hb₀ hb₁ hα hβ v hint hdisc fun w h => (hy w h).1,
   DEInt_of_forall hb₀ hb₁ hα hβ v hint hdisc fun w h => by
    have := (hy w h).2
    rw [← map_inv] at this
    exact this⟩

end Local

/-! ### The image of $S_0$ -/

section Box

variable (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (S : Finset (HeightOneSpectrum (𝓞 F))) (SK : Finset (HeightOneSpectrum (𝓞 K)))
  (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ

/-- $\{y\in G^\natural(F_v) : y_w\in\Lambda^{(m_w)}_w\ \forall w\mid v\}$. -/
def nsLoc (v : HeightOneSpectrum (𝓞 F)) : Set (GnK (v.adicCompletion F) a b d) :=
  {y | ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
    quatLocalUnit hb₁ hα hβ v w h (y : DEK (v.adicCompletion F) a b d) ∈ lamCong w α β (mK w) (hmK1 w)}

/-- **$U_v = \varphi(\{y : y_w\in\Lambda^{(m_w)}_w\ \forall w\mid v\})\subseteq SO(V)(F_v)$.** -/
def nsU (v : HeightOneSpectrum (𝓞 F)) : Set (Measure.SOv v (qNS a b d)) :=
  nsSOK (v.adicCompletion F) a b d ha0 hd0 '' nsLoc hb₁ hα hβ mK hmK1 v

theorem evalSO_nsAdele (g : (dN).G) (v : HeightOneSpectrum (𝓞 F)) :
    Measure.evalSO (qNS a b d) v (nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 g).2 =
      nsSOK (v.adicCompletion F) a b d ha0 hd0
        (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g) := rfl

theorem quatLocalUnit_nsPairV (g : (dN).G) (w : HeightOneSpectrum (𝓞 K)) :
    quatLocalUnit hb₁ hα hβ (underPlace w) w rfl
      (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (underPlace w) g : DEK ((underPlace (k := F) w).adicCompletion F) a b d) =
      unitAtA (α : K) (β : K) w (g : MK × (Adeles F)ˣ).1 :=
  Units.ext (unitAtA_eq_quatLocalHom hb₀ hb₁ hα hβ (underPlace w) w rfl _).symm

theorem quatLocalUnit_nsPairV' (g : (dN).G) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : underPlace (k := F) w = v) :
    quatLocalUnit hb₁ hα hβ v w h
      (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g : DEK (v.adicCompletion F) a b d) =
      unitAtA (α : K) (β : K) w (g : MK × (Adeles F)ˣ).1 := by
  subst h; exact quatLocalUnit_nsPairV hb₀ hb₁ hα hβ hα0 hβ0 g w

/-- Good places for the box. -/
def NSGoodPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
    Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1 ∧
      v.valuation F (Algebra.discr F bK) = 1

/-- The scalar idele with components $r_v$ ($v\in T$) and $1$ elsewhere. -/
def scalIdele (T : Finset (HeightOneSpectrum (𝓞 F))) (r : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) :
    (Adeles F)ˣ :=
  (idelesEquiv F).symm (1, ∏ v ∈ T, mulSingleAtHom v (r v))

open scoped Classical in
theorem scalIdele_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (r : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (u : HeightOneSpectrum (𝓞 F)) :
    ((scalIdele T r : (Adeles F)ˣ) : Adeles F).2 u = if u ∈ T then (r u : u.adicCompletion F) else 1 := by
  have e : ((scalIdele T r : (Adeles F)ˣ) : Adeles F).2 u =
      (unitAtHom u (∏ v ∈ T, mulSingleAtHom v (r v)) : u.adicCompletion F) := rfl
  rw [e, map_prod]
  split_ifs with hu
  · rw [Finset.prod_eq_single u (fun v _ hvu => by
      change unitAt (mulSingleAt v (r v)) u = 1; exact unitAt_mulSingleAt_of_ne (Ne.symm hvu) _)
      (fun h => absurd hu h)]
    change ((unitAt (mulSingleAt u (r u)) u : (u.adicCompletion F)ˣ) : u.adicCompletion F) = _
    rw [unitAt_mulSingleAt]
  · rw [Finset.prod_eq_one (fun v hv => by
      change unitAt (mulSingleAt v (r v)) u = 1
      exact unitAt_mulSingleAt_of_ne (fun h => hu (by rw [h]; exact hv)) _)]
    rfl

theorem nsPairV_zHom (c : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v ((dN).zHom c) : DEK (v.adicCompletion F) a b d) :
      DEr (v.adicCompletion F) a b d) = algebraMap (v.adicCompletion F) (DEr (v.adicCompletion F) a b d)
        ((c : Adeles F).2 v) := by
  rw [nsPairV_val]
  change deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
    ((nsUnit hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ((gnatBC bK 0 hb₀ (coeK_ne_zero hα0)
      (coeK_ne_zero hβ0)).zHom c) : _) : QuatQuadAdele F (d : F) (a : F) (b : F)) = _
  rw [nsUnit_zHom]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · refine QuadraticAlgebra.ext ?_ ?_ <;> rfl
  · refine QuadraticAlgebra.ext ?_ ?_ <;> simp <;> rfl
  · refine QuadraticAlgebra.ext ?_ ?_ <;> simp <;> rfl
  · refine QuadraticAlgebra.ext ?_ ?_ <;> simp <;> rfl

/-- Scalars of $D_E\otimes F_v$. -/
abbrev scalE (v : HeightOneSpectrum (𝓞 F)) (r : (v.adicCompletion F)ˣ) : DEK (v.adicCompletion F) a b d :=
  Units.map (algebraMap (v.adicCompletion F) (DEr (v.adicCompletion F) a b d)).toMonoidHom r

theorem scalE_comm (v : HeightOneSpectrum (𝓞 F)) (r : (v.adicCompletion F)ˣ) (x : DEK (v.adicCompletion F) a b d) :
    scalE v r * x = x * scalE v r :=
  Units.ext (Algebra.commutes _ _)

set_option maxHeartbeats 1600000 in
include hα0 hβ0 in
/-- Local rescalings of a lift of an element of the box. -/
theorem exists_local_rescale_ns (g : (dN).G)
    (hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v)
    (hbox : (nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 g).2 ∈
      Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ r : (v.adicCompletion F)ˣ,
      (∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
        quatLocalUnit hb₁ hα hβ v w h (scalE v r *
          (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g : DEK (v.adicCompletion F) a b d)) ∈
            lamLocUnits (α : K) (β : K) w) ∧
      (v ∈ S → ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
        quatLocalUnit hb₁ hα hβ v w h (scalE v r *
          (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g : DEK (v.adicCompletion F) a b d)) ∈
            lamCong w α β (mK w) (hmK1 w)) := by
  set p := nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g with hp
  by_cases hv : v ∈ S
  · obtain ⟨y, hy, hyX⟩ := hbox.1 v hv
    rw [evalSO_nsAdele hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0] at hyX
    have h1 : nsSOK (v.adicCompletion F) a b d ha0 hd0 (y⁻¹ * p) = 1 := by
      rw [map_mul, map_inv, hyX, inv_mul_cancel]
    obtain ⟨t, ht⟩ := (nsSOK_eq_one_iff ha0 hd0 _).1 h1
    have ht0 : t ≠ 0 := by
      rintro rfl
      have := ((y⁻¹ * p : GnK (v.adicCompletion F) a b d) : DEK (v.adicCompletion F) a b d).ne_zero
      rw [ht] at this; simp at this
    have hpy : (p : DEK (v.adicCompletion F) a b d) = (y : DEK (v.adicCompletion F) a b d) * scalE v (Units.mk0 t ht0) := by
      have e : ((y⁻¹ * p : GnK (v.adicCompletion F) a b d) : DEK (v.adicCompletion F) a b d) = scalE v (Units.mk0 t ht0) :=
        Units.ext ht
      have : (p : DEK (v.adicCompletion F) a b d) =
          (y : DEK (v.adicCompletion F) a b d) * ((y⁻¹ * p : GnK (v.adicCompletion F) a b d) : DEK (v.adicCompletion F) a b d) := by
        simp
      rw [this, e]
    have hry : scalE v (Units.mk0 t ht0)⁻¹ * (p : DEK (v.adicCompletion F) a b d) = (y : DEK (v.adicCompletion F) a b d) := by
      rw [hpy, ← mul_assoc, scalE_comm, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    refine ⟨(Units.mk0 t ht0)⁻¹, fun w h => ?_, fun _ w h => ?_⟩
    · rw [hry]; exact lamCong_subset mK hmK1 w (hy w h)
    · rw [hry]; exact hy w h
  · have hstd := hbox.2 v hv
    rw [evalSO_nsAdele hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0] at hstd
    obtain ⟨h2, hav, hbv, hdv, -⟩ := hgood v hv
    obtain ⟨r, hr⟩ := exists_smul_mem_lamEUnits v ha0 hd0 h2 hav hbv hdv p hstd
    exact ⟨r, fun w h => quatLocalUnit_mem_lamLocUnits hb₁ hα hβ v w h hr, fun h' => absurd h' hv⟩

set_option maxHeartbeats 3200000 in
include hα0 hβ0 in
/-- **$\Phi(\pi(S_0)) = G_\infty\times\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)$.** -/
@[kb "weil1982" "§3.7, pp. 64-65 [unverified page]"]
theorem nsAdele_image_nsS0 (hb0 : (b : F) ≠ 0) (hint : ∀ i, IsIntegral ℤ (bK i))
    (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) :
    nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 ''
        (nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) : Set (dN).G) =
      univ ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1) := by
  ext X
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' := (mem_HS α β SK mK hmK1).1 hg
    refine ⟨mem_univ _, fun v hv => ?_, fun v hv => ?_⟩
    · rw [evalSO_nsAdele hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0]
      refine ⟨_, fun w h => ?_, rfl⟩
      rw [quatLocalUnit_nsPairV' hb₀ hb₁ hα hβ hα0 hβ0 g v w h]
      exact hg'.2 w ((hSK w).2 (h ▸ hv))
    · rw [evalSO_nsAdele hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0]
      obtain ⟨h2, hav, hbv, hdv, hdisc⟩ := hgood v hv
      have hl := mem_lamEUnits_of_forall hb₀ hb₁ hα hβ v hint hdisc
        (y := (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g : DEK (v.adicCompletion F) a b d))
        (fun w h => by rw [quatLocalUnit_nsPairV' hb₀ hb₁ hα hβ hα0 hβ0 g v w h]; exact hg'.1 w)
      exact nsSOK_mem_stdStab v ha0 hd0 hav.le hbv.le hdv.le _ hl
  · rintro ⟨-, hbox⟩
    obtain ⟨g, rfl⟩ := nsAdele_surjective hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hb0 hd0 X
    choose r hr using exists_local_rescale_ns hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S mK hmK1 g hgood hbox
    have hev := eventually_deMap_mem_lamEUnits
      (nsUnit hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) g)
    classical
    set T := S ∪ (Filter.eventually_cofinite.mp hev).toFinset with hT
    have hnT : ∀ v ∉ T, v ∉ S ∧ (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) v g :
        DEK (v.adicCompletion F) a b d) ∈ lamEUnits v a b d := by
      intro v hv
      rw [hT, Finset.mem_union, not_or] at hv
      refine ⟨hv.1, ?_⟩
      by_contra hc
      exact hv.2 ((Set.Finite.mem_toFinset _).2 hc)
    set c := scalIdele T r
    refine ⟨(dN).zHom c * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_nsS0, mem_HS]
      have key : ∀ w : HeightOneSpectrum (𝓞 K), unitAtA (α : K) (β : K) w (((dN).zHom c * g : (dN).G) : MK × (Adeles F)ˣ).1 =
          quatLocalUnit hb₁ hα hβ (underPlace w) w rfl
            ((if underPlace (k := F) w ∈ T then scalE (underPlace w) (r (underPlace w)) else 1) *
              (nsPairV hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (underPlace w) g :
                DEK ((underPlace (k := F) w).adicCompletion F) a b d)) := by
        intro w
        rw [← quatLocalUnit_nsPairV hb₀ hb₁ hα hβ hα0 hβ0, map_mul, Subgroup.coe_mul]
        congr 2
        apply Units.ext
        rw [nsPairV_zHom, scalIdele_apply]
        split_ifs <;> simp
      refine ⟨fun w => ?_, fun w hw => ?_⟩
      · rw [key]
        split_ifs with hwT
        · exact (hr _).1 w rfl
        · rw [one_mul]
          exact quatLocalUnit_mem_lamLocUnits hb₁ hα hβ _ w rfl (hnT _ hwT).2
      · rw [key]
        have hvS := (hSK w).1 hw
        rw [if_pos (Finset.mem_union_left _ hvS)]
        exact (hr _).2 hvS w rfl
    · rw [map_mul]
      have : nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 ((dN).zHom c) = 1 := by
        rw [← MonoidHom.mem_ker, ker_nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0]
        exact ⟨c, rfl⟩
      rw [this, one_mul]

end Box

/-! ### $U_v$ is open -/

section SingleSO

variable {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

/-- **`singleSO` is continuous** (it factors through the principal piece $\prod_{w\ne v}SO(L_w)\times SO(V)(F_v)$). -/
theorem continuous_singleSO (v : HeightOneSpectrum (𝓞 F)) : Continuous (Measure.singleSO Q₀ v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]; exact (Set.finite_singleton v).compl_mem_cofinite
  let g : Measure.SOv v Q₀ → Πʳ w : HeightOneSpectrum (𝓞 F),
      [orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (w.adicCompletion F),
        stdStab (Q₀.map (algebraMap (𝓞 F) F)) w]_[Filter.principal ({v}ᶜ : Set _)] := fun x =>
    ⟨Pi.mulSingle v (x : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)), by
      rw [Filter.eventually_principal]
      intro w hw
      rw [Pi.mulSingle_eq_of_ne hw]
      exact (stdStab _ w).one_mem⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.2
    ((continuous_mulSingle v).comp continuous_subtype_val)
  have := (RestrictedProduct.continuous_inclusion hle).comp hg
  exact this.subtype_mk _

end SingleSO

section BoxOpen

variable (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (S : Finset (HeightOneSpectrum (𝓞 F))) (SK : Finset (HeightOneSpectrum (𝓞 K)))
  (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

theorem one_mem_nsU (v : HeightOneSpectrum (𝓞 F)) : (1 : Measure.SOv v (qNS a b d)) ∈ nsU hb₁ hα hβ ha0 hd0 mK hmK1 v :=
  ⟨1, fun w h => by rw [Subgroup.coe_one, map_one]; exact (lamCong w α β (mK w) (hmK1 w)).one_mem, map_one _⟩

theorem singleSO_mem_boxSO_iff {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (U : ∀ v, Set (Measure.SOv v Q₀))
    (hU : ∀ u ∈ S, (1 : Measure.SOv u Q₀) ∈ U u) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S)
    (x : Measure.SOv v Q₀) : Measure.singleSO Q₀ v x ∈ Measure.boxSO Q₀ S U ↔ x ∈ U v := by
  constructor
  · intro h
    have := h.1 v hv
    rwa [Measure.evalSO_singleSO_same] at this
  · intro hx
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · by_cases huv : u = v
      · subst huv; rw [Measure.evalSO_singleSO_same]; exact hx
      · rw [Measure.evalSO_singleSO_ne _ huv]; exact hU u hu
    · have huv : u ≠ v := fun h => hu (h ▸ hv)
      rw [Measure.evalSO_singleSO_ne _ huv]; exact (Measure.soStabSO u Q₀).one_mem

include hb₀ hα0 hβ0 in
theorem isOpen_nsU (hb0 : (b : F) ≠ 0) (hint : ∀ i, IsIntegral ℤ (bK i))
    (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ S) : IsOpen (nsU hb₁ hα hβ ha0 hd0 mK hmK1 v) := by
  have himg := nsAdele_image_nsS0 hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK mK hmK1 hb0 hint hSK hgood
  have ho : IsOpen ((univ : Set (GInfSO (qNS a b d))) ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1)) := by
    rw [← himg]
    exact isOpenMap_nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hb0 hd0 _
      (isOpen_nsS0 hb₀ hα0 hβ0 ((isOpen_quatCongS SK mK hmK1).preimage (continuous_quatFinPart α β)))
  have hbox : IsOpen (Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1)) := by
    have := isOpenMap_snd _ ho
    rwa [Set.snd_image_prod Set.univ_nonempty] at this
  have e : nsU hb₁ hα hβ ha0 hd0 mK hmK1 v =
      Measure.singleSO (qNS a b d) v ⁻¹' Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1) := by
    ext x
    exact (singleSO_mem_boxSO_iff S (qNS a b d) _ (fun u _ => one_mem_nsU hb₁ hα hβ ha0 hd0 mK hmK1 u) hv x).symm
  rw [e]
  exact hbox.preimage (continuous_singleSO _ v)

end BoxOpen

end

end QuadFormsKB.Tamagawa.Measure.Weil
