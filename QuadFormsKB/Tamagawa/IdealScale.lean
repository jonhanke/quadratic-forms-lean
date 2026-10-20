/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.LocalSmith

/-!
# Lattices scaled by ideles, and genus sums of non-free lattices

For an exponent vector $e = (e_\mathfrak p)$ with finite support (e.g. $e_\mathfrak p = \mathrm{ord}_\mathfrak p\mathfrak b$ for a fractional ideal
$\mathfrak b$) and a lattice $L \subseteq F^n$, **`scaleLat e L`** is the lattice glued from the local lattices $\varpi_\mathfrak p^{e_\mathfrak p}L_\mathfrak p$
(`LocFamily.glue`); for $e = \mathrm{ord}\,\mathfrak b$ it is $\mathfrak bL$, in general a **non-free** lattice. No class-number hypothesis.

**Proves**
* `loc_scaleLat`, `scaleLat_image` ($\gamma(\mathfrak bL) = \mathfrak b(\gamma L)$), `scaleLat_scaleLat`, `scaleLat_zero`, `scaleLat_le`;
* the genus calculus: `sameGenus_scaleLat`, `isIsometric_scaleLat_iff`, `autLat_scaleLat` ($O(\mathfrak bL) = O(L)$);
* **`repMass_scaleLat`**: $\mathrm{repMass}(\mathfrak bL, t) = \sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}r(\mathfrak bM, t)/|O(M)|$ — the genus of the
  non-free lattice $\mathfrak bL$ is the image of the genus of $L$, class by class, with the same automorphism groups;
* `mass_scaleLat` ($\mathrm{Mass}(\mathfrak bL) = \mathrm{Mass}(L)$).
-/

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices QuadForm LocalDensity

/-! ### Scalar matrices $\varpi^k$ -/

section Scalar

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem unifV_ne_zero : unifV v ≠ 0 := by
  intro h
  exact (NF.irreducible_π v).ne_zero (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))

theorem valued_unifV_zpow (k : ℤ) : Valued.v (unifV v ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, NF.valued_π, ← WithZero.exp_zsmul]
  congr 1; simp

/-- **The scalar matrix** $\varpi^k\cdot 1 \in \mathrm{GL}_n(F_\mathfrak p)$, $\varpi$ = `unifV v`, $k \in \mathbb Z$. -/
def scalGL (k : ℤ) : GL (Fin n) Fv :=
  Units.map (Matrix.scalar (Fin n) : Fv →+* Matrix (Fin n) (Fin n) Fv).toMonoidHom
    (Units.mk0 (unifV v ^ k) (zpow_ne_zero _ (unifV_ne_zero v)))

theorem scalGL_val (k : ℤ) : (scalGL (n := n) v k).val = Matrix.scalar (Fin n) (unifV v ^ k) := rfl

theorem scalGL_comm (k : ℤ) (g : GL (Fin n) Fv) : scalGL v k * g = g * scalGL v k := by
  ext1
  rw [Units.val_mul, Units.val_mul, scalGL_val]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

theorem scalGL_add (a b : ℤ) : scalGL (n := n) v (a + b) = scalGL v a * scalGL v b := by
  ext1
  rw [Units.val_mul, scalGL_val, scalGL_val, scalGL_val, zpow_add₀ (unifV_ne_zero v), map_mul]

theorem scalGL_zero : scalGL (n := n) v 0 = 1 := by
  ext1
  rw [scalGL_val, zpow_zero, map_one, Units.val_one]

theorem scalGL_mulVec (k : ℤ) (y : Fin n → Fv) : (scalGL v k).val *ᵥ y = unifV v ^ k • y := by
  rw [scalGL_val]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- $\varpi^k\,\mathfrak o_\mathfrak p^n$ is the ball of radius $e^{-k}$. -/
theorem locAct_scalGL_std (k : ℤ) : locAct v (scalGL v k) (std v : Submodule 𝔬 (Fin n → Fv)) = ball v k := by
  ext y
  rw [mem_locAct]
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [scalGL_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, valued_unifV_zpow]
    have := hz i
    rw [neg_zero, WithZero.exp_zero] at this
    calc WithZero.exp (-k) * Valued.v (z i) ≤ WithZero.exp (-k) * 1 := mul_le_mul_right this _
      _ = _ := mul_one _
  · intro hy
    refine ⟨unifV v ^ (-k) • y, fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, map_mul, valued_unifV_zpow, neg_zero, WithZero.exp_zero]
      calc WithZero.exp (-(-k)) * Valued.v (y i) ≤ WithZero.exp (-(-k)) * WithZero.exp (-k) :=
            mul_le_mul_right (hy i) _
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · rw [scalGL_mulVec, smul_smul, ← zpow_add₀ (unifV_ne_zero v), add_neg_cancel, zpow_zero, one_smul]

/-- For $k \ge 0$, $\varpi^k\Lambda \subseteq \Lambda$. -/
theorem locAct_scalGL_le {k : ℤ} (hk : 0 ≤ k) (Λ : Submodule 𝔬 (Fin n → Fv)) :
    locAct v (scalGL v k) Λ ≤ Λ := by
  rintro _ ⟨z, hz, rfl⟩
  show (scalGL v k).val *ᵥ z ∈ Λ
  rw [scalGL_mulVec]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  have : unifV v ^ (m : ℤ) • z = (NF.π v ^ m : 𝔬) • z := by
    rw [zpow_natCast]; rfl
  rw [this]
  exact Λ.smul_mem _ hz

end Scalar

/-! ### Scaling lattices by an idele $\varpi^e$ -/

section ScaleLat

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The local family $(\varpi_\mathfrak p^{e_\mathfrak p}L_\mathfrak p)_\mathfrak p$. -/
def scaleFamily (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0) (L : Lat F n) :
    LocFamily F n where
  M v := locAct v (scalGL v (e v)) (loc v L.1)
  isLattice v := locAct_isLattice _ (loc_isLattice v L.2)
  eventually_std := by
    filter_upwards [he, loc_eventually_std L.2] with v hv hL
    rw [hv, hL, scalGL_zero, locAct_one]

/-- **The lattice $\varpi^eL$** with localizations $\varpi_\mathfrak p^{e_\mathfrak p}L_\mathfrak p$ ($= \mathfrak bL$ for $e = \mathrm{ord}\,\mathfrak b$; O'Meara §81
[unverified]). In general not free. -/
@[kb "omeara1963" "§81 (lattices from local data; aL for a fractional ideal a) [unverified]"]
def scaleLat (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0) (L : Lat F n) : Lat F n :=
  ⟨(scaleFamily e he L).glue, (scaleFamily e he L).glue_isLattice⟩

variable (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0)

theorem loc_scaleLat (L : Lat F n) (v : HeightOneSpectrum (𝓞 F)) :
    loc v (scaleLat e he L).1 = locAct v (scalGL v (e v)) (loc v L.1) :=
  (scaleFamily e he L).loc_glue v

theorem mem_scaleLat (L : Lat F n) (x : Fin n → F) :
    x ∈ (scaleLat e he L).1 ↔ ∀ v, locVec v x ∈ locAct v (scalGL v (e v)) (loc v L.1) := Iff.rfl

theorem scaleLat_image (γ : GL (Fin n) F) (L : Lat F n) :
    scaleLat e he (Lat.image γ L) = Lat.image γ (scaleLat e he L) :=
  Subtype.ext <| loc_injective (scaleLat e he _).2 (Lat.image γ _).2 fun v => by
    rw [loc_scaleLat, show (Lat.image γ L).1 = glImage γ L.1 from rfl,
      show (Lat.image γ (scaleLat e he L)).1 = glImage γ (scaleLat e he L).1 from rfl, loc_glImage, loc_glImage,
      loc_scaleLat, ← locAct_mul, ← locAct_mul, scalGL_comm]

include he in
theorem eventually_add {e' : HeightOneSpectrum (𝓞 F) → ℤ} (he' : ∀ᶠ v in Filter.cofinite, e' v = 0) :
    ∀ᶠ v in Filter.cofinite, (e + e') v = 0 :=
  (he.and he').mono fun v h => by simp [h.1, h.2]

include he in
theorem eventually_neg : ∀ᶠ v in Filter.cofinite, (-e) v = 0 := he.mono fun v h => by simp [h]

theorem scaleLat_scaleLat {e' : HeightOneSpectrum (𝓞 F) → ℤ} (he' : ∀ᶠ v in Filter.cofinite, e' v = 0)
    (L : Lat F n) : scaleLat e he (scaleLat e' he' L) = scaleLat (e + e') (eventually_add e he he') L :=
  Subtype.ext <| loc_injective (scaleLat e he _).2 (scaleLat _ _ _).2 fun v => by
    rw [loc_scaleLat, loc_scaleLat, loc_scaleLat, ← locAct_mul, ← scalGL_add, Pi.add_apply]

theorem scaleLat_zero (he0 : ∀ᶠ v in Filter.cofinite, (0 : HeightOneSpectrum (𝓞 F) → ℤ) v = 0)
    (L : Lat F n) : scaleLat 0 he0 L = L :=
  Subtype.ext <| loc_injective (scaleLat _ _ _).2 L.2 fun v => by
    rw [loc_scaleLat, Pi.zero_apply, scalGL_zero, locAct_one]

theorem scaleLat_congr {e' : HeightOneSpectrum (𝓞 F) → ℤ} (h : e = e')
    (he' : ∀ᶠ v in Filter.cofinite, e' v = 0) (L : Lat F n) : scaleLat e he L = scaleLat e' he' L := by
  subst h; rfl

theorem scaleLat_neg_scaleLat (L : Lat F n) : scaleLat (-e) (eventually_neg e he) (scaleLat e he L) = L := by
  rw [scaleLat_scaleLat]
  exact (scaleLat_congr _ _ (e' := 0) (by simp) (Filter.Eventually.of_forall fun _ => rfl) L).trans
    (scaleLat_zero _ L)

theorem scaleLat_injective : Function.Injective (scaleLat (n := n) e he) := fun L M h => by
  rw [← scaleLat_neg_scaleLat e he L, h, scaleLat_neg_scaleLat]

/-- For $e \ge 0$ (an integral ideal), $\varpi^eL \subseteq L$. -/
theorem scaleLat_le (hpos : ∀ v, 0 ≤ e v) (L : Lat F n) : (scaleLat e he L).1 ≤ L.1 := fun x hx =>
  (mem_iff_forall_loc L.2 x).mpr fun v => locAct_scalGL_le v (hpos v) _ (hx v)

variable {e he}

theorem isIntegral_scaleLat (Q : QuadForm F n) (hpos : ∀ v, 0 ≤ e v) {L : Lat F n} (hL : IsIntegral Q L.1) :
    IsIntegral Q (scaleLat e he L).1 := fun x hx => hL x (scaleLat_le e he hpos L hx)

variable (Q : QuadForm F n) (e he)

theorem sameGenus_scaleLat {L M : Lat F n} (h : SameGenus Q L.1 M.1) :
    SameGenus Q (scaleLat e he L).1 (scaleLat e he M).1 := fun v => by
  obtain ⟨g, hg, hgL⟩ := h v
  refine ⟨g, hg, ?_⟩
  rw [loc_scaleLat, loc_scaleLat, ← locAct_mul, ← scalGL_comm, locAct_mul, hgL]

theorem isIsometric_scaleLat {L M : Lat F n} (h : IsIsometric Q L.1 M.1) :
    IsIsometric Q (scaleLat e he L).1 (scaleLat e he M).1 := by
  obtain ⟨γ, hγ, hγL⟩ := h
  refine ⟨γ, hγ, ?_⟩
  have hM : Lat.image γ L = M := Subtype.ext hγL
  show (Lat.image γ (scaleLat e he L)).1 = _
  rw [← scaleLat_image, hM]

theorem isIsometric_scaleLat_iff {L M : Lat F n} :
    IsIsometric Q (scaleLat e he L).1 (scaleLat e he M).1 ↔ IsIsometric Q L.1 M.1 := by
  refine ⟨fun h => ?_, isIsometric_scaleLat e he Q⟩
  have := isIsometric_scaleLat (-e) (eventually_neg e he) Q h
  rwa [scaleLat_neg_scaleLat, scaleLat_neg_scaleLat] at this

theorem sameGenus_scaleLat_iff {L M : Lat F n} :
    SameGenus Q (scaleLat e he L).1 (scaleLat e he M).1 ↔ SameGenus Q L.1 M.1 := by
  refine ⟨fun h => ?_, sameGenus_scaleLat e he Q⟩
  have := sameGenus_scaleLat (-e) (eventually_neg e he) Q h
  rwa [scaleLat_neg_scaleLat, scaleLat_neg_scaleLat] at this

/-- **$O(\varpi^eL) = O(L)$.** -/
theorem autLat_scaleLat (L : Lat F n) : autLat Q (scaleLat e he L).1 = autLat Q L.1 := by
  ext γ
  show glImage (γ : GL (Fin n) F) (scaleLat e he L).1 = (scaleLat e he L).1 ↔ glImage (γ : GL (Fin n) F) L.1 = L.1
  have h1 : glImage (γ : GL (Fin n) F) (scaleLat e he L).1 = (scaleLat e he (Lat.image γ L)).1 := by
    rw [scaleLat_image]; rfl
  rw [h1]
  constructor
  · intro h
    have := scaleLat_injective e he (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro h
    rw [show Lat.image (γ : GL (Fin n) F) L = L from Subtype.ext h]

end ScaleLat

/-! ### Genus sums of scaled lattices -/

section GenusSums

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
  (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0)

/-- The map $\mathrm{cls}(M) \mapsto \mathrm{cls}(\varpi^eM)$ on classes. -/
def classScale : LatClass Q → LatClass Q :=
  Quotient.map (scaleLat e he) fun _ _ h => isIsometric_scaleLat e he Q h

theorem classScale_mk (M : Lat F n) : classScale Q e he (Quotient.mk _ M) = Quotient.mk _ (scaleLat e he M) := rfl

theorem classScale_neg (c : LatClass Q) : classScale Q (-e) (eventually_neg e he) (classScale Q e he c) = c := by
  induction c using Quotient.inductionOn with
  | h M => rw [classScale_mk, classScale_mk, scaleLat_neg_scaleLat]

theorem classScale_mem (L : Lat F n) {c : LatClass Q} (hc : c ∈ genusClasses Q L) :
    classScale Q e he c ∈ genusClasses Q (scaleLat e he L) := by
  obtain ⟨M, rfl, hM⟩ := hc
  exact ⟨scaleLat e he M, rfl, sameGenus_scaleLat e he Q hM⟩

theorem bijOn_classScale (L : Lat F n) :
    Set.BijOn (classScale Q e he) (genusClasses Q L) (genusClasses Q (scaleLat e he L)) := by
  refine ⟨fun c hc => classScale_mem Q e he L hc, ?_, fun c hc => ?_⟩
  · intro c _ c' _ h
    rw [← classScale_neg Q e he c, h, classScale_neg]
  · refine ⟨classScale Q (-e) (eventually_neg e he) c, ?_, ?_⟩
    · have := classScale_mem Q (-e) (eventually_neg e he) (scaleLat e he L) hc
      rwa [scaleLat_neg_scaleLat] at this
    · have := classScale_neg Q (-e) (eventually_neg e he) c
      simp only [neg_neg] at this
      exact this

theorem autCard_classScale (c : LatClass Q) : LatClass.autCard Q (classScale Q e he c) = LatClass.autCard Q c := by
  induction c using Quotient.inductionOn with
  | h M =>
    show Nat.card (autLat Q (scaleLat e he M).1) = Nat.card (autLat Q M.1)
    rw [autLat_scaleLat]

theorem repCount_classScale (c : LatClass Q) (t : F) :
    LatClass.repCount Q (classScale Q e he c) t = repCount Q (scaleLat e he c.out) t := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The genus sum of the non-free lattice $\varpi^eL$** (O'Meara §102 [unverified]):
$$\mathrm{repMass}(\varpi^eL, t) = \sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r(\varpi^eM, t)}{|O(M)|}.$$ -/
@[kb "omeara1963" "§102 (genus of aL) [unverified]"]
theorem repMass_scaleLat (L : Lat F n) (t : F) :
    repMass Q (scaleLat e he L) t =
      ∑ᶠ c ∈ genusClasses Q L, (repCount Q (scaleLat e he c.out) t : ℝ) / LatClass.autCard Q c := by
  unfold repMass
  refine (finsum_mem_eq_of_bijOn (classScale Q e he) (bijOn_classScale Q e he L) fun c _ => ?_).symm
  rw [repCount_classScale, autCard_classScale]

/-- **$\mathrm{Mass}(\varpi^eL) = \mathrm{Mass}(L)$.** -/
theorem mass_scaleLat (L : Lat F n) : mass Q (scaleLat e he L) = mass Q L := by
  unfold mass
  refine (finsum_mem_eq_of_bijOn (classScale Q e he) (bijOn_classScale Q e he L) fun c _ => ?_).symm
  rw [autCard_classScale]

end GenusSums

end QuadFormsKB.Tamagawa
