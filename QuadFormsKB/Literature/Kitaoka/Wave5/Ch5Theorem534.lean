/-
# Kitaoka 1993, Theorem 5.3.4: extending isometries of sublattices over $\mathbb Z_p$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.3, Theorem 5.3.4 and its proof, p. 82 (printed
page). The statement `Kitaoka.Padic.Theorem534` is in `Ch5Extension.lean`.

**Proves** `theorem534 : Theorem534` (unconditional).

**Proof** (Kitaoka's). For $x \in M$, $h = \sigma(x) - x \in L^a$ and $Q(h) = -2B(h, x) \in (2a)$, so $h \in L_a$. Put
$H = L_a$ and $q = (2a)^{-1}Q$, so that $b(x, y) = a^{-1}B(x, y)$; then $q(H) \subseteq R$, $b(L, H) \subseteq R$ and the
hypotheses (3) of Theorem 5.3.4 are (2) of Theorem 1.2.2. Kneser's theorem with $R = \mathbb Z_p$, $\tilde R = \mathbb Q_p$,
$U = \mathbb Q_p^n$ (`Kitaoka.Kneser.kneser_U`) gives the extension. (Kitaoka's text reads "$\tilde R = R$", but the
values of $q$ lie in $F$.) $M$ is free: a finitely generated torsion-free module over the principal ideal domain
$\mathbb Z_p$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1KneserMain
import QuadFormsKB.Literature.Kitaoka.Ch5Extension
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Noetherian.Basic

open QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- $L_a$ as a $\mathbb Z_p$-submodule. -/
def lowerLSub (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (L : Submodule ℤ_[p] (Fin n → ℚ_[p])) (a : ℚ_[p]) :
    Submodule ℤ_[p] (Fin n → ℚ_[p]) where
  carrier := lowerL Q L a
  add_mem' := by
    rintro x y ⟨⟨hxL, hxB⟩, ⟨r, hr⟩⟩ ⟨⟨hyL, hyB⟩, ⟨s, hs⟩⟩
    refine ⟨⟨L.add_mem hxL hyL, fun z hz => ?_⟩, ?_⟩
    · obtain ⟨r1, h1⟩ := hxB z hz
      obtain ⟨r2, h2⟩ := hyB z hz
      refine ⟨r1 + r2, ?_⟩
      simp only [pbil, polar_add_left, add_div] at h1 h2 ⊢
      rw [h1, h2]; push_cast; ring
    · obtain ⟨t, ht⟩ := hxB y hyL
      refine ⟨r + s + t, ?_⟩
      have e : Q (x + y) = Q x + Q y + 2 * pbil Q x y := by
        simp only [pbil]; rw [QuadraticMap.map_add Q]; ring
      rw [e, hr, hs, ht]; push_cast; ring
  zero_mem' := ⟨⟨L.zero_mem, fun z _ => ⟨0, by simp [pbil]⟩⟩, ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨⟨hxL, hxB⟩, ⟨r, hr⟩⟩
    refine ⟨⟨L.smul_mem c hxL, fun z hz => ?_⟩, ⟨c * c * r, ?_⟩⟩
    · obtain ⟨r1, h1⟩ := hxB z hz
      refine ⟨c * r1, ?_⟩
      rw [← algebraMap_smul ℚ_[p] c x]
      simp only [pbil, polar_smul_left, smul_eq_mul] at h1 ⊢
      rw [mul_div_assoc, h1]; push_cast; simp [PadicInt.coe_mul]; ring
    · rw [← algebraMap_smul ℚ_[p] c x, QuadraticMap.map_smul, smul_eq_mul, hr]
      push_cast; simp [PadicInt.coe_mul]; ring

theorem polar_scaled (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) {a : ℚ_[p]} (x y : Fin n → ℚ_[p]) :
    polar ((2 * a)⁻¹ • Q) x y = a⁻¹ * pbil Q x y := by
  simp only [polar, pbil, QuadraticMap.smul_apply, smul_eq_mul]
  field_simp
  first | done | ring

/-- **Kitaoka 1993, Theorem 5.3.4** (p. 82): `Theorem534`. Unconditional. -/
@[kb "kitaoka1993" "§5.3, Thm. 5.3.4, p. 82 (proof)"]
theorem theorem534 : Theorem534 := by
  intro p _ n Q L M N a _ hL hM hN ha h3a _ h3b _ σ hσq hσ
  classical
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have h2a : (2 * a) ≠ 0 := mul_ne_zero h2 ha
  set q := (2 * a)⁻¹ • Q with hqdef
  set H := lowerLSub Q L a
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  -- $M$ is finitely generated and free
  have hLfg : L.FG := hL.fg
  have hMfg : M.FG := by
    have : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hLfg
    have : IsNoetherian ℤ_[p] L := inferInstance
    have hfg := IsNoetherian.noetherian (M.comap L.subtype)
    have := hfg.map L.subtype
    rwa [Submodule.map_comap_eq_of_le (by simpa using hM)] at this
  have hMfin : Module.Finite ℤ_[p] M := Module.Finite.iff_fg.mpr hMfg
  have hMtf : Module.IsTorsionFree ℤ_[p] M := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    apply Subtype.ext
    have h1 := congrArg (fun z : M => (z : Fin n → ℚ_[p])) hxy
    simp only [Submodule.coe_smul] at h1
    rw [← algebraMap_smul ℚ_[p] r (x : Fin n → ℚ_[p]), ← algebraMap_smul ℚ_[p] r (y : Fin n → ℚ_[p])] at h1
    have hr' : algebraMap ℤ_[p] ℚ_[p] r ≠ 0 := fun h => hr0 (hinj (h.trans (map_zero _).symm))
    exact smul_right_injective _ hr' h1
  have hMfree : Module.Free ℤ_[p] M := Module.free_of_finite_type_torsion_free'
  -- the hypotheses of Kneser's theorem
  have hHL : H ≤ L := fun x hx => hx.1.1
  have h1q : ∀ h ∈ H, q h ∈ (algebraMap ℤ_[p] ℚ_[p]).range := by
    rintro h ⟨-, ⟨r, hr⟩⟩
    refine ⟨r, ?_⟩
    rw [hqdef, QuadraticMap.smul_apply, smul_eq_mul, hr]
    field_simp
    rfl
  have h1b : ∀ x ∈ L, ∀ h ∈ H, polar q x h ∈ (algebraMap ℤ_[p] ℚ_[p]).range := by
    rintro x hx h ⟨⟨-, hB⟩, -⟩
    obtain ⟨r, hr⟩ := hB x hx
    refine ⟨r, ?_⟩
    rw [hqdef, polar_scaled, show pbil Q x h = pbil Q h x by simp [pbil, polar_comm], hr]
    field_simp
    rfl
  have h2a' : ∀ f : M →ₗ[ℤ_[p]] ℤ_[p], ∃ y ∈ H, ∀ x : M, algebraMap ℤ_[p] ℚ_[p] (f x) = polar q x y := by
    intro f
    obtain ⟨y, hy, hy'⟩ := h3a f
    exact ⟨y, hy, fun x => by rw [hqdef, polar_scaled, ← hy' x]; rfl⟩
  have h2b' : ∀ f : N →ₗ[ℤ_[p]] ℤ_[p], ∃ y ∈ H, ∀ x : N, algebraMap ℤ_[p] ℚ_[p] (f x) = polar q x y := by
    intro f
    obtain ⟨y, hy, hy'⟩ := h3b f
    exact ⟨y, hy, fun x => by rw [hqdef, polar_scaled, ← hy' x]; rfl⟩
  have hσq' : ∀ x, q (σ x) = q x := fun x => by rw [hqdef, QuadraticMap.smul_apply, hσq]; rfl
  have hσH : ∀ x : M, (σ x : Fin n → ℚ_[p]) - x ∈ H := by
    intro x
    refine ⟨hσ x, ?_⟩
    obtain ⟨hhL, hhB⟩ := hσ x
    obtain ⟨r, hr⟩ := hhB x (hM x.2)
    refine ⟨-r, ?_⟩
    have e : Q (σ x) = Q ((σ x : Fin n → ℚ_[p]) - x) + 2 * pbil Q ((σ x : Fin n → ℚ_[p]) - x) x + Q x := by
      have : (σ x : Fin n → ℚ_[p]) = ((σ x : Fin n → ℚ_[p]) - x) + x := by abel
      conv_lhs => rw [this]
      simp only [pbil]; rw [QuadraticMap.map_add Q]; ring
    rw [hσq] at e
    have : Q ((σ x : Fin n → ℚ_[p]) - x) = -2 * pbil Q ((σ x : Fin n → ℚ_[p]) - x) x := by linear_combination -e
    rw [this, hr, PadicInt.coe_neg]; ring
  obtain ⟨τ, hτq, hτL, hτL', hτσ, -, hτH⟩ :=
    Kneser.kneser_U q L M N H hinj hMfg hMfree hM hN hHL h1q h1b h2a' h2b' σ hσq' hσH
  refine ⟨τ, fun x => ?_, hτL, hτL', hτσ, fun x hx => hτH x hx⟩
  have := hτq x
  rw [hqdef, QuadraticMap.smul_apply, QuadraticMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
  exact mul_left_cancel₀ (inv_ne_zero h2a) this

end QuadFormsKB.Kitaoka.Padic
