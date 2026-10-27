import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Lattices.Basic

/-!
# The norm form of a quadratic extension $E/F$ and its isometries

Let $E/F$ be a quadratic extension of fields of characteristic $0$ (Mathlib's `Algebra.IsQuadraticExtension F E`),
$\sigma$ its nontrivial automorphism (`conj F E`), $N = N_{E/F}$ and $\mathrm{Tr} = \mathrm{Tr}_{E/F}$. Then
$N(x) = x\,\sigma(x)$ and $\mathrm{Tr}(x) = x + \sigma(x)$ (`algebraMap_norm`, `algebraMap_trace`), and $N$ is a quadratic form on
the $2$-dimensional $F$-space $E$ (`normForm F E`) with polar form $B(x, y) = \mathrm{Tr}(x\,\sigma(y))$ (`polar_normForm`).

**Similitudes of the norm form** (`linear_similitude`): an $F$-linear $\varphi : E \to E$ with $N(\varphi x) = a\,N(x)$ for all $x$,
$a \ne 0$, is $x \mapsto \lambda x$ or $x \mapsto \lambda\,\sigma(x)$ with $\lambda = \varphi(1)$, $N(\lambda) = a$. In particular the
orthogonal group of $(E, N)$ is $\{x \mapsto ux\} \sqcup \{x \mapsto u\,\sigma(x)\}$, $N(u) = 1$ (O'Meara §57 for the
norm form of a quadratic extension as a binary space [unverified locator]; Shimura, *Arithmetic of Quadratic Forms*,
§4 [unverified locator]). Proof: $\psi = \lambda^{-1}\varphi$ fixes $1$ and preserves $N$, hence (polarize at $1$) also
$\mathrm{Tr}$; so $\psi(x)$ is a root of $X^2 - \mathrm{Tr}(x)X + N(x) = (X - x)(X - \sigma x)$; and a linear map with
$\psi(x) \in \{x, \sigma x\}$ for every $x$ is $\mathrm{id}$ or $\sigma$ (a vector space is not a union of two proper
subspaces).

**Lattices** (`isometricLattices_iff`): for $\mathcal O_F$-submodules $L, L' \subseteq E$ ($F$ a number field) and
$c, c' \in F^\times$, the lattices $(L, cN)$ and $(L', c'N)$ are isometric (the repository's `IsometricLattices`) iff
$$L' = \lambda L\quad\text{or}\quad L' = \lambda\,\sigma(L)\qquad\text{for some }\lambda \in E^\times\text{ with }c'\,N(\lambda) = c .$$
-/

open NumberField Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-! ### The nontrivial automorphism -/

section Conj

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [CharZero F] [Algebra.IsQuadraticExtension F E]

theorem charZero_top (F E : Type*) [Field F] [Field E] [Algebra F E] [CharZero F] : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective

instance : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)

theorem card_aut : Nat.card (E ≃ₐ[F] E) = 2 :=
  (IsGalois.card_aut_eq_finrank F E).trans (Algebra.IsQuadraticExtension.finrank_eq_two F E)

theorem exists_aut_ne_one : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 := by
  have h := card_aut F E
  rw [Nat.card_eq_two_iff' 1] at h
  obtain ⟨σ, hσ, -⟩ := h
  exact ⟨σ, hσ⟩

/-- **The nontrivial automorphism** $\sigma$ of the quadratic extension $E/F$ ("conjugation"). -/
@[kb "neukirch1999" "Ch. I §8 (Galois group of a quadratic extension) [unverified]"]
def conj : E ≃ₐ[F] E := (exists_aut_ne_one F E).choose

theorem conj_ne_one : conj F E ≠ 1 := (exists_aut_ne_one F E).choose_spec

theorem eq_one_or_eq_conj (g : E ≃ₐ[F] E) : g = 1 ∨ g = conj F E := by
  have h := card_aut F E
  rw [Nat.card_eq_two_iff' 1] at h
  obtain ⟨σ, _, hu⟩ := h
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr ((hu g hg).trans (hu _ (conj_ne_one F E)).symm)

variable {F E}

@[simp]
theorem conj_conj (x : E) : conj F E (conj F E x) = x := by
  have h : conj F E * conj F E = 1 := by
    rcases eq_one_or_eq_conj F E (conj F E * conj F E) with h | h
    · exact h
    · exfalso
      apply conj_ne_one F E
      have := congrArg (fun g => (conj F E)⁻¹ * g) h
      simpa using this
  exact congrArg (fun g : E ≃ₐ[F] E => g x) h

open Classical in
theorem univ_aut : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, conj F E} := by
  ext g
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_one_or_eq_conj F E g

/-- $N_{E/F}(x) = x\,\sigma(x)$ (Mathlib's `Algebra.norm_eq_prod_automorphisms`). -/
theorem algebraMap_norm (x : E) : algebraMap F E (Algebra.norm F x) = x * conj F E x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_aut, Finset.prod_insert (by
    simpa [eq_comm] using conj_ne_one F E), Finset.prod_singleton]
  rfl

/-- $\mathrm{Tr}_{E/F}(x) = x + \sigma(x)$. -/
theorem algebraMap_trace (x : E) : algebraMap F E (Algebra.trace F E x) = x + conj F E x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_aut, Finset.sum_insert (by
    simpa [eq_comm] using conj_ne_one F E), Finset.sum_singleton]
  rfl

theorem norm_conj (x : E) : Algebra.norm F (conj F E x) = Algebra.norm F x := by
  apply (algebraMap F E).injective
  rw [algebraMap_norm, algebraMap_norm, conj_conj, mul_comm]

/-- The fixed elements of $\sigma$ are those of $F$. -/
theorem conj_eq_self_iff (x : E) : conj F E x = x ↔ ∃ a : F, algebraMap F E a = x := by
  have := charZero_top F E
  constructor
  · intro h
    refine ⟨Algebra.trace F E x / 2, ?_⟩
    rw [map_div₀, algebraMap_trace, h, map_ofNat]
    have : (2 : E) ≠ 0 := two_ne_zero
    field_simp
    ring
  · rintro ⟨a, rfl⟩
    exact (conj F E).commutes a

/-- **The two roots.** If $N(z) = N(x)$ and $\mathrm{Tr}(z) = \mathrm{Tr}(x)$ then $z = x$ or $z = \sigma(x)$:
$(z - x)(z - \sigma x) = z^2 - \mathrm{Tr}(x)z + N(x) = z^2 - \mathrm{Tr}(z)z + N(z) = 0$. -/
theorem eq_or_eq_conj_of_norm_trace {x z : E} (hn : Algebra.norm F z = Algebra.norm F x)
    (ht : Algebra.trace F E z = Algebra.trace F E x) : z = x ∨ z = conj F E x := by
  have hn' := congrArg (algebraMap F E) hn
  have ht' := congrArg (algebraMap F E) ht
  rw [algebraMap_norm, algebraMap_norm] at hn'
  rw [algebraMap_trace, algebraMap_trace] at ht'
  have h0 : (z - x) * (z - conj F E x) = 0 := by
    have e : (z - x) * (z - conj F E x) = z * z - (x + conj F E x) * z + x * conj F E x := by ring
    rw [e, ← ht', ← hn']
    ring
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

end Conj

/-! ### The norm form -/

section NormForm

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [CharZero F] [Algebra.IsQuadraticExtension F E]

/-- The polar form $B(x, y) = \mathrm{Tr}_{E/F}(x\,\sigma(y))$ of the norm form, as an $F$-bilinear map. -/
def normPolar : LinearMap.BilinForm F E :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F E (x * conj F E y))
    (fun x x' y => by rw [add_mul, map_add])
    (fun a x y => by rw [smul_mul_assoc, map_smul, smul_eq_mul])
    (fun x y y' => by rw [map_add, mul_add, map_add])
    (fun a x y => by rw [map_smul, mul_smul_comm, map_smul, smul_eq_mul])

theorem normPolar_apply (x y : E) : normPolar F E x y = Algebra.trace F E (x * conj F E y) := rfl

variable {F E} in
theorem norm_add (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + Algebra.trace F E (x * conj F E y) := by
  apply (algebraMap F E).injective
  rw [algebraMap_norm, RingHom.map_add, RingHom.map_add, algebraMap_norm, algebraMap_norm, algebraMap_trace,
    map_add, map_mul, conj_conj]
  ring

/-- **The norm form** $N = N_{E/F}$ of a quadratic extension, as a quadratic form on the $2$-dimensional $F$-space $E$:
$N(x) = x\,\sigma(x)$, with polar form $B(x, y) = \mathrm{Tr}_{E/F}(x\,\sigma(y))$ (`polar_normForm`). -/
@[kb "omeara1963" "§57 (norm form of a quadratic extension) [unverified]"]
def normForm : QuadraticForm F E where
  toFun x := Algebra.norm F x
  toFun_smul a x := by
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      smul_eq_mul, sq]
  exists_companion' := ⟨normPolar F E, fun x y => norm_add x y⟩

variable {F E}

@[simp]
theorem normForm_apply (x : E) : normForm F E x = Algebra.norm F x := rfl

theorem polar_normForm (x y : E) :
    QuadraticMap.polar (normForm F E) x y = Algebra.trace F E (x * conj F E y) := by
  rw [QuadraticMap.polar, normForm_apply, normForm_apply, normForm_apply, norm_add]
  ring

end NormForm

/-! ### Similitudes of the norm form -/

section Similitude

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F] [Algebra.IsQuadraticExtension F E]

/-- **Similitudes of the norm form.** An $F$-linear map $\varphi : E \to E$ with $N(\varphi x) = a\,N(x)$ for all $x$, where
$a \ne 0$, is $x \mapsto \lambda x$ or $x \mapsto \lambda\,\sigma(x)$ with $\lambda = \varphi(1)$; then $N(\lambda) = a$. -/
@[kb "omeara1963" "§57 (norm form of a quadratic extension) [unverified]"]
theorem linear_similitude (φ : E →ₗ[F] E) {a : F} (ha : a ≠ 0)
    (h : ∀ x, Algebra.norm F (φ x) = a * Algebra.norm F x) :
    (∀ x, φ x = φ 1 * x) ∨ (∀ x, φ x = φ 1 * conj F E x) := by
  set l := φ 1 with hl
  have hNl : Algebra.norm F l = a := by rw [hl, h, map_one, mul_one]
  have hl0 : l ≠ 0 := by
    intro h0; rw [h0, Algebra.norm_eq_zero_iff.mpr rfl] at hNl; exact ha hNl.symm
  -- ψ = l⁻¹ φ
  set ψ : E → E := fun x => l⁻¹ * φ x with hψ
  have hψ1 : ψ 1 = 1 := by simp [hψ, ← hl, hl0]
  have hψadd : ∀ x y, ψ (x + y) = ψ x + ψ y := fun x y => by simp [hψ, mul_add]
  have hψsmul : ∀ (c : F) x, ψ (c • x) = c • ψ x := fun c x => by
    simp only [hψ]; rw [map_smul, Algebra.smul_def, Algebra.smul_def]; ring
  have hNψ : ∀ x, Algebra.norm F (ψ x) = Algebra.norm F x := fun x => by
    have hNli : Algebra.norm F l⁻¹ = a⁻¹ := by
      rw [← hNl]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, inv_mul_cancel₀ hl0, map_one]
    simp only [hψ, map_mul, hNli, h]
    field_simp
  have hTψ : ∀ x, Algebra.trace F E (ψ x) = Algebra.trace F E x := fun x => by
    have e1 := hNψ (x + 1)
    rw [hψadd, hψ1, norm_add, norm_add, hNψ x] at e1
    simpa [map_one] using e1
  have hcases : ∀ x, ψ x = x ∨ ψ x = conj F E x := fun x =>
    eq_or_eq_conj_of_norm_trace (hNψ x) (hTψ x)
  have hfin : (∀ x, ψ x = x) ∨ (∀ x, ψ x = conj F E x) := by
    by_contra hne
    push Not at hne
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hne
    have hu' : ψ u = conj F E u := (hcases u).resolve_left hu
    have hv' : ψ v = v := (hcases v).resolve_right hv
    rcases hcases (u + v) with h1 | h1
    · rw [hψadd, hu', hv'] at h1
      exact hu (hu'.trans (add_right_cancel h1))
    · rw [hψadd, hu', hv', map_add] at h1
      exact hv (hv'.trans (add_left_cancel h1))
  have key : ∀ x, φ x = l * ψ x := fun x => by simp [hψ, ← mul_assoc, mul_inv_cancel₀ hl0]
  rcases hfin with h1 | h1
  · exact Or.inl fun x => by rw [key, h1]
  · exact Or.inr fun x => by rw [key, h1]

/-- **The orthogonal group of the norm form:** an $F$-linear $\varphi$ preserving $N$ is $x \mapsto ux$ or
$x \mapsto u\,\sigma(x)$, with $u = \varphi(1)$, $N(u) = 1$. -/
@[kb "omeara1963" "§57 [unverified]"]
theorem linear_isometry (φ : E →ₗ[F] E) (h : ∀ x, Algebra.norm F (φ x) = Algebra.norm F x) :
    Algebra.norm F (φ 1) = 1 ∧ ((∀ x, φ x = φ 1 * x) ∨ (∀ x, φ x = φ 1 * conj F E x)) :=
  ⟨by rw [h, map_one], linear_similitude φ one_ne_zero fun x => by rw [h, one_mul]⟩

/-- Multiplication by $\lambda \ne 0$ as an $F$-linear automorphism of $E$. -/
def mulEquiv (l : E) (hl : l ≠ 0) : E ≃ₗ[F] E where
  toFun x := l * x
  invFun x := l⁻¹ * x
  map_add' x y := mul_add l x y
  map_smul' c x := by simp [Algebra.smul_def]; ring
  left_inv x := by simp [← mul_assoc, inv_mul_cancel₀ hl]
  right_inv x := by simp [← mul_assoc, mul_inv_cancel₀ hl]

@[simp]
theorem mulEquiv_apply (l : E) (hl : l ≠ 0) (x : E) : mulEquiv (F := F) l hl x = l * x := rfl

/-- $x \mapsto \lambda x$ and $x \mapsto \lambda\sigma(x)$ as similitudes: an isometry
$(E, c\,N) \cong (E, c'\,N)$ when $c'\,N(\lambda) = c$. -/
def simIso {c c' : F} (l : E) (hl : l ≠ 0) (hc : c' * Algebra.norm F l = c) (b : Bool) :
    (c • normForm F E).IsometryEquiv (c' • normForm F E) where
  toLinearEquiv := if b then (conj F E).toLinearEquiv.trans (mulEquiv l hl) else mulEquiv l hl
  map_app' x := by
    have e : ∀ y, (c' • normForm F E) y = c' * Algebra.norm F y := fun y => rfl
    have e' : ∀ y, (c • normForm F E) y = c * Algebra.norm F y := fun y => rfl
    cases b
    · change (c' • normForm F E) (l * x) = _
      rw [e, e', map_mul, ← hc]; ring
    · change (c' • normForm F E) (l * conj F E x) = _
      rw [e, e', map_mul, norm_conj, ← hc]; ring

theorem simIso_apply {c c' : F} (l : E) (hl : l ≠ 0) (hc : c' * Algebra.norm F l = c) (b : Bool) (x : E) :
    simIso l hl hc b x = l * (if b then conj F E x else x) := by
  cases b <;> rfl

end Similitude

/-! ### Lattices in $(E, cN)$ -/

section Lattice

variable {F E : Type*} [Field F] [NumberField F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- The lattice $\lambda L = \{\lambda x : x \in L\}$ for an $\mathcal O_F$-submodule $L \subseteq E$. -/
def smulLat (l : E) (L : Submodule (𝓞 F) E) : Submodule (𝓞 F) E := L.map (LinearMap.mulLeft (𝓞 F) l)

theorem mem_smulLat {l : E} {L : Submodule (𝓞 F) E} {x : E} : x ∈ smulLat l L ↔ ∃ y ∈ L, l * y = x := by
  simp [smulLat]

/-- The conjugate lattice $\sigma(L)$. -/
def conjLat (L : Submodule (𝓞 F) E) : Submodule (𝓞 F) E :=
  L.map ((conj F E).toLinearMap.restrictScalars (𝓞 F))

theorem mem_conjLat {L : Submodule (𝓞 F) E} {x : E} : x ∈ conjLat L ↔ ∃ y ∈ L, conj F E y = x := by
  simp [conjLat]

theorem map_simIso {c c' : F} (l : E) (hl : l ≠ 0) (hc : c' * Algebra.norm F l = c) (b : Bool)
    (L : Submodule (𝓞 F) E) :
    L.map (Lattices.IsometryEquiv.toOLinear (simIso l hl hc b)) =
      smulLat l (if b then conjLat L else L) := by
  ext x
  cases b
  · simp [smulLat, simIso_apply]
  · simp only [Lattices.IsometryEquiv.toOLinear, Submodule.mem_map, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, smulLat, conjLat, ite_true]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨conj F E y, ⟨y, hy, rfl⟩, ?_⟩
      simp [simIso_apply]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [simIso_apply]⟩

/-- **Isometry of lattices in $(E, cN)$.** For $c, c' \in F^\times$ and $\mathcal O_F$-submodules $L, L' \subseteq E$:
$(L, c\,N) \cong (L', c'\,N)$ iff $L' = \lambda L$ or $L' = \lambda\,\sigma(L)$ for some $\lambda \in E^\times$ with
$c'\,N(\lambda) = c$. -/
@[kb "omeara1963" "§82, cls L; §57 [unverified]"]
theorem isometricLattices_iff {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) (L L' : Submodule (𝓞 F) E) :
    Lattices.IsometricLattices (c • normForm F E) (c' • normForm F E) L L' ↔
      ∃ l : E, l ≠ 0 ∧ c' * Algebra.norm F l = c ∧ (L' = smulLat l L ∨ L' = smulLat l (conjLat L)) := by
  constructor
  · rintro ⟨τ, hτ⟩
    have hN : ∀ x, Algebra.norm F (τ x) = (c / c') * Algebra.norm F x := fun x => by
      have := τ.map_app x
      simp only [smul_apply, normForm_apply, smul_eq_mul] at this
      field_simp
      linear_combination this
    have ha : c / c' ≠ 0 := div_ne_zero hc hc'
    set l := τ 1
    have hNl : Algebra.norm F l = c / c' := by rw [hN, map_one, mul_one]
    have hl0 : l ≠ 0 := by
      intro h0; rw [h0, Algebra.norm_eq_zero_iff.mpr rfl] at hNl; exact ha hNl.symm
    have hcl : c' * Algebra.norm F l = c := by rw [hNl]; field_simp
    refine ⟨l, hl0, hcl, ?_⟩
    have hmap : ∀ b : Bool, (∀ x, τ x = simIso l hl0 hcl b x) →
        L' = smulLat l (if b then conjLat L else L) := by
      intro b hb
      rw [← hτ, ← map_simIso l hl0 hcl b L]
      congr 1
      ext x
      exact hb x
    rcases linear_similitude τ.toLinearEquiv.toLinearMap ha hN with h | h
    · exact Or.inl (hmap false fun x => by rw [simIso_apply]; exact h x)
    · exact Or.inr (hmap true fun x => by rw [simIso_apply]; exact h x)
  · rintro ⟨l, hl, hcl, h | h⟩
    · exact ⟨simIso l hl hcl false, by rw [map_simIso, h]; rfl⟩
    · exact ⟨simIso l hl hcl true, by rw [map_simIso, h]; rfl⟩

end Lattice

end QuadFormsKB.Binary.Rel
