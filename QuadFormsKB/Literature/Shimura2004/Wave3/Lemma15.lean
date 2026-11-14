/-
# Shimura 2004, Lemma 1.5 (ii): $SO^\varphi(V)$ is transitive on the nonzero vectors of a given value

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, Lemma 1.5 (ii)
(printed p. 11), and the remark in the Introduction (printed p. 1) that for $n > 2$ and $q \ne 0$ the vectors $h$
with $\varphi[h] = q$ form a single $SO^\varphi$-orbit. Page numbers are printed pages.

**Setting and dictionary.** $F$ a field of characteristic $\ne 2$ (`[Invertible (2 : F)]`), $V$ a
finite-dimensional $F$-vector space of dimension $n$ = `finrank F V`, and `Q : QuadraticForm F V` with
$\varphi[x] = Q(x)$ and $\varphi(x, y)$ = `QuadraticMap.associated Q x y` (so $\varphi(x, x) = \varphi[x]$),
nondegenerate (`hQ`). $O^\varphi(V)$ is O'Meara's `OMeara.orth Q` and $SO^\varphi(V)$ is `OMeara.orthPlus Q`
(isometries of determinant $1$). *Convention:* Shimura lets $O^\varphi$ act on the right ($h \mapsto h\gamma$); here
isometries are linear maps applied on the left, so "$h\gamma = k$" reads `γ h = k`.

**Proves** (all unconditional; standard axioms only)
* `exists_anisotropic_orthogonal`: if $h \ne 0$ and either $\varphi[h] \ne 0$, $n > 1$, or $\varphi[h] = 0$,
  $n > 2$, then there is $u$ with $\varphi[u] \ne 0$ and $\varphi(h, u) = 0$ (the hyperplane $h^\perp$ is not
  totally isotropic).
* `lemma_1_5_ii_anisotropic`: Lemma 1.5 (ii), case $\varphi[h] \ne 0$, $n > 1$: if $\varphi[h] = \varphi[k] \ne 0$
  there is $\gamma \in SO^\varphi(V)$ with $\gamma h = k$.
* `lemma_1_5_ii_isotropic`: Lemma 1.5 (ii), case $\varphi[h] = 0$, $n > 2$: if $h, k \ne 0$ and
  $\varphi[h] = \varphi[k] = 0$ there is $\gamma \in SO^\varphi(V)$ with $\gamma h = k$.
* `lemma_1_5_ii_orth`: the first assertion of Lemma 1.5 (ii) (in $O^\varphi(V)$, any $n$), from Witt's theorem.

**Proof.** Witt's theorem (`QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`,
`QuadraticForm.exists_isometryEquiv_apply_eq_of_isotropic`) gives $\sigma \in O^\varphi(V)$ with $\sigma h = k$.
If $\det\sigma = -1$, replace $\sigma$ by $\sigma\tau_u$, where $\tau_u$ is the symmetry (`OMeara.symmetry`,
determinant $-1$) of an anisotropic $u \perp h$; $\tau_u$ fixes $h$. Such $u$ exists: if $\varphi$ vanished on
$W = h^\perp$, then $W \subseteq W^\perp = Fh$, which is impossible for $\dim W = n - 1$ under either hypothesis.
-/
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Citation

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

/-- Nondegeneracy of $\varphi(x,y)$ = `associated Q` gives nondegeneracy of the polar form $2\varphi(x,y)$. -/
theorem polarBilin_nondegenerate_of_associated (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (QuadraticMap.polarBilin Q).Nondegenerate := by
  have key : ∀ x y : V, QuadraticMap.polarBilin Q x y = 2 * QuadraticMap.associated Q x y := by
    intro x y
    rw [← QuadraticMap.two_nsmul_associated F, two_mul, LinearMap.smul_apply, LinearMap.smul_apply,
      two_nsmul]
  have two : (2 : F) ≠ 0 := Invertible.ne_zero 2
  refine ⟨fun x hx => hQ.1 x fun y => ?_, fun y hy => hQ.2 y fun x => ?_⟩
  · have := hx y; rw [key] at this; exact (mul_eq_zero.1 this).resolve_left two
  · have := hy x; rw [key] at this; exact (mul_eq_zero.1 this).resolve_left two

/-- **The hyperplane $h^\perp$ is not totally isotropic** (used in Shimura, Lemma 1.5 (ii), p. 11): if
$\varphi$ is nondegenerate, $h \ne 0$, and either $\varphi[h] \ne 0$ and $n > 1$, or $n > 2$, then some
$u$ has $\varphi[u] \ne 0$ and $\varphi(h, u) = 0$. -/
theorem exists_anisotropic_orthogonal (hQ : (QuadraticMap.associated Q).Nondegenerate) {h : V} (h0 : h ≠ 0)
    (hdim : (Q h ≠ 0 ∧ 1 < finrank F V) ∨ 2 < finrank F V) :
    ∃ u : V, Q u ≠ 0 ∧ QuadraticMap.associated Q h u = 0 := by
  set B := QuadraticMap.associated (R := F) Q
  have hrefl : B.IsRefl := fun x y hxy => by
    have := bil_comm Q x y; simp only [bil] at this; rw [← this]; exact hxy
  set W := LinearMap.BilinForm.orthogonal B (F ∙ h)
  by_contra hcon
  push Not at hcon
  -- $\varphi$ vanishes on $W$
  have hQW : ∀ w ∈ W, Q w = 0 := by
    intro w hw
    by_contra hw0
    exact hcon w hw0 ((LinearMap.BilinForm.mem_orthogonal_iff).1 hw h (Submodule.mem_span_singleton_self h))
  -- hence $W \subseteq W^\perp$
  have hWW : W ≤ LinearMap.BilinForm.orthogonal B W := by
    intro w hw v hv
    have h1 := hQW v hv
    have h2 := hQW w hw
    have h3 := hQW (v + w) (W.add_mem hv hw)
    have : B v w = 0 := by
      have e := QuadraticMap.associated_apply (S := F) (Q := Q) v w
      rw [show B v w = _ from e, h1, h2, h3]; simp
    exact this
  have hWperp : LinearMap.BilinForm.orthogonal B W = F ∙ h := LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl _
  rw [hWperp] at hWW
  have hfr : finrank F W = finrank F V - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton h0]
  rcases hdim with ⟨hh, hn⟩ | hn
  · -- $W \cap Fh = 0$, so $W = 0$
    have hbot : W = ⊥ := by
      have hd := LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot (B := B)
        (x := h) (by rw [QuadraticMap.associated_eq_self_apply]; exact hh)
      rw [← hd]
      exact le_antisymm (le_inf hWW le_rfl) inf_le_right
    rw [hbot, finrank_bot] at hfr
    omega
  · have := Submodule.finrank_mono hWW
    rw [finrank_span_singleton h0] at this
    omega

/-- The symmetry $\tau_u$ fixes every vector orthogonal to $u$. -/
theorem symmetry_apply_of_orthogonal {u x : V} (hu : Q u ≠ 0) (hxu : QuadraticMap.associated Q x u = 0) :
    symmetry Q u hu x = x := by
  rw [symmetry_apply]
  simp [bil, hxu]

/-- Correction of the determinant: if some $\sigma \in O^\varphi(V)$ has $\sigma h = k$ and $h$ is orthogonal to
an anisotropic vector $u$, then some $\gamma \in SO^\varphi(V)$ has $\gamma h = k$ ($\gamma = \sigma$ or
$\sigma\tau_u$). -/
theorem exists_orthPlus_of_orth (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) {h k : V} (hσk : σ h = k)
    {u : V} (hu : Q u ≠ 0) (hhu : QuadraticMap.associated Q h u = 0) :
    ∃ γ ∈ orthPlus Q, γ h = k := by
  rcases det_orth_eq Q hQ hσ with hd | hd
  · exact ⟨σ, ⟨hσ, hd⟩, hσk⟩
  · refine ⟨σ * symmetry Q u hu, ⟨(orth Q).mul_mem hσ (symmetry_mem_orth Q hu), ?_⟩, ?_⟩
    · show LinearEquiv.det (σ * symmetry Q u hu) = 1
      rw [map_mul, hd, det_symmetry]; simp
    · show σ (symmetry Q u hu h) = k
      rw [symmetry_apply_of_orthogonal hu hhu, hσk]

/-- **Lemma 1.5 (ii)**, first assertion (Shimura, p. 11): if $h, k \ne 0$ and $\varphi[h] = \varphi[k]$, there
is $\gamma \in O^\varphi(V)$ with $\gamma h = k$ (Witt's theorem). -/
@[kb "shimura2004" "Lemma 1.5 (ii), p. 11 (transitivity of O^φ)"]
theorem lemma_1_5_ii_orth (hQ : (QuadraticMap.associated Q).Nondegenerate) {h k : V} (h0 : h ≠ 0)
    (k0 : k ≠ 0) (hk : Q h = Q k) : ∃ γ ∈ orth Q, γ h = k := by
  have hP := polarBilin_nondegenerate_of_associated hQ
  by_cases hh : Q h = 0
  · obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_isotropic Q
      (QuadraticForm.radical_eq_bot_of_nondegenerate Q hP) h0 k0 hh (hk ▸ hh)
    exact ⟨ρ.toLinearEquiv, fun x => ρ.map_app x, hρ⟩
  · obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate Q hP hh rfl hk.symm
    exact ⟨ρ.toLinearEquiv, fun x => ρ.map_app x, hρ⟩

/-- **Lemma 1.5 (ii)**, anisotropic case (Shimura, p. 11; also the remark of the Introduction, p. 1): if
$\dim V > 1$ and $\varphi[h] = \varphi[k] \ne 0$, there is $\gamma \in SO^\varphi(V)$ with $\gamma h = k$. -/
@[kb "shimura2004" "Lemma 1.5 (ii), p. 11 (SO^φ, case φ[h] ≠ 0, dim V > 1)"]
theorem lemma_1_5_ii_anisotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 1 < finrank F V)
    {h k : V} (hh : Q h ≠ 0) (hk : Q h = Q k) : ∃ γ ∈ orthPlus Q, γ h = k := by
  have h0 : h ≠ 0 := fun e => hh (by simp [e])
  have k0 : k ≠ 0 := fun e => hh (by simp [hk, e])
  obtain ⟨σ, hσ, hσk⟩ := lemma_1_5_ii_orth hQ h0 k0 hk
  obtain ⟨u, hu, hhu⟩ := exists_anisotropic_orthogonal hQ h0 (Or.inl ⟨hh, hn⟩)
  exact exists_orthPlus_of_orth hQ hσ hσk hu hhu

/-- **Lemma 1.5 (ii)**, isotropic case (Shimura, p. 11): if $\dim V > 2$, $h, k \ne 0$ and
$\varphi[h] = \varphi[k] = 0$, there is $\gamma \in SO^\varphi(V)$ with $\gamma h = k$. -/
@[kb "shimura2004" "Lemma 1.5 (ii), p. 11 (SO^φ, case φ[h] = 0, dim V > 2)"]
theorem lemma_1_5_ii_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 2 < finrank F V)
    {h k : V} (h0 : h ≠ 0) (k0 : k ≠ 0) (hh : Q h = 0) (hk : Q k = 0) : ∃ γ ∈ orthPlus Q, γ h = k := by
  obtain ⟨σ, hσ, hσk⟩ := lemma_1_5_ii_orth hQ h0 k0 (hh.trans hk.symm)
  obtain ⟨u, hu, hhu⟩ := exists_anisotropic_orthogonal hQ h0 (Or.inr hn)
  exact exists_orthPlus_of_orth hQ hσ hσk hu hhu

/-- **The remark of the Introduction** (Shimura, p. 1): for $n > 2$ and $q \ne 0$ the vectors $h$ with
$\varphi[h] = q$ form a single orbit under $SO^\varphi(V)$ (empty or not). -/
@[kb "shimura2004" "Introduction, p. 1 (single SO^φ-orbit on φ[h] = q ≠ 0, n > 2)"]
theorem intro_single_orbit (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 2 < finrank F V)
    {q : F} (hq : q ≠ 0) {h k : V} (hh : Q h = q) (hk : Q k = q) : ∃ γ ∈ orthPlus Q, γ h = k :=
  lemma_1_5_ii_anisotropic hQ (by omega) (hh ▸ hq) (hh.trans hk.symm)

end QuadFormsKB.Shimura2004
