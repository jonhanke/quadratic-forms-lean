/-
# Extending a homomorphism from a generic subset

**Layer:** pure group theory.

**Setting.** $G$, $H$ groups, $\Omega \subseteq G$ a subset, $\rho : G \to H$ a map (its values off $\Omega$ are irrelevant).

**Result** (`exists_monoidHom_of_generic`). Suppose
* (multiplicativity on $\Omega$) $\rho(xy) = \rho(x)\rho(y)$ whenever $x$, $y$ and $xy$ all lie in $\Omega$, and
* (genericity) for every finite list $h_0, \dots, h_{r-1}$ of elements of $G$ there is $z \in \Omega$ with
  $h_iz \in \Omega$ for all $i$.
Then there is a group homomorphism $\varphi : G \to H$ with $\varphi = \rho$ on $\Omega$.

*Proof.* Put $\varphi(g) = \rho(gz)\rho(z)^{-1}$ for any $z \in \Omega$ with $gz \in \Omega$. This does not depend on $z$:
for two choices $z, z'$ take $y \in \Omega$ with $z^{-1}y, z'^{-1}y, gy \in \Omega$; with $v = z^{-1}y$,
$\rho(gz)\rho(v) = \rho(gy)$ and $\rho(z)\rho(v) = \rho(y)$, so $\rho(gz)\rho(z)^{-1} = \rho(gy)\rho(y)^{-1}$, and the same
for $z'$. For $g, h$ take $z \in \Omega$ with $hz, ghz \in \Omega$; then $\varphi(g) = \rho(ghz)\rho(hz)^{-1}$ (choice $hz$)
and $\varphi(h) = \rho(hz)\rho(z)^{-1}$, so $\varphi(g)\varphi(h) = \varphi(gh)$.

This is the device that turns the big-cell formula for the Weil representation into a representation of
$\mathrm{Sp}_{2g}(k)$ (`Weil/Genus/SiegelPres.lean`).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.WeilRep.Genus

variable {G H : Type*} [Group G] [Group H]

/-- Independence of the choice in $\rho(gz)\rho(z)^{-1}$. -/
lemma generic_indep {Ω : Set G} {ρ : G → H}
    (hmul : ∀ x y, x ∈ Ω → y ∈ Ω → x * y ∈ Ω → ρ (x * y) = ρ x * ρ y)
    (hgen : ∀ L : List G, ∃ z ∈ Ω, ∀ h ∈ L, h * z ∈ Ω) {g z z' : G}
    (hz : z ∈ Ω) (hgz : g * z ∈ Ω) (hz' : z' ∈ Ω) (hgz' : g * z' ∈ Ω) :
    ρ (g * z) * (ρ z)⁻¹ = ρ (g * z') * (ρ z')⁻¹ := by
  obtain ⟨y, hy, hL⟩ := hgen [z⁻¹, z'⁻¹, g]
  have h1 : z⁻¹ * y ∈ Ω := hL _ (by simp)
  have h2 : z'⁻¹ * y ∈ Ω := hL _ (by simp)
  have h3 : g * y ∈ Ω := hL _ (by simp)
  have key : ∀ u, u ∈ Ω → g * u ∈ Ω → u⁻¹ * y ∈ Ω →
      ρ (g * u) * (ρ u)⁻¹ = ρ (g * y) * (ρ y)⁻¹ := by
    intro u hu hgu hv
    have e1 : ρ (u * (u⁻¹ * y)) = ρ u * ρ (u⁻¹ * y) := hmul _ _ hu hv (by simpa using hy)
    have e2 : ρ (g * u * (u⁻¹ * y)) = ρ (g * u) * ρ (u⁻¹ * y) :=
      hmul _ _ hgu hv (by simpa [mul_assoc] using h3)
    simp only [mul_inv_cancel_left, mul_assoc] at e1 e2
    rw [e1, e2]
    group
  rw [key z hz hgz h1, key z' hz' hgz' h2]

/-- **Extension from a generic subset.** If $\rho : G \to H$ is multiplicative on $\Omega$ (`hmul`: $\rho(xy) = \rho(x)\rho(y)$
whenever $x, y, xy \in \Omega$) and $\Omega$ is generic (`hgen`: for every finite list $L$ of elements of $G$ there is
$z \in \Omega$ with $hz \in \Omega$ for all $h \in L$), then some homomorphism $\varphi : G \to H$ agrees with $\rho$ on
$\Omega$. -/
@[kb "weil1964" "§§1–2 (operators defined on a dense subset of $\\mathrm{Sp}$ and extended) [unverified]"]
theorem exists_monoidHom_of_generic (Ω : Set G) (ρ : G → H)
    (hmul : ∀ x y, x ∈ Ω → y ∈ Ω → x * y ∈ Ω → ρ (x * y) = ρ x * ρ y)
    (hgen : ∀ L : List G, ∃ z ∈ Ω, ∀ h ∈ L, h * z ∈ Ω) :
    ∃ φ : G →* H, ∀ x ∈ Ω, φ x = ρ x := by
  have hz : ∀ g : G, ∃ z, z ∈ Ω ∧ g * z ∈ Ω := fun g => by
    obtain ⟨z, hz, hL⟩ := hgen [g]
    exact ⟨z, hz, hL _ (by simp)⟩
  choose zf hzf hgzf using hz
  let φ : G → H := fun g => ρ (g * zf g) * (ρ (zf g))⁻¹
  have hφ : ∀ g z, z ∈ Ω → g * z ∈ Ω → φ g = ρ (g * z) * (ρ z)⁻¹ := fun g z h1 h2 =>
    generic_indep hmul hgen (hzf g) (hgzf g) h1 h2
  refine ⟨MonoidHom.mk' φ fun g h => ?_, fun x hx => ?_⟩
  · obtain ⟨z, hz, hL⟩ := hgen [h, g * h]
    have h1 : h * z ∈ Ω := hL _ (by simp)
    have h2 : g * h * z ∈ Ω := hL _ (by simp)
    rw [hφ (g * h) z hz h2, hφ h z hz h1, hφ g (h * z) h1 (by simpa [mul_assoc] using h2)]
    simp only [mul_assoc]
    group
  · obtain ⟨z, hz, hL⟩ := hgen [x]
    have h1 : x * z ∈ Ω := hL _ (by simp)
    show φ x = ρ x
    rw [hφ x z hz h1, hmul x z hx hz h1]
    group

end QuadFormsKB.WeilRep.Genus
