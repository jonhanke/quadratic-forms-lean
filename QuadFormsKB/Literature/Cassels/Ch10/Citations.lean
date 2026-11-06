/-
# Cassels, Chapter 10: citations for declarations elsewhere in the library

Declarations outside the `Ch10/` files that state (variants of) items of Cassels' Chapter 10 but carried no tag with
the item's locator. The tags are added here with `attribute [kb …]`, so the files where the declarations live are
unchanged. Cassels works over $\mathbb Q$, $\mathbb Q_p$; the library's abstract spaces are over any field of
characteristic $\ne 2$ and its lattice statements are over a number field $F$ (*generalization*).

* §3 (p. 176): $M_0(V)$, $u \mapsto T_u$ (3.1) and (3.2), from `Ch10/Clifford.lean` (`Cassels.M0`, `Cassels.conjHom`,
  `Cassels.vecUnit_conj`).
* Theorem 3.2 (p. 179): $\Omega \subseteq \Theta$, and $\Omega = \Theta$ for isotropic $V$ — O'Meara's 55:6a in
  the abstract setting (`OMeara.omega_le_orthPrime`, `OMeara.omega_eq_orthPrime_of_isotropic`).
* §3 (pp. 178–179): $\Omega(V)$, $\Theta$ and the spinor norm $\theta$ (`OMeara.omega`, `OMeara.orthPrime`,
  `OMeara.spinorNormHom`).
* §4, (4.1) (p. 182): $O(\Lambda)$ for a lattice (`Lattices.autLat`).
* §6 (p. 185): the natural map $O(V) \to O(V_K)$ (`Lattices.orthMap`).
* §7 (p. 186): $O(\Lambda_p)$ is open in $O(V_p)$ (`Tamagawa.Measure.isOpen_stdStab`, `Tamagawa.Measure.isOpen_stabLat`).
* Proof of Theorem 7.1 (pp. 188–189): the case $n = 3$ through the quaternary norm form of $C_0(V)$
  (`Lattices.rotApprox_ternary`, `Lattices.rotApprox_ternary_isotropic`) and the case $n \ge 4$ through products of
  symmetries approximated with Lemma 7.1 (`Lattices.pair_approx`, `Lattices.list_approx`,
  `Lattices.exists_correction`); these follow O'Meara 104:4 and prove the version for $\Theta$ (O'Meara's $O'$).
-/
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Lattices.SATernary
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Literature.Cassels.Ch10.Clifford

namespace QuadFormsKB

-- Ch. 10, §3, p. 176: M₀(V), the map u ↦ T_u (3.1), and (3.2)
attribute [kb "cassels1978" "Ch. 10, §3, p. 176 (M₀(V))"] Cassels.M0
attribute [kb "cassels1978" "Ch. 10, §3, (3.1), p. 176 (T_u x = u x u⁻¹; on the Clifford group)"] Cassels.conjHom
attribute [kb "cassels1978" "Ch. 10, §3, (3.2), p. 176 (y x y⁻¹ = −τ_y x)"] Cassels.vecUnit_conj

-- Ch. 10, Theorem 3.2: Ω ⊆ Θ, and Ω = Θ for isotropic V
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, p. 179 (Ω ⊆ Θ)"] OMeara.omega_le_orthPrime
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, pp. 179–181 (Ω = Θ whenever V is isotropic)"]
  OMeara.omega_eq_orthPrime_of_isotropic

-- Ch. 10, §3: Ω(V), Θ and the spinor norm
attribute [kb "cassels1978" "Ch. 10, §3, p. 179 (Ω, the commutator subgroup of O(V))"] OMeara.omega
attribute [kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 3, (3.7 bis), p. 178 (Θ, the kernel of the spinor norm)"]
  OMeara.orthPrime
attribute [kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 3, (3.7), p. 178 (the spinor norm θ : O⁺ → k^×/(k^×)², a homomorphism)"]
  OMeara.spinorNormHom

-- Ch. 10, §4, (4.1): O(Λ); §6: change of field
attribute [kb "cassels1978" "Ch. 10, §4, (4.1), p. 182 (O(Λ); generalization: number field)"] Lattices.autLat
attribute [kb "cassels1978" "Ch. 10, §6, p. 185 (the natural homomorphism O(V) → O(V_K))"] Lattices.orthMap

-- Ch. 10, §7, p. 186: O(Λ_p) is open in O(V_p)
attribute [kb "cassels1978" "Ch. 10, §7, p. 186 (O(Λ_p) is an open subgroup of O(V_p); generalization: number field)"]
  Tamagawa.Measure.isOpen_stdStab Tamagawa.Measure.isOpen_stabLat

-- Ch. 10, §7, proof of Theorem 7.1: n = 3 through the quaternary form uu', n ≥ 4 through products of symmetries
attribute [kb "cassels1978" "Ch. 10, §7, proof of Thm. 7.1, p. 188 (n = 3, via the quaternary form uu'; for Θ, number field)"]
  Lattices.rotApprox_ternary Lattices.rotApprox_ternary_isotropic
attribute [kb "cassels1978" "Ch. 10, §7, proof of Thm. 7.1, p. 189 (n ≥ 4, products of symmetries; for Θ, number field)"]
  Lattices.pair_approx Lattices.list_approx Lattices.exists_correction

end QuadFormsKB
