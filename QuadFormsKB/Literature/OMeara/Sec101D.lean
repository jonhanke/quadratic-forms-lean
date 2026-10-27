/-
# O'Meara §101D: the idèle group $J_F^L$

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n`, a lattice $L$ = `L : Lat F n`, its
localizations $L_\mathfrak p$ and local stabilizers $O(L_\mathfrak p)$ = `locStabV Q 𝔭 L` (`Lattices/SpinorLocal.lean`),
the rotations `Tamagawa.soSub`, the spinor norm `spinorNormHom`, and the finite idèles
$(\mathbb A_F^{\mathrm{fin}})^\times$ = `(FiniteAdeleRing (𝓞 F) F)ˣ` with components `Tamagawa.Measure.Weil.unitAt`.

**Defines** (O'Meara 1973, §101D, p. 297; item 101.d1)
* `localSpinorNormGroup Q hQ 𝔭 L` $= \theta(O^+(L_\mathfrak p)) \subseteq F_\mathfrak p^\times$, the elements whose square
  class is the spinor norm of a rotation of $V_\mathfrak p$ carrying $L_\mathfrak p$ onto itself;
* `spinorIdeleGroup Q hQ L` $= J_F^L = \{i \in J_F : i_\mathfrak p \in \theta(O^+(L_\mathfrak p))$ for all
  $\mathfrak p \in S\}$, with $S$ the set of all finite spots (so $J_F$ is here the group of finite idèles).
-/
import QuadFormsKB.Literature.OMeara.Sec101B
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleChart

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **The local spinor norm group** $\theta(O^+(L_\mathfrak p)) \subseteq F_\mathfrak p^\times$ (O'Meara 1973, §101D,
p. 297, and §92): the $\alpha \in F_\mathfrak p^\times$ with $\alpha F_\mathfrak p^{\times 2} = \theta(\sigma)$ for some
rotation $\sigma \in O^+(L_\mathfrak p)$. -/
@[kb "omeara1963" "§101D, p. 297 (θ(O⁺(L_𝔭)), the local condition of J_F^L)"]
def localSpinorNormGroup (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n) :
    Subgroup (v.adicCompletion F)ˣ :=
  ((locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F)).map
    (spinorNormHom Q (v.adicCompletion F) hQ)).comap (sqClassHom (v.adicCompletion F))

theorem mem_localSpinorNormGroup (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n)
    {a : (v.adicCompletion F)ˣ} :
    a ∈ localSpinorNormGroup Q hQ v L ↔
      ∃ σ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F),
        spinorNorm Q (v.adicCompletion F) σ = SqClass.mk a := by
  simp [localSpinorNormGroup, sqClassHom_apply, spinorNormHom_apply]

/-- **The idèle group $J_F^L$** (O'Meara 1973, §101D, p. 297; item 101.d1): the finite idèles $i$ with
$i_\mathfrak p \in \theta(O^+(L_\mathfrak p))$ for every finite spot $\mathfrak p$. -/
@[kb "omeara1963" "§101D, p. 297 (the idèle group J_F^L)"]
def spinorIdeleGroup (hQ : Q.Nondegenerate) (L : Lat F n) : Subgroup (FiniteAdeleRing (𝓞 F) F)ˣ where
  carrier := {i | ∀ v, Tamagawa.Measure.Weil.unitAt i v ∈ localSpinorNormGroup Q hQ v L}
  mul_mem' {a b} ha hb v := by
    rw [Tamagawa.Measure.Weil.unitAt_mul]
    exact (localSpinorNormGroup Q hQ v L).mul_mem (ha v) (hb v)
  one_mem' v := by
    rw [Tamagawa.Measure.Weil.unitAt_one]
    exact (localSpinorNormGroup Q hQ v L).one_mem
  inv_mem' {a} ha v := by
    have : Tamagawa.Measure.Weil.unitAt a⁻¹ v = (Tamagawa.Measure.Weil.unitAt a v)⁻¹ := Units.ext rfl
    rw [this]
    exact (localSpinorNormGroup Q hQ v L).inv_mem (ha v)

end QuadFormsKB.Lattices
