/-
# Eichler's theorem: for indefinite forms in $n \ge 3$ variables, spinor genus = class

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`Lattices/SpinorGenus.lean`).

**Proves**, conditional on the named input `StrongApproximationSpin F` (strong approximation for rotations,
`Lattices/StrongApproximation.lean`):
* `eichler_spinorGenus_eq_class`: if $Q$ is nondegenerate and indefinite and $n \ge 3$, every lattice in the spinor
  genus of $L$ is isometric to $L$ (Eichler 1952; O'Meara 1963, 104:5 [unverified]; Cassels 1978, Ch. 11 Thm 1.4
  [unverified]);
* `latSpinorGenus_eq_class`: $\mathrm{spn}(L) = \mathrm{cls}(L)$ as sets;
* `classesEquivSpinorGenera`: the classes in $\mathrm{gen}(L)$ are in bijection with the spinor genera in
  $\mathrm{gen}(L)$ (the class number of the genus equals its number of spinor genera).

*Proof.* If $M = \sigma\Sigma L$ with $\sigma \in O(V)$ and $\Sigma \in O'(V_{\mathbb A_f})$, strong approximation gives
$\gamma \in O'(V)$ with $\gamma^{-1}\Sigma \in O(\hat L)$, so $\Sigma L = \gamma L$ and $M = (\sigma\gamma)L$.
-/
import QuadFormsKB.Lattices.SpinorGenus
import QuadFormsKB.Lattices.StrongApproximation

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Eichler's theorem** (Eichler 1952; O'Meara 1963, 104:5 [unverified]; Cassels 1978, Ch. 11, Thm 1.4
[unverified]): for a nondegenerate indefinite form $Q$ over $F$ in $n \ge 3$ variables, two lattices in the same
spinor genus are isometric. **Conditional** on the named input `StrongApproximationSpin F`. -/
@[kb "omeara1963" "104:5 [unverified]"]
theorem eichler_spinorGenus_eq_class (hSA : StrongApproximationSpin F) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    (hind : IsIndefinite Q) {L M : Lat F n} (h : SameSpinorGenus Q L M) : IsIsometric Q L.1 M.1 := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨σ, k, hk, rfl⟩ := (mem_latSpinorGenus Q).mp h
  obtain ⟨γ, -, hγ⟩ := hSA.approx Q hn hQ hind L k hk
  have hkL : latSMul Q k L = latSMul Q (diagF Q γ) L := by
    have hs : ((diagF Q γ)⁻¹ * k) • L = L :=
      MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ hγ)
    calc latSMul Q k L = (diagF Q γ * ((diagF Q γ)⁻¹ * k)) • L := by rw [mul_inv_cancel_left]; rfl
      _ = latSMul Q (diagF Q γ) L := by rw [mul_smul, hs]; rfl
  refine ⟨((σ * γ : orthGroup Q F) : GL (Fin n) F), (σ * γ).2, ?_⟩
  rw [hkL, diagF_smul, diagF_smul, Lat.image, Lat.image, Subgroup.coe_mul, glImage_mul]

/-- **$\mathrm{spn}(L) = \mathrm{cls}(L)$** for nondegenerate indefinite $Q$ in $n \ge 3$ variables (conditional on
`StrongApproximationSpin F`). -/
@[kb "omeara1963" "104:5 [unverified]"]
theorem latSpinorGenus_eq_class (hSA : StrongApproximationSpin F) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    (hind : IsIndefinite Q) (L : Lat F n) :
    latSpinorGenus Q L = {M : Lat F n | IsIsometric Q L.1 M.1} :=
  Set.Subset.antisymm (fun _ h => eichler_spinorGenus_eq_class Q hSA hn hQ hind h)
    (class_subset_latSpinorGenus Q L)

/-- **Classes in the genus = spinor genera in the genus** for nondegenerate indefinite $Q$, $n \ge 3$ (conditional
on `StrongApproximationSpin F`): the class relation and the spinor-genus relation agree on $\mathrm{gen}(L)$, so the
identity of the genus induces a bijection between the two quotients. -/
@[kb "omeara1963" "104:5 [unverified]"]
def classesEquivSpinorGenera (hSA : StrongApproximationSpin F) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    (hind : IsIndefinite Q) (L : Lat F n) :
    @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (ratPoints Q) L ≃
      @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (spnGroup Q) L :=
  Quotient.congr (Equiv.refl _) fun M M' => by
    rw [classRel_iff, spinorRel_iff]
    exact ⟨fun h => IsIsometric.sameSpinorGenus Q h, fun h => eichler_spinorGenus_eq_class Q hSA hn hQ hind h⟩

end QuadFormsKB.Lattices
