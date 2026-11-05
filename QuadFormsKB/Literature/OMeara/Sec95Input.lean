/-
# O'Meara 95:1 for the matrix orthogonal group: the field `index` of `Lattices.QuaternarySpinorInput`

**Setting.** $F$ is a number field, $Q$ a quaternary form over $F$ in the library's matrix model (`QuadForm F 4`,
`Lattices.orthGroup Q K` the matrices $g$ with $g^{\mathsf T}Hg = H$, `Lattices.spinorKernel Q K` the products of an
even number of symmetries with square product of values), and $K = F_\mathfrak p$ (`v.adicCompletion F`).

**Proves** `quaternarySpinor_index`: the statement of the field `index` of the named input
`Lattices.QuaternarySpinorInput` (`Lattices/StrongApproximationProof.lean`): two elements of
$O'(V_\mathfrak p) \setminus \Omega(V_\mathfrak p)$ have product in $\Omega(V_\mathfrak p)$, where
$\Omega(V_\mathfrak p)$ is the commutator subgroup of the matrix group. It follows from O'Meara's 95:1 and 95:1a
(`omega_orthPrime_local`, `omega_cosets_local`, `Sec95.lean`) through the comparison of the matrix model with the
abstract model `OMeara.orth`, `OMeara.orthPrime`, `OMeara.omega` on $K^4$.
-/
import QuadFormsKB.Literature.OMeara.Sec95
import QuadFormsKB.Lattices.StrongApproximationProof

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace QIn

open QuadFormsKB.Lattices Matrix

section Bridge

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (K : Type) [Field K] [Algebra F K]
  [CharZero K] [Invertible (2 : K)]

/-- $\mathrm{GL}_n(K) \simeq$ the linear automorphisms of $K^n$. -/
def glEquiv : GL (Fin n) K ≃* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))

theorem glEquiv_apply (g : GL (Fin n) K) (x : Fin n → K) : glEquiv K g x = g.val *ᵥ x := by
  simp [glEquiv]

theorem map_orthGroup : (orthGroup Q K).map (glEquiv K).toMonoidHom = orth (qk Q K) := by
  ext σ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩ x
    rw [glEquiv_apply, qk_apply, qk_apply]
    exact evalIn_mulVec_of_mem Q hg x
  · intro hσ
    refine ⟨(glEquiv K).symm σ, mem_orthGroup_of_evalIn Q fun z => ?_, by simp⟩
    have := hσ z
    rw [qk_apply, qk_apply] at this
    have h2 : glEquiv K ((glEquiv K).symm σ) z = σ z := by simp
    rw [glEquiv_apply] at h2
    rw [h2]; exact this

theorem two_mul_bil (x y : Fin n → K) : 2 * OMeara.bil (qk Q K) x y = qbil Q K x y := by
  have h := Cl54.polar_eq_two_mul_bil (qk Q K) x y
  rw [polar_qk] at h
  exact h.symm

theorem glEquiv_symm {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    glEquiv K (symm Q K x : GL (Fin n) K) = OMeara.symmetry (qk Q K) x (by rwa [qk_apply]) := by
  ext1 y
  rw [glEquiv_apply, symm_mulVec_bil Q K hx, OMeara.symmetry_apply, qk_apply, two_mul_bil Q K, qbil_comm]

theorem glEquiv_symmProd (xs : List (Fin n → K)) (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) :
    glEquiv K ((symmProd Q K xs : orthGroup Q K) : GL (Fin n) K) =
      Cl54.symProd (qk Q K) xs (fun u hu => by rw [qk_apply]; exact hxs u hu) := by
  induction xs with
  | nil => simp [symmProd, Cl54.symProd]
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    have hxs' : ∀ u ∈ xs, Q.evalIn K u ≠ 0 := fun u hu => hxs u (List.mem_cons_of_mem x hu)
    have e : symmProd Q K (x :: xs) = symm Q K x * symmProd Q K xs := by simp [symmProd]
    rw [e, Cl54.symProd_cons, Subgroup.coe_mul, map_mul, glEquiv_symm Q K hx, ih hxs']

theorem mem_orthPrime_of_mem_spinorKernel {g : orthGroup Q K} (hg : g ∈ spinorKernel Q K) :
    glEquiv K (g : GL (Fin n) K) ∈ OMeara.orthPrime (qk Q K) := by
  obtain ⟨xs, ⟨hxa, hxe, c, hc⟩, rfl⟩ := hg
  rw [glEquiv_symmProd Q K xs hxa]
  have hl : ∀ u ∈ xs, qk Q K u ≠ 0 := fun u hu => by rw [qk_apply]; exact hxa u hu
  have hv : (xs.map (qk Q K)).prod = valProd Q K xs := by
    unfold valProd
    exact congrArg List.prod (List.map_congr_left fun x _ => qk_apply Q K x)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : valProd Q K xs ≠ 0 := by
      refine List.prod_ne_zero ?_
      intro h0
      obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
      exact hxa x hx hx0
    exact h0 (by simpa using hc)
  refine ⟨⟨OMeara.Sp55.symProd_mem_orth _ xs hl, ?_⟩, ?_⟩
  · show _ ∈ LinearEquiv.det.ker
    rw [MonoidHom.mem_ker, OMeara.Sp55.det_symProd, hxe.neg_one_pow]
  · rw [OMeara.Sp55.hasSpinorNorm_iff]
    exact ⟨xs, hl, rfl, c, hc0, by rw [hv, hc]; ring⟩

theorem mem_commutator_iff (g : orthGroup Q K) :
    g ∈ commutator (orthGroup Q K) ↔ glEquiv K (g : GL (Fin n) K) ∈ OMeara.omega (qk Q K) := by
  have h1 : (commutator (orthGroup Q K)).map (orthGroup Q K).subtype = ⁅orthGroup Q K, orthGroup Q K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : OMeara.omega (qk Q K) = ⁅orthGroup Q K, orthGroup Q K⁆.map (glEquiv K).toMonoidHom := by
    rw [Subgroup.map_commutator, map_orthGroup]; rfl
  rw [h2, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, ← h1]
  exact (Subgroup.mem_map_iff_mem (orthGroup Q K).subtype_injective).symm

end Bridge

/-- Two elements outside a subgroup of index two have product in it (inside a supergroup). -/
theorem mul_mem_of_relIndex_two {G : Type*} [Group G] {N P : Subgroup G} (h : N.relIndex P = 2) {a b : G}
    (ha : a ∈ P) (hb : b ∈ P) (han : a ∉ N) (hbn : b ∉ N) : a * b ∈ N := by
  have key := Subgroup.mul_mem_iff_of_index_two (H := N.subgroupOf P) h (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  have : (⟨a, ha⟩ * ⟨b, hb⟩ : P) ∈ N.subgroupOf P := key.mpr (by
    simp only [Subgroup.mem_subgroupOf]; exact iff_of_false han hbn)
  exact this

end QIn

/-- **95:1 for the matrix model: the field `index` of `Lattices.QuaternarySpinorInput`** (O'Meara 1973, 95:1 and
95:1a, pp. 280–283): for a regular quaternary form $Q$ over a number field $F$ and a finite place $\mathfrak p$, two
elements of $O'(V_\mathfrak p)$ outside $\Omega(V_\mathfrak p)$ have product in $\Omega(V_\mathfrak p)$, i.e.
$(O'(V_\mathfrak p) : \Omega(V_\mathfrak p)) \le 2$. -/
@[kb "omeara1963" "§95, 95:1, pp. 280–283 ((O'₄ : Ω₄) ≤ 2, matrix model)"]
theorem quaternarySpinor_index {F : Type} [Field F] [NumberField F] (Q : QuadForm F 4) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 F)) (φ ψ : Lattices.orthGroup Q (v.adicCompletion F))
    (hφ : φ ∈ Lattices.spinorKernel Q (v.adicCompletion F)) (hψ : ψ ∈ Lattices.spinorKernel Q (v.adicCompletion F))
    (hφΩ : φ ∉ commutator (↥(Lattices.orthGroup Q (v.adicCompletion F))))
    (hψΩ : ψ ∉ commutator (↥(Lattices.orthGroup Q (v.adicCompletion F)))) :
    φ * ψ ∈ commutator (↥(Lattices.orthGroup Q (v.adicCompletion F))) := by
  let _ : Invertible (2 : v.adicCompletion F) := invertibleOfNonzero two_ne_zero
  have hnd : (QuadraticMap.associated (Lattices.qk Q (v.adicCompletion F))).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp
        (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (v.adicCompletion F) hQ))
  have ha := QIn.mem_orthPrime_of_mem_spinorKernel Q _ hφ
  have hb := QIn.mem_orthPrime_of_mem_spinorKernel Q _ hψ
  have ha' : QIn.glEquiv (v.adicCompletion F) (φ : GL (Fin 4) (v.adicCompletion F)) ∉
      omega (Lattices.qk Q (v.adicCompletion F)) := fun h => hφΩ ((QIn.mem_commutator_iff Q _ φ).mpr h)
  have hb' : QIn.glEquiv (v.adicCompletion F) (ψ : GL (Fin 4) (v.adicCompletion F)) ∉
      omega (Lattices.qk Q (v.adicCompletion F)) := fun h => hψΩ ((QIn.mem_commutator_iff Q _ ψ).mpr h)
  rw [QIn.mem_commutator_iff, Subgroup.coe_mul, map_mul]
  by_cases hexc : Module.finrank (v.adicCompletion F) (Fin 4 → v.adicCompletion F) = 4 ∧
      (Lattices.qk Q (v.adicCompletion F)).Anisotropic ∧ Valued.v (2 : v.adicCompletion F) = 1
  · obtain ⟨hn, han, h2⟩ := hexc
    exact QIn.mul_mem_of_relIndex_two (relIndex_omega_orthPrime_local v _ han hn h2) ha hb ha' hb'
  · exact absurd (omega_eq_orthPrime_local v _ hnd hexc ▸ ha) ha'

end QuadFormsKB.OMeara


example {F : Type} [Field F] [NumberField F] (h : QuadFormsKB.Lattices.QuaternarySpinorInput F) :
    QuadFormsKB.Lattices.QuaternarySpinorInput F :=
  { h with index := fun Q hQ v φ ψ => QuadFormsKB.OMeara.quaternarySpinor_index Q hQ v φ ψ }
