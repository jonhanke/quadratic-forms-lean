/-
# Cassels, Chapter 11, §1: spinor norms of lattices and the number of spinor genera

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$, a
$\mathbb Q$-quadratic space $V, \phi$); lattices `Lat F n`; the rotations `Tamagawa.soSub` ($O^+$), the spinor norm
`spinorNormHom`; O'Meara's proper spinor genus `SameProperSpinorGenus` (`Literature/OMeara/Sec102.lean`).

*Cassels' spinor genus is the proper spinor genus.* Cassels (1978, Ch. 11, (1.25)–(1.27), pp. 200–201) defines the
spinor genus by $\Gamma_p = \gamma\delta_p\Lambda_p$ with $\gamma \in O^+(V)$ and $\delta_p$ in the spinor kernel
$\Theta(V_p)$: this is O'Meara's *proper* spinor genus $\operatorname{spn}^+$ (`SameProperSpinorGenus`), and the number
of spinor genera in a genus of Cassels' Theorem 1.2 is O'Meara's $g^+(L)$ (`properSpinorGenusNumber`).

**Defines**
* `latSpinorNormGroup Q hQ L` $= \theta(\Lambda) = \{\theta(\alpha) : \alpha \in O^+(\Lambda)\}$ (Cassels (1.20),
  p. 200), as the subgroup of $F^\times$ of the $a$ whose square class is such a spinor norm (the global analogue of
  `localSpinorNormGroup`, which is Cassels' $\theta(\Lambda_p)$, (1.21)).

**Proves**
* Lemma 1.3 (p. 200): (i) isometric lattices have the same $\theta(\Lambda)$
  (`latSpinorNormGroup_eq_of_isIsometric`); (ii) lattices in one genus have the same $\theta(\Lambda_p)$ for every $p$
  (`localSpinorNormGroup_eq_of_sameGenus`). Both by transport of structure: $\theta(\gamma\alpha\gamma^{-1}) =
  \theta(\alpha)$.
* Theorem 1.2 (p. 202), first two assertions: the number of (proper) spinor genera in the genus of an integral
  lattice is finite and a power of $2$ (`properSpinorGenusNumber_eq_two_pow`), and the same for O'Meara's $g(L)$
  (`spinorGenusNumber_eq_two_pow`). The proof: the spinor genera in $\operatorname{gen}L$ are in bijection with the
  group $O(V)(\mathbb A_f)/O(V)O'(V_{\mathbb A_f})O(\hat L)$ (`spinorGeneraEquivQuot`), of exponent $2$; it is finite
  because the class number is (`ClassFin.genusClasses_finite_of_nondegenerate`); and $g^+ \in \{g, 2g\}$
  (`properSpinorGenusNumber_eq`, O'Meara 102:2).
-/
import QuadFormsKB.Literature.OMeara.Sec101D
import QuadFormsKB.Literature.OMeara.Sec102Spn
import QuadFormsKB.Lattices.ClassFinite

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### Conjugation invariance of the spinor norm on rotations -/

section Conj

variable (K : Type*) [Field K] [Algebra F K] [CharZero K]

theorem spinorNorm_conj (hQ : Q.Nondegenerate) (g σ : orthGroup Q K) :
    spinorNorm Q K (g * σ * g⁻¹) = spinorNorm Q K σ := by
  rw [← spinorNormHom_apply Q K hQ, map_mul, map_mul, map_inv, mul_comm (spinorNormHom Q K hQ g),
    mul_assoc, mul_inv_cancel, mul_one, spinorNormHom_apply]

theorem conj_mem_soSub (g σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K) :
    g * σ * g⁻¹ ∈ Tamagawa.soSub Q K := by
  rw [Tamagawa.mem_soSub] at hσ ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, det_mul, hσ, mul_one]
  rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]

/-- **Transport of structure for spinor norm images**: if $H' = gHg^{-1}$, then $\theta(H \cap O^+) =
\theta(H' \cap O^+)$. -/
theorem map_spinorNormHom_conj (hQ : Q.Nondegenerate) (g : orthGroup Q K) {H H' : Subgroup (orthGroup Q K)}
    (hH : ∀ σ, σ ∈ H' ↔ g⁻¹ * σ * g ∈ H) :
    (H ⊓ Tamagawa.soSub Q K).map (spinorNormHom Q K hQ) =
      (H' ⊓ Tamagawa.soSub Q K).map (spinorNormHom Q K hQ) := by
  ext c
  simp only [Subgroup.mem_map, Subgroup.mem_inf, spinorNormHom_apply]
  constructor
  · rintro ⟨σ, ⟨hσH, hσS⟩, rfl⟩
    refine ⟨g * σ * g⁻¹, ⟨(hH _).mpr (by simpa [mul_assoc] using hσH), conj_mem_soSub Q K g σ hσS⟩,
      spinorNorm_conj Q K hQ g σ⟩
  · rintro ⟨σ, ⟨hσH, hσS⟩, rfl⟩
    refine ⟨g⁻¹ * σ * g, ⟨(hH σ).mp hσH, by simpa using conj_mem_soSub Q K g⁻¹ σ hσS⟩, ?_⟩
    simpa using spinorNorm_conj Q K hQ g⁻¹ σ

end Conj

/-! ### $\theta(\Lambda)$ and Lemma 1.3 -/

/-- **The spinor norm group of a lattice** $\theta(\Lambda) = \{\theta(\alpha) : \alpha \in O^+(\Lambda)\}$
(Cassels 1978, Ch. 11, (1.20), p. 200), as the subgroup of the $a \in F^\times$ whose square class $aF^{\times 2}$ is
the spinor norm of a rotation $\alpha \in O^+(V)$ with $\alpha\Lambda = \Lambda$. -/
@[kb "cassels1978" "Ch. 11, §1, (1.20), p. 200 (θ(Λ))"]
def latSpinorNormGroup (hQ : Q.Nondegenerate) (L : Lat F n) : Subgroup Fˣ :=
  ((autLat Q L.1 ⊓ Tamagawa.soSub Q F).map (spinorNormHom Q F hQ)).comap (sqClassHom F)

theorem mem_latSpinorNormGroup (hQ : Q.Nondegenerate) (L : Lat F n) {a : Fˣ} :
    a ∈ latSpinorNormGroup Q hQ L ↔
      ∃ σ ∈ autLat Q L.1 ⊓ Tamagawa.soSub Q F, spinorNorm Q F σ = SqClass.mk a := by
  simp [latSpinorNormGroup, sqClassHom_apply, spinorNormHom_apply]

/-- **Cassels, Lemma 1.3 (i)** (Ch. 11, p. 200): equivalent lattices have the same spinor norm group,
$\theta(\Lambda) = \theta(\Gamma)$ if $\Gamma = \gamma\Lambda$ with $\gamma \in O(V)$ ("by transport of structure"). -/
@[kb "cassels1978" "Ch. 11, Lemma 1.3 (i), p. 200"]
theorem latSpinorNormGroup_eq_of_isIsometric (hQ : Q.Nondegenerate) {L M : Lat F n}
    (h : IsIsometric Q L.1 M.1) : latSpinorNormGroup Q hQ L = latSpinorNormGroup Q hQ M := by
  obtain ⟨γ, hγ, he⟩ := h
  unfold latSpinorNormGroup
  congr 1
  refine map_spinorNormHom_conj Q F hQ ⟨γ, hγ⟩ fun σ => ?_
  rw [mem_autLat, mem_autLat, ← he]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, glImage_mul]
  constructor
  · intro hσ
    rw [hσ, ← glImage_mul, inv_mul_cancel, glImage_one]
  · intro hσ
    conv_rhs => rw [← hσ]
    rw [← glImage_mul, ← glImage_mul, ← glImage_mul, mul_inv_cancel, one_mul]

/-- **Cassels, Lemma 1.3 (ii)** (Ch. 11, p. 200): lattices in the same genus have the same local spinor norm groups
$\theta(\Lambda_p) = \theta(\Gamma_p)$ at every finite prime $p$. -/
@[kb "cassels1978" "Ch. 11, Lemma 1.3 (ii), p. 200"]
theorem localSpinorNormGroup_eq_of_sameGenus (hQ : Q.Nondegenerate) {L M : Lat F n} (h : SameGenus Q L.1 M.1)
    (v : HeightOneSpectrum (𝓞 F)) : localSpinorNormGroup Q hQ v L = localSpinorNormGroup Q hQ v M := by
  obtain ⟨g, hg, he⟩ := h v
  unfold localSpinorNormGroup
  congr 1
  refine map_spinorNormHom_conj Q _ hQ ⟨g, hg⟩ fun σ => ?_
  change locAct v _ (loc v M.1) = loc v M.1 ↔ locAct v _ (loc v L.1) = loc v L.1
  rw [← he]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
  constructor
  · intro hσ
    rw [hσ, ← locAct_mul, inv_mul_cancel, locAct_one]
  · intro hσ
    conv_rhs => rw [← hσ]
    rw [← locAct_mul, ← locAct_mul, ← locAct_mul, mul_inv_cancel, one_mul]

/-! ### Theorem 1.2: the number of spinor genera is finite and a power of $2$ -/

/-- The spinor genera in $\operatorname{gen}L$ (as classes of `spnSetoid`) are the classes of the
`spnGroup`-orbits on the genus. -/
def genusSpinorGeneraEquiv (L : Lat F n) :
    @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (spnGroup Q) L ≃ genusSpinorGenera Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  refine Equiv.ofBijective
    (Quotient.lift (fun M => (⟨Quotient.mk (spnSetoid Q) (M : Lat F n), M, rfl, ?_⟩ : genusSpinorGenera Q L))
      fun M M' h => Subtype.ext (Quotient.sound ((spinorRel_iff Q L M M').mp h))) ⟨?_, ?_⟩
  · exact (Set.ext_iff.mp (orbit_eq_genus Q L) M).mp M.2
  · intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact Quotient.sound ((spinorRel_iff Q L _ _).mpr (Quotient.exact (congrArg Subtype.val hxy)))
  · rintro ⟨_, M, rfl, hM⟩
    have hM' : M ∈ @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L := by
      rw [orbit_eq_genus]; exact hM
    exact ⟨Quotient.mk _ ⟨M, hM'⟩, rfl⟩

/-- The spinor genera in the genus of an integral lattice are finite in number. -/
theorem genusSpinorGenera_finite (hQ : Q.Nondegenerate) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    (genusSpinorGenera Q L).Finite := by
  have hG := ClassFin.genusClasses_finite_of_nondegenerate hQ L hLi
  refine (hG.image (fun c : LatClass Q => (Quotient.mk (spnSetoid Q) c.out))).subset ?_
  rintro _ ⟨M, rfl, hM⟩
  refine ⟨Quotient.mk _ M, ⟨M, rfl, hM⟩, Quotient.sound ?_⟩
  exact IsIsometric.sameSpinorGenus Q (Quotient.exact (Quotient.out_eq (Quotient.mk (latSetoid Q) M)))

/-- **$g(L)$ is a power of $2$**: for an integral lattice $L$ on a regular space, the number of spinor genera in
$\operatorname{gen}L$ is finite and equal to $2^k$ for some $k$. -/
@[kb "omeara1963" "§102B, 102:8, p. 302 (the number of spinor genera is a power of 2)"]
theorem spinorGenusNumber_eq_two_pow (hQ : Q.Nondegenerate) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    (genusSpinorGenera Q L).Finite ∧ ∃ k : ℕ, spinorGenusNumber Q L = 2 ^ k := by
  have hfin := genusSpinorGenera_finite Q hQ L hLi
  refine ⟨hfin, ?_⟩
  have : Fact Q.Nondegenerate := ⟨hQ⟩
  let e : OAf Q ⧸ spnLocGroup Q L ≃ genusSpinorGenera Q L :=
    (spinorGeneraEquivQuot Q hQ L).symm.trans (genusSpinorGeneraEquiv Q L)
  have : Finite (genusSpinorGenera Q L) := hfin.to_subtype
  have : Finite (OAf Q ⧸ spnLocGroup Q L) := Finite.of_equiv _ e.symm
  have hp : IsPGroup 2 (OAf Q ⧸ spnLocGroup Q L) := fun x =>
    ⟨1, by rw [pow_one, sq]; exact spinorGeneraQuot_mul_self Q L x⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  refine ⟨k, ?_⟩
  rw [spinorGenusNumber, ← Nat.card_coe_set_eq, ← Nat.card_congr e, hk]

/-- **Cassels, Theorem 1.2** (Ch. 11, p. 202), the first two assertions: *the number of spinor genera in a genus is
finite and a power of $2$.* Cassels' spinor genus is the proper spinor genus (module docstring), so the number is
$g^+(L)$ = `properSpinorGenusNumber`. Stated for an integral lattice $L$ (Cassels' finiteness argument is Theorem 1.1
of Chapter 9, finiteness of the class number of an integral form; every lattice becomes integral after scaling).
The third assertion (the number "can always be determined effectively") is Cassels' Theorem 3.1. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.2, p. 202 (finite and a power of 2)"]
theorem properSpinorGenusNumber_eq_two_pow (hQ : Q.Nondegenerate) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    (genusProperSpinorGenera Q L).Finite ∧ ∃ k : ℕ, properSpinorGenusNumber Q L = 2 ^ k := by
  obtain ⟨hfin, k, hk⟩ := spinorGenusNumber_eq_two_pow Q hQ L hLi
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine (hfin.image spnLift₁).subset ?_
      rintro _ ⟨M, rfl, hM⟩
      set c : Quotient (spnSetoid Q) := Quotient.mk _ M
      obtain ⟨γ, k', hk', he⟩ := (mem_latSpinorGenus Q).mp (Quotient.exact (Quotient.out_eq c))
      exact ⟨c, ⟨M, rfl, hM⟩, Quotient.sound ((sameProperSpinorGenus_iff Q).mpr
        ⟨γ, by simp [Tamagawa.mem_soSub], k', hk', he⟩)⟩
    · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
      exact ((hfin.image _).union (hfin.image _)).subset (genusProperSpinorGenera_subset τ hQ hτ L)
  · rcases properSpinorGenusNumber_eq Q hQ L with h | h
    · exact ⟨k, h.trans hk⟩
    · exact ⟨k + 1, by rw [h, hk, pow_succ, mul_comm]⟩

end QuadFormsKB.Lattices
