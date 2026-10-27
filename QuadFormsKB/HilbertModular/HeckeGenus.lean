/-
# The $T(\mathfrak p^2)$ identity for the genus representation numbers over $F$

**Setting.** $F$ totally real with $\mathcal O_F$ a PID, $Q_0$ a totally positive definite form over $\mathcal O_F$ of even rank $n = 2k \ge 2$,
$Q = Q_0 \otimes F$ on $F^n$, $L = \mathcal O_F^n$, and the classes $\mathrm{cls}(M) \subseteq \mathrm{gen}(L)$ of the genus with weights $1/|O(M)|$ (full
orthogonal group, GL-classes). $\pi$ is a prime of $\mathcal O_F$ with $\pi \nmid 2\det H(Q_0)$, $q = N(\pi)$, $\chi_\pi$ = `Nbr.chiPi Q₀ π`.

**Main theorem** (`genus_sum_latRepF_sq`, the Eichler commutation relation averaged over the genus): for $\nu \in \mathcal O_F$, $\pi \nmid \nu$,
$$\sum_{\mathrm{cls}(M)}\frac{r_M(\pi^2\nu)}{|O(M)|} = \lambda_\pi\sum_{\mathrm{cls}(M)}\frac{r_M(\nu)}{|O(M)|},\qquad
  \lambda_\pi = q^{n-2} + \chi_\pi q^{n/2-1} + 1$$
(`heckeEigen`; for $n = 4$: $q^2 + \chi_\pi q + 1$, the $\mathbb Q$ value $p^2 + 1 + \varepsilon p$ of `Siegel.Kneser.genusRepAvg_neighbor_four`).

*Proof.* For each class representative $M = \gamma\mathcal O_F^n$ (free: PID), the single-lattice relation
(`Nbr.sum_latRep_neighbors_F` for the Gram form $Q_\gamma$, which is in the genus of $Q_0$, so $\pi \nmid \det H(Q_\gamma)$ and $Q_\gamma$ has the
counts and the character of $Q_0$ mod $\pi$) gives
$$(q - 1)\sum_{M' \sim_\pi M}r_{M'}(\nu) = (q-1)\,r_M(\pi^2\nu) + (q^{n-2} - q)\,r_M(\nu),\qquad (q-1)\#\{M' \sim_\pi M\} = q^{n-1} - 1 + \chi_\pi(q-1)q^{n/2-1}.$$
Averaging over the classes, the neighbour sum is $\#\{M'\}\sum r_M(\nu)/|O(M)|$ (`Lattices.DoubleCount.sum_inv_card_stab_sum_nb`:
neighbours stay in the genus, the relation is symmetric and $O(V)$-invariant). Solve for $\sum r_M(\pi^2\nu)/|O(M)|$.

**Hypothesis** `NbrInGenus Q₀ π`: $\pi$-neighbours of lattices in the genus are in the genus (Kneser 1957, Satz 1; O'Meara 1963, 92:2
for the local step). It is a statement about lattices only, not about theta series or Eisenstein series.

Over $\mathbb Q$: `Siegel.Kneser.genus_sum_neighbors`, `Siegel.Kneser.genusRepAvg_neighbor_four`.
-/
import QuadFormsKB.Lattices.NeighborGenus
import QuadFormsKB.Lattices.DoubleCount
import QuadFormsKB.HilbertModular.GenusTheta

open Matrix NumberField
open scoped Pointwise

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Kneser neighbours stay in the genus** (Kneser 1957, Satz 1 [unverified]; for $F = \mathbb Q$ proved as
`Siegel.Kneser.sameGenus_of_neighbor`): every $\pi$-neighbour $M'$ (`Nbr.IsNbrL`) of a lattice $M$ in the genus of $\mathcal O_F^n$ is in that
genus. Parameters: `Q₀` (the form over $\mathcal O_F$), `π` (the prime). Proved for $\mathcal O_F$ a PID and $\pi \nmid 2\det H$
(`HeckeGenusLocal.nbrInGenus_of_pid`). -/
@[kb "kneser1957" "Satz 1 (neighbours lie in the genus) [unverified]"]
def NbrInGenus (Q₀ : QuadForm (𝓞 F) n) (π : 𝓞 F) : Prop :=
  ∀ M M' : Submodule (𝓞 F) (Fin n → F), M.IsLattice F → SameGenus (formF Q₀) intVec M →
    IsNbrL (formF Q₀) π M M' → SameGenus (formF Q₀) intVec M'

/-- **The Eichler eigenvalue** $\lambda_\pi = q^{n-2} + \chi_\pi q^{n/2-1} + 1$ of $T(\pi^2)$ on $\theta_{\mathrm{Gen}}$ ($q = N(\pi)$, $\chi_\pi$ = `Nbr.chiPi`;
for $n = 4$, $q^2 + \chi_\pi q + 1$). -/
@[kb "eichler1952" "the T(𝔭²) eigenvalue of the genus theta series [unverified]"]
noncomputable def heckeEigen (Q₀ : QuadForm (𝓞 F) n) {π : 𝓞 F} (hπ : Prime π) : ℂ :=
  (nm π : ℂ) ^ (n - 2) + (chiPi Q₀ hπ : ℂ) * (nm π : ℂ) ^ (n / 2 - 1) + 1

/-! ### Genus lattices are free with Gram forms in the genus of $Q_0$ -/

section GenusLattice

variable [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n}
  (hQ : IsTotallyPosDef (formF Q₀))

/-- A lattice between $\pi M$ and $\pi^{-1}M$ is a lattice. -/
lemma isLattice_of_isNbrL {π : 𝓞 F} (hπ : Prime π) {M M' : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F)
    (h : IsNbrL (formF Q₀) π M M') : M'.IsLattice F := by
  have hπ0 : algebraMap (𝓞 F) F π ≠ 0 := by
    intro h0; exact hπ.ne_zero (IsFractionRing.injective (𝓞 F) F (by rw [h0, map_zero]))
  set u : Fˣ := Units.mk0 _ hπ0
  haveI := hM
  have h1 : u • M ≤ M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
    exact h.smul_right y hy
  have h2 : M' ≤ u⁻¹ • M := by
    intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨(algebraMap (𝓞 F) F π) • x, h.smul_left x hx, ?_⟩
    show (u⁻¹ : Fˣ) • ((algebraMap (𝓞 F) F π) • x) = x
    rw [Units.smul_def, smul_smul]; simp [u, hπ0]
  have hfg : M'.FG := Submodule.FG.of_le (Submodule.IsLattice.fg (A := F) (M := u⁻¹ • M)) h2
  exact Submodule.IsLattice.of_le_of_isLattice_of_fg F h1 hfg

include hQ in
/-- A lattice in the genus of $\mathcal O_F^n$ is $\gamma\mathcal O_F^n$ (PID), integral, with Gram form in the genus of $Q_0$. -/
lemma exists_gram_of_genus {M : Submodule (𝓞 F) (Fin n → F)} (hl : M.IsLattice F)
    (hg : SameGenus (formF Q₀) intVec M) :
    ∃ (γ : GL (Fin n) F) (h : IsIntegral (formF Q₀) (latOf γ)), M = latOf γ ∧
      FormSameGenus Q₀ (gramZ (formF Q₀) γ h) ∧ IsTotPosGram (gramF (gramZ (formF Q₀) γ h)) := by
  obtain ⟨γ, hγ⟩ := exists_latOf_of_isPrincipalIdealRing (n := n) ⟨M, hl⟩
  simp only at hγ
  have hi : IsIntegral (formF Q₀) (latOf γ) := by
    rw [← hγ]; exact SameGenus.isIntegral _ (isIntegral_stdLat Q₀) hg
  refine ⟨γ, hi, hγ, formSameGenus_gramZ Q₀ (by rwa [← hγ]) hi, isTotPosGram_gramZ hQ γ hi⟩

variable {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q₀.hessian.det)
include hQ hπ hdet

/-- The $\pi$-neighbours of a genus lattice form a finite set. -/
theorem finite_nbrSet {M : Submodule (𝓞 F) (Fin n → F)} (hl : M.IsLattice F)
    (hg : SameGenus (formF Q₀) intVec M) : {M' | IsNbrL (formF Q₀) π M M'}.Finite := by
  classical
  have := finite_res hπ
  letI := Fintype.ofFinite (Res π)
  obtain ⟨γ, h, rfl, hfs, -⟩ := exists_gram_of_genus hQ hl hg
  rw [setOf_isNbrL_latOf hπ γ h (not_dvd_det_of_formSameGenus hπ hfs hdet)]
  exact Set.Finite.image _ (Finset.finite_toSet _)

include h2 in
/-- **The single-lattice relation for a genus lattice** ($n$ even, $\pi \nmid 2\det H(Q_0)$, $\pi \nmid \nu$):
$(q - 1)\sum_{M' \sim_\pi M}r_{M'}(\nu) = (q-1)\,r_M(\pi^2\nu) + (q^{n-2} - q)\,r_M(\nu)$. -/
theorem sum_latRepF_nbr (hn : Even n) (hn2 : 2 ≤ n) {M : Submodule (𝓞 F) (Fin n → F)} (hl : M.IsLattice F)
    (hg : SameGenus (formF Q₀) intVec M) {ν : 𝓞 F} (hν : ¬ π ∣ ν) :
    ((nm π : ℤ) - 1) * ∑ M' ∈ (finite_nbrSet hQ hπ hdet hl hg).toFinset, (latRepF (formF Q₀) M' ν : ℤ) =
      ((nm π : ℤ) - 1) * latRepF (formF Q₀) M (π ^ 2 * ν) +
        ((nm π : ℤ) ^ (n - 2) - nm π) * latRepF (formF Q₀) M ν := by
  classical
  have := finite_res hπ
  letI := Fintype.ofFinite (Res π)
  obtain ⟨γ, h, rfl, hfs, hpos⟩ := exists_gram_of_genus hQ hl hg
  have hdet' := not_dvd_det_of_formSameGenus hπ hfs hdet
  have hS := setOf_isNbrL_latOf (Q := formF Q₀) hπ γ h hdet'
  have hfin : ∀ M : 𝓞 F, Set.Finite {y : Fin n → 𝓞 F | Nbr.qv (𝓞 F) (gramZ (formF Q₀) γ h) y = M} :=
    fun M => finite_repSetF hpos M
  have hT : (finite_nbrSet hQ hπ hdet hl hg).toFinset =
      (neighbors F (gramZ (formF Q₀) γ h) π).image (glImage γ) := by
    ext M'; simp only [Set.Finite.mem_toFinset, hS, Set.mem_image, Finset.mem_coe, Finset.mem_image]
  rw [hT, Finset.sum_image fun _ _ _ _ e => glImage_injective γ e]
  simp_rw [latRepF_glImage_eq γ h]
  have hL : latOf γ = glImage γ (Nbr.stdLat (𝓞 F) F n) := by rw [latOf, intVec_eq_stdLat]
  rw [hL, latRepF_glImage_eq γ h, latRepF_glImage_eq γ h, latRep_stdLat hfin, latRep_stdLat hfin]
  exact sum_latRep_neighbors_F hπ hpos h2 hdet' hn hn2 hν

include h2 in
/-- **The number of $\pi$-neighbours of a genus lattice** is that of $\mathcal O_F^n$:
$(q - 1)\cdot\#\{M' \sim_\pi M\} = q^{n-1} - 1 + \chi_\pi(q-1)q^{n/2-1}$, $\chi_\pi$ of $Q_0$. -/
theorem card_nbrSet (hn : Even n) (hn2 : 2 ≤ n) {M : Submodule (𝓞 F) (Fin n → F)} (hl : M.IsLattice F)
    (hg : SameGenus (formF Q₀) intVec M) :
    ((nm π : ℤ) - 1) * (finite_nbrSet hQ hπ hdet hl hg).toFinset.card =
      (nm π : ℤ) ^ (n - 1) - 1 + chiPi Q₀ hπ * ((nm π : ℤ) - 1) * (nm π : ℤ) ^ (n / 2 - 1) := by
  classical
  have := finite_res hπ
  letI := Fintype.ofFinite (Res π)
  obtain ⟨γ, h, rfl, hfs, hpos⟩ := exists_gram_of_genus hQ hl hg
  have hdet' := not_dvd_det_of_formSameGenus hπ hfs hdet
  have hS := setOf_isNbrL_latOf (Q := formF Q₀) hπ γ h hdet'
  have hT : (finite_nbrSet hQ hπ hdet hl hg).toFinset =
      (neighbors F (gramZ (formF Q₀) γ h) π).image (glImage γ) := by
    ext M'; simp only [Set.Finite.mem_toFinset, hS, Set.mem_image, Finset.mem_coe, Finset.mem_image]
  rw [hT, Finset.card_image_of_injective _ (glImage_injective γ),
    card_neighbors_F hπ h2 hdet' hn (by omega), chiPi_eq_of_formSameGenus hπ hfs h2 hdet hn hn2]

end GenusLattice

/-! ### Averaging over the genus -/

section Average

variable [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) n)

/-- **The lattices in the genus of $\mathcal O_F^n$** in $(F^n, Q_0)$. -/
abbrev GenLat : Type := {M : Submodule (𝓞 F) (Fin n → F) // M.IsLattice F ∧ SameGenus (formF Q₀) intVec M}

/-- $O(V)(F)$ acts on the genus by $g \cdot M = gM$. -/
noncomputable instance : MulAction (orthGroup (formF Q₀) F) (GenLat Q₀) where
  smul g M := ⟨glImage (g : GL (Fin n) F) M.1, glImage_isLattice _ M.2.1,
    M.2.2.trans _ (IsIsometric.sameGenus _ ⟨g, g.2, rfl⟩)⟩
  one_smul M := Subtype.ext (glImage_one _)
  mul_smul g h M := Subtype.ext (glImage_mul _ _ _)

variable {Q₀}

lemma genLat_smul_val (g : orthGroup (formF Q₀) F) (M : GenLat Q₀) :
    (g • M).1 = glImage (g : GL (Fin n) F) M.1 := rfl

/-- The stabilizer of $M$ is $O(M)$. -/
lemma card_stabilizer_genLat (M : GenLat Q₀) :
    Nat.card (MulAction.stabilizer (orthGroup (formF Q₀) F) M) = Nat.card (autLat (formF Q₀) M.1) := by
  have : MulAction.stabilizer (orthGroup (formF Q₀) F) M = autLat (formF Q₀) M.1 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_autLat, ← genLat_smul_val, Subtype.ext_iff]
  rw [this]

lemma autCard_eq (c : LatClass (formF Q₀)) :
    LatClass.autCard (formF Q₀) c = Nat.card (autLat (formF Q₀) c.out.1) := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

variable (hQ : IsTotallyPosDef (formF Q₀)) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2)
  (hdet : ¬ π ∣ Q₀.hessian.det) (hnb : NbrInGenus Q₀ π)
include hQ hπ h2 hdet hnb

/-- **The $T(\pi^2)$ relation for the genus representation numbers** (Eichler 1952; Kneser 1957): for $n$ even, $n \ge 2$, a good prime
$\pi \nmid 2\det H(Q_0)$ whose neighbours stay in the genus (`NbrInGenus`), and $\nu \in \mathcal O_F$ with $\pi \nmid \nu$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^n)}\frac{r_M(\pi^2\nu)}{|O(M)|} = \lambda_\pi\sum_{\mathrm{cls}(M)}\frac{r_M(\nu)}{|O(M)|},
  \qquad\lambda_\pi = q^{n-2} + \chi_\pi q^{n/2-1} + 1$$
(`heckeEigen`), the sums over the classes of the genus (`genusClasses`, representatives `c.out`, $|O(M)|$ = `LatClass.autCard`). -/
@[kb "eichler1952" "T(𝔭²) relation for the genus average, over F [unverified]"]
theorem genus_sum_latRepF_sq (hn : Even n) (hn2 : 2 ≤ n) {ν : 𝓞 F} (hν : ¬ π ∣ ν) :
    ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
        ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 (π ^ 2 * ν) : ℂ) =
      heckeEigen Q₀ hπ * ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
        ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) := by
  classical
  set C := (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset with hC
  set G := orthGroup (formF Q₀) F
  -- the relation on the genus
  set R : GenLat Q₀ → GenLat Q₀ → Prop := fun x y => IsNbrL (formF Q₀) π x.1 y.1 with hR
  have hinv : ∀ (g : G) (x y : GenLat Q₀), R (g • x) (g • y) ↔ R x y := fun g x y =>
    isNbrL_glImage_iff g.2
  have hsymm : ∀ x y, R x y → R y x := fun x y h => h.symm
  have hfinR : ∀ x : GenLat Q₀, {y | R x y}.Finite := fun x =>
    ((finite_nbrSet hQ hπ hdet x.2.1 x.2.2).preimage Subtype.val_injective.injOn)
  -- neighbours of genus lattices are genus lattices
  have hlift : ∀ x : GenLat Q₀, ∀ M', IsNbrL (formF Q₀) π x.1 M' →
      M'.IsLattice F ∧ SameGenus (formF Q₀) intVec M' := fun x M' h =>
    ⟨isLattice_of_isNbrL hπ x.2.1 h, hnb x.1 M' x.2.1 x.2.2 h⟩
  have hsum : ∀ (x : GenLat Q₀) (f : Submodule (𝓞 F) (Fin n → F) → ℂ),
      ∑ y ∈ (hfinR x).toFinset, f y.1 =
        ∑ M' ∈ (finite_nbrSet hQ hπ hdet x.2.1 x.2.2).toFinset, f M' := by
    intro x f
    refine Finset.sum_nbij' (fun y => y.1) (fun M' => if h : IsNbrL (formF Q₀) π x.1 M' then
      ⟨M', hlift x M' h⟩ else x) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢; exact hy
    · intro M' hM'
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hM' ⊢
      rw [dif_pos hM']; exact hM'
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hy
      rw [dif_pos hy]
    · intro M' hM'
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hM'
      rw [dif_pos hM']
    · intro y _; rfl
  have hcard : ∀ x : GenLat Q₀, (hfinR x).toFinset.card =
      (finite_nbrSet hQ hπ hdet x.2.1 x.2.2).toFinset.card := by
    intro x
    have := hsum x (fun _ => 1)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact_mod_cast this
  -- representatives
  let rep : C → GenLat Q₀ := fun c => ⟨c.1.out.1, c.1.out.2,
    sameGenus_out (L := HilbertModular.stdLat) ((Set.Finite.mem_toFinset _).mp c.2)⟩
  have hrep_inj : Function.Injective rep := by
    intro c c' h
    have h1 : c.1.out.1 = c'.1.out.1 := congrArg (fun x : GenLat Q₀ => x.1) h
    have h2 : c.1.out = c'.1.out := Subtype.ext h1
    exact Subtype.ext (by rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1, h2])
  set s := C.attach.image rep with hs
  have hreduce : ∀ (f : GenLat Q₀ → ℂ), ∑ x ∈ s, f x = ∑ c ∈ C.attach, f (rep c) :=
    fun f => Finset.sum_image fun c _ c' _ h => hrep_inj h
  -- hypotheses of the double counting lemma
  have hdist : ∀ x ∈ s, ∀ x' ∈ s, (∃ g : G, g • x' = x) → x = x' := by
    intro x hx x' hx' ⟨g, hg⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hx'
    have hiso : IsIsometric (formF Q₀) c'.1.out.1 c.1.out.1 := ⟨g, g.2, congrArg Subtype.val hg⟩
    have : c'.1 = c.1 := by
      rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]; exact Quotient.sound hiso
    rw [Subtype.ext this]
  have hclos : ∀ x ∈ s, ∀ y, R x y → ∃ x' ∈ s, ∃ g : G, g • x' = y := by
    intro x _ y _
    set c : LatClass (formF Q₀) := Quotient.mk _ ⟨y.1, y.2.1⟩
    have hc : c ∈ C := (Set.Finite.mem_toFinset _).mpr ⟨⟨y.1, y.2.1⟩, rfl, y.2.2⟩
    refine ⟨rep ⟨c, hc⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    have hiso : IsIsometric (formF Q₀) c.out.1 y.1 := Quotient.exact (Quotient.out_eq c)
    obtain ⟨γ, hγ, he⟩ := hiso
    exact ⟨⟨γ, hγ⟩, Subtype.ext he⟩
  have hstab : ∀ x ∈ s, 0 < Nat.card (MulAction.stabilizer G x) := by
    intro x _
    rw [card_stabilizer_genLat]
    have := finite_autLat hQ x.2.1 (SameGenus.isIntegral _ (isIntegral_stdLat Q₀) x.2.2)
    exact Nat.card_pos
  have hf : ∀ (m : 𝓞 F) (g : G) (x : GenLat Q₀), (latRepF (formF Q₀) (g • x).1 m : ℂ) = latRepF (formF Q₀) x.1 m :=
    fun m g x => by rw [genLat_smul_val, latRepF_glImage g.2]
  have hdc := Lattices.DoubleCount.sum_inv_card_stab_sum_nb hinv hsymm hfinR s hdist hclos hstab
    (fun x => (latRepF (formF Q₀) x.1 ν : ℂ)) (hf ν)
  -- the per-lattice relations, in `ℂ`
  set q : ℂ := (nm π : ℂ)
  have hrel : ∀ x : GenLat Q₀, (q - 1) * ∑ y ∈ (hfinR x).toFinset, (latRepF (formF Q₀) y.1 ν : ℂ) =
      (q - 1) * latRepF (formF Q₀) x.1 (π ^ 2 * ν) + (q ^ (n - 2) - q) * latRepF (formF Q₀) x.1 ν := by
    intro x
    rw [hsum x (fun M => (latRepF (formF Q₀) M ν : ℂ))]
    have := congrArg (fun z : ℤ => (z : ℂ)) (sum_latRepF_nbr hQ hπ h2 hdet hn hn2 x.2.1 x.2.2 hν)
    push_cast at this
    exact this
  have hnb' : ∀ x : GenLat Q₀, (q - 1) * ((hfinR x).toFinset.card : ℂ) =
      q ^ (n - 1) - 1 + (chiPi Q₀ hπ : ℂ) * (q - 1) * q ^ (n / 2 - 1) := by
    intro x
    rw [hcard x]
    have := congrArg (fun z : ℤ => (z : ℂ)) (card_nbrSet hQ hπ h2 hdet hn hn2 x.2.1 x.2.2)
    push_cast at this
    exact this
  -- solve
  have hq1 : q - 1 ≠ 0 := by
    have : 1 < nm π := by
      have h1 : nm π ≠ 1 := fun h => hπ.not_isUnit ((nm_eq_one_iff π).mp h)
      have h0 : nm π ≠ 0 := by
        rw [nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
      omega
    intro h
    have : (nm π : ℂ) = 1 := by linear_combination h
    norm_cast at this
    omega
  have hn' : n - 2 + 1 = n - 1 := by omega
  have key : ∀ x : GenLat Q₀, (q - 1) * (latRepF (formF Q₀) x.1 (π ^ 2 * ν) : ℂ) =
      (q - 1) * heckeEigen Q₀ hπ * latRepF (formF Q₀) x.1 ν +
        ((q - 1) * ∑ y ∈ (hfinR x).toFinset, (latRepF (formF Q₀) y.1 ν : ℂ) -
          (q - 1) * ((hfinR x).toFinset.card : ℂ) * latRepF (formF Q₀) x.1 ν) := by
    intro x
    rw [hrel x, mul_assoc (q - 1) (((hfinR x).toFinset.card : ℂ)), ← mul_assoc, hnb' x, heckeEigen]
    rw [← hn', pow_succ]
    ring
  apply mul_left_cancel₀ hq1
  have hC' : ∀ (f : C → ℂ), ∑ c ∈ C.attach, f c = ∑ c ∈ C, if h : c ∈ C then f ⟨c, h⟩ else 0 := by
    intro f
    rw [← Finset.sum_attach C (fun c => if h : c ∈ C then f ⟨c, h⟩ else 0)]
    refine Finset.sum_congr rfl fun c _ => by rw [dif_pos c.2]
  -- rewrite the class sums as sums over `s`
  have hw : ∀ (m : 𝓞 F), ∑ c ∈ C, ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 m : ℂ) =
      ∑ x ∈ s, ((Nat.card (MulAction.stabilizer G x) : ℂ))⁻¹ * (latRepF (formF Q₀) x.1 m : ℂ) := by
    intro m
    rw [hreduce, ← Finset.sum_attach C]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [card_stabilizer_genLat, autCard_eq]
  rw [hw, hw, Finset.mul_sum, Finset.mul_sum]
  have hsplit : ∀ x ∈ s, (q - 1) * (((Nat.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
      (latRepF (formF Q₀) x.1 (π ^ 2 * ν) : ℂ)) =
      (q - 1) * (heckeEigen Q₀ hπ * (((Nat.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
        (latRepF (formF Q₀) x.1 ν : ℂ))) +
      ((q - 1) * (((Nat.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
          ∑ y ∈ (hfinR x).toFinset, (latRepF (formF Q₀) y.1 ν : ℂ)) -
        (q - 1) * (((Nat.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
          ((hfinR x).toFinset.card : ℂ) * (latRepF (formF Q₀) x.1 ν : ℂ))) := by
    intro x _
    have := key x
    linear_combination ((Nat.card (MulAction.stabilizer G x) : ℂ))⁻¹ * this
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [hdc, sub_self, add_zero]

end Average

end QuadFormsKB.HilbertModular
