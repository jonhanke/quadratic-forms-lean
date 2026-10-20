/-
# The mass as an adelic volume, Tamagawa measures, and the Smith–Minkowski–Siegel mass formula

**Layer:** lattices over $\mathcal O_F$ in a totally positive definite space $(F^n, Q)$, $F$ a (totally real)
number field (`Lattices/`), with the class set as a double coset space (`Lattices/ClassSet.lean`).

**Proves (unconditionally)**
* `mass_eq_dcMass`: $\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M) \subseteq \mathrm{gen}(L)} 1/|O(M)| = \mathrm{dcMass}(O(V)(F), O(\hat L)) =
  \sum_{\Gamma\alpha K} 1/|\Gamma \cap \alpha K\alpha^{-1}|$, $\Gamma = O(V)(F)$, $K = O(\hat L)$ inside $O(V)(\mathbb A_f)$. With
  `dcMass_of_le` this says $\mathrm{Mass}(L) = \mathrm{vol}(O(V)(F)\backslash O(V)(\mathbb A_f))/\mathrm{vol}(O(\hat L))$ for any left Haar
  measure (`mass_mul_vol_eq`); the archimedean group $O(V)(F \otimes \mathbb R)$ is compact and contributes the same factor
  to numerator and denominator.
* `mass_SO_eq_two_mul_mass` (for $L = \mathcal O_F^n$): $\mathrm{dcMass}(SO(V)(F), SO(\hat L)) = 2\,\mathrm{Mass}(L)$. *Proof:*
  $O(V)(\mathbb A_f) = SO(V)(\mathbb A_f)\cdot O(\hat L)$ (local reflections, `Reflection.lean`) and $[O(V)(F) : SO(V)(F)] = 2$;
  then `dcMass_normal`.

**Defines** the Tamagawa measure of $K_{SO} = SO(V)(F\otimes\mathbb R) \times SO(\hat L)$ and $\tau(SO)$ (`tamagawaK`,
`tauSO`), and states $\tau(SO) = 2$ as a cited input (`TamagawaNumberTwo`, Weil 1982).

**Proves (conditionally on $\tau(SO) = 2$)** the mass formula `massFormula`:
$$\mathrm{Mass}(\mathcal O_F^n) = \frac{|d_F|^{n(n-1)/4}}{\prod_{\sigma}\mathrm{vol}(SO(V_\sigma))\cdot\prod_{\mathfrak p}\alpha_\mathfrak p(L, L)},$$
and its explicit form for odd $n$ (`massFormula_odd`).

**Conventions:** classes are $O(V)(F)$-orbits ($\mathrm{GL}_n(\mathcal O_F)$-classes for free lattices,
`isIsometric_latOf_iff`), weighted by $1/|O(M)|$ with $O(M) \subseteq \mathrm{GL}$ including improper automorphisms. The
adelic group is $SO$ (connected; $\prod_\mathfrak p \mathrm{vol}(O(L_\mathfrak p))$ diverges, each factor being $\approx 2$), and the factor $2$
between the $SO$- and $O$-masses is tracked in `mass_SO_eq_two_mul_mass`.
-/
import QuadFormsKB.Tamagawa.LocalVolume
import QuadFormsKB.Lattices.Finite
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Analysis.NFLFunctions

open NumberField IsDedekindDomain MulAction Matrix
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices

section MassVolume

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- The lattice $hL$ attached to the coset $h\,O(\hat L)$. -/
def cosetLat (L : Lat F n) : OAf Q ⧸ locStab Q L → Lat F n :=
  Quotient.lift (fun h => latSMul Q h L) (fun a b hab => by
    have hab : a⁻¹ * b ∈ locStab Q L := QuotientGroup.leftRel_apply.mp hab
    rw [← stabilizer_eq_locStab Q L] at hab
    have := (@MulAction.mem_stabilizer_iff (OAf Q) (Lat F n) _ (latAction Q) _ _).mp hab
    change latSMul Q (a⁻¹ * b) L = L at this
    have h2 := congrArg (latSMul Q a) this
    change @HSMul.hSMul _ _ _ (@instHSMul _ _ (latAction Q).toSMul) a
      (@HSMul.hSMul _ _ _ (@instHSMul _ _ (latAction Q).toSMul) (a⁻¹ * b) L) = latSMul Q a L at h2
    rw [← (latAction Q).mul_smul, mul_inv_cancel_left] at h2
    exact h2.symm)

theorem cosetLat_mk (L : Lat F n) (h : OAf Q) : cosetLat Q L (QuotientGroup.mk h) = latSMul Q h L := rfl

theorem latSMul_mul (a b : OAf Q) (L : Lat F n) : latSMul Q (a * b) L = latSMul Q a (latSMul Q b L) :=
  (latAction Q).mul_smul a b L

theorem cosetLat_injective (L : Lat F n) : Function.Injective (cosetLat Q L) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  rw [cosetLat_mk, cosetLat_mk] at hxy
  rw [QuotientGroup.eq, ← stabilizer_eq_locStab Q L]
  refine (@MulAction.mem_stabilizer_iff (OAf Q) (Lat F n) _ (latAction Q) _ _).mpr ?_
  change latSMul Q (a⁻¹ * b) L = L
  rw [latSMul_mul, ← hxy, ← latSMul_mul, inv_mul_cancel]
  exact (latAction Q).one_smul L

theorem cosetLat_smul (L : Lat F n) (γ : ratPoints Q) (x : OAf Q ⧸ locStab Q L) :
    ∃ γ₀ : orthGroup Q F, cosetLat Q L (γ • x) = Lat.image (γ₀ : GL (Fin n) F) (cosetLat Q L x) := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  refine ⟨γ₀, ?_⟩
  induction x using QuotientGroup.induction_on with | H a => ?_
  show latSMul Q ((γ : OAf Q) * a) L = _
  rw [latSMul_mul, cosetLat_mk, ← hγ₀, diagF_smul]

/-- **Classes = $\Gamma$-orbits:** $hL \cong h'L$ iff $h' O(\hat L) \in \Gamma h O(\hat L)$. -/
theorem isIsometric_cosetLat_iff (L : Lat F n) (x y : OAf Q ⧸ locStab Q L) :
    IsIsometric Q (cosetLat Q L x).1 (cosetLat Q L y).1 ↔ ∃ γ : ratPoints Q, γ • x = y := by
  constructor
  · rintro ⟨γ₀, hγ₀, he⟩
    refine ⟨⟨diagF Q ⟨γ₀, hγ₀⟩, ⟨_, rfl⟩⟩, cosetLat_injective Q L ?_⟩
    induction x using QuotientGroup.induction_on with | H a => ?_
    show latSMul Q (diagF Q ⟨γ₀, hγ₀⟩ * a) L = _
    rw [latSMul_mul, diagF_smul]
    exact Lattices.Lat.ext he
  · rintro ⟨γ, rfl⟩
    obtain ⟨γ₀, h⟩ := cosetLat_smul Q L γ x
    exact ⟨γ₀, γ₀.2, by rw [h]; rfl⟩

/-- **The stabilizer of $\alpha O(\hat L)$ in $\Gamma = O(V)(F)$ has the order of $O(\alpha L)$** ((4.11) of the AWS notes
over $F$, `card_autLat_eq`). -/
theorem card_stabilizer_coset (L : Lat F n) (α : OAf Q) :
    Nat.card (stabilizer (ratPoints Q) (QuotientGroup.mk α : OAf Q ⧸ locStab Q L)) =
      Nat.card (autLat Q (latSMul Q α L).1) := by
  rw [← card_autLat_eq Q α L]
  refine Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, γ.1.2, AWS.mem_conjSub.mpr ((mem_stabilizer_coset _ _ α γ.1).mp γ.2)⟩
      invFun := fun γ => ⟨⟨γ.1, γ.2.1⟩, (mem_stabilizer_coset _ _ α ⟨γ.1, γ.2.1⟩).mpr
        (AWS.mem_conjSub.mp γ.2.2)⟩
      left_inv := fun γ => rfl
      right_inv := fun γ => rfl }

/-- **The mass of the genus is the mass of the double coset space** (unconditional):
$$\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{1}{|O(M)|} =
  \sum_{\Gamma\alpha K \in \Gamma\backslash O(V)(\mathbb A_f)/K}\frac{1}{|\Gamma\cap\alpha K\alpha^{-1}|},\qquad
  \Gamma = O(V)(F),\ K = O(\hat L),$$
for every lattice $L$ (both sides are `finsum`s, matched term by term; they are finite sums for an integral $L$ in a
totally positive definite space, `genusClasses_finite`) (AWS notes (4.11)–(4.12) over $F$; Weil 1982, §3.5
[unverified locator]). Classes and $O(M)$ include improper isometries (the convention of this repository). -/
@[kb "hanke2011aws" "§4.6, (4.11)-(4.12) (over F)"]
theorem mass_eq_dcMass (L : Lat F n) :
    mass Q L = dcMass (ratPoints Q) (locStab Q L) := by
  classical
  let Φ : orbitRel.Quotient (ratPoints Q) (OAf Q ⧸ locStab Q L) → LatClass Q :=
    fun ω => Quotient.mk _ (cosetLat Q L ω.out)
  have hΦinj : Function.Injective Φ := by
    intro ω₁ ω₂ h
    have h' := Quotient.exact h
    obtain ⟨γ, hγ⟩ := (isIsometric_cosetLat_iff Q L _ _).mp h'
    rw [← Quotient.out_eq' ω₁, ← Quotient.out_eq' ω₂]
    apply Quotient.sound'
    rw [orbitRel_apply]
    rw [← hγ]
    exact ⟨γ⁻¹, inv_smul_smul γ _⟩
  have hrange : Φ '' Set.univ = genusClasses Q L := by
    ext c
    constructor
    · rintro ⟨ω, -, rfl⟩
      refine ⟨cosetLat Q L ω.out, rfl, ?_⟩
      induction ω.out using QuotientGroup.induction_on with | H a => ?_
      have := orbit_eq_genus Q L
      have hmem : latSMul Q a L ∈ @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L := ⟨a, rfl⟩
      rw [this] at hmem
      exact hmem
    · rintro ⟨M, rfl, hM⟩
      have hmem : M ∈ latGenus Q L := hM
      rw [← orbit_eq_genus Q L] at hmem
      obtain ⟨a, ha⟩ := hmem
      refine ⟨Quotient.mk'' (QuotientGroup.mk a), Set.mem_univ _, ?_⟩
      apply Quotient.sound
      show IsIsometric Q (cosetLat Q L _).1 M.1
      have h1 : (Quotient.mk'' (QuotientGroup.mk a : OAf Q ⧸ locStab Q L) :
          orbitRel.Quotient (ratPoints Q) _).out ∈ orbit (ratPoints Q) (QuotientGroup.mk a) :=
        out_mem_orbit _ _ rfl
      obtain ⟨γ, hγ⟩ := h1
      have := (isIsometric_cosetLat_iff Q L (QuotientGroup.mk a) _).mpr ⟨γ, hγ⟩
      rw [cosetLat_mk] at this
      have hM' : (latSMul Q a L) = M := ha
      rw [hM'] at this
      exact IsIsometric.symm Q this
  unfold mass dcMass orbitMass
  rw [← hrange, finsum_mem_image hΦinj.injOn, finsum_mem_univ]
  congr 1
  ext ω
  have hω : ω.out = QuotientGroup.mk ω.out.out := (QuotientGroup.out_eq' ω.out).symm
  show ((Nat.card (autLat Q (cosetLat Q L ω.out).1) : ℝ))⁻¹ = _
  rw [hω, cosetLat_mk, card_stabilizer_coset]

/-- The map from orbits to classes used in `mass_eq_dcMass`. -/
def orbitToClass (L : Lat F n) : orbitRel.Quotient (ratPoints Q) (OAf Q ⧸ locStab Q L) → LatClass Q :=
  fun ω => Quotient.mk _ (cosetLat Q L ω.out)

theorem orbitToClass_injective (L : Lat F n) : Function.Injective (orbitToClass Q L) := by
  intro ω₁ ω₂ h
  have h' := Quotient.exact h
  obtain ⟨γ, hγ⟩ := (isIsometric_cosetLat_iff Q L _ _).mp h'
  rw [← Quotient.out_eq' ω₁, ← Quotient.out_eq' ω₂]
  apply Quotient.sound'
  rw [orbitRel_apply, ← hγ]
  exact ⟨γ⁻¹, inv_smul_smul γ _⟩

theorem orbitToClass_image (L : Lat F n) : orbitToClass Q L '' Set.univ ⊆ genusClasses Q L := by
  rintro _ ⟨ω, -, rfl⟩
  refine ⟨cosetLat Q L ω.out, rfl, ?_⟩
  induction ω.out using QuotientGroup.induction_on with | H a => ?_
  have hmem : latSMul Q a L ∈ @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L := ⟨a, rfl⟩
  rw [orbit_eq_genus Q L] at hmem
  exact hmem

/-- **Finitely many double cosets** for an integral lattice in a totally positive definite space. -/
theorem finite_orbits {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    Finite (orbitRel.Quotient (ratPoints Q) (OAf Q ⧸ locStab Q L)) := by
  have h := ((genusClasses_finite hQ L hLi).subset (orbitToClass_image Q L)).of_finite_image
    (orbitToClass_injective Q L).injOn
  exact Set.finite_univ_iff.mp h

/-- **Finite stabilizers** $\Gamma \cap \alpha K\alpha^{-1} \cong O(\alpha L)$. -/
theorem finite_stabilizer {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    (x : OAf Q ⧸ locStab Q L) : Finite (stabilizer (ratPoints Q) x) := by
  induction x using QuotientGroup.induction_on with | H α => ?_
  have hgen : SameGenus Q L.1 (latSMul Q α L).1 := by
    have hmem : latSMul Q α L ∈ @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L := ⟨α, rfl⟩
    rw [orbit_eq_genus Q L] at hmem
    exact hmem
  have := finite_autLat hQ (latSMul Q α L).2 (hgen.isIntegral Q hLi)
  apply Nat.finite_of_card_ne_zero
  rw [card_stabilizer_coset]
  exact Nat.card_pos.ne'

end MassVolume

/-! ### $SO$ versus $O$: the factor $2$ -/

section SO

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$SO(V)(\mathbb A_f)$**: the $h \in O(V)(\mathbb A_f)$ with $\det h_\mathfrak p = 1$ at every $\mathfrak p$. -/
@[kb "weil1982" "§3.5 [unverified locator]"]
def soAf (Q : QuadForm F n) : Subgroup (OAf Q) where
  carrier := {h | ∀ v, ((h v : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)).val.det = 1}
  mul_mem' {a b} ha hb v := by
    have := (soSub Q (v.adicCompletion F)).mul_mem (ha v) (hb v)
    exact this
  one_mem' v := (soSub Q (v.adicCompletion F)).one_mem
  inv_mem' {a} ha v := (soSub Q (v.adicCompletion F)).inv_mem (ha v)

/-- The standard lattice $\mathcal O_F^n$. -/
abbrev stdLat (F : Type*) [Field F] [NumberField F] (n : ℕ) : Lat F n := ⟨intVec, intVec_isLattice⟩

theorem nondegenerate_map (hQ : Q₀.Nondegenerate) : (QF).Nondegenerate := by
  rw [QuadForm.Nondegenerate]
  have : (QF).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (RingOfIntegers.coe_injective)).mpr hQ

/-- **$O(V)(\mathbb A_f) = SO(V)(\mathbb A_f)\cdot O(\hat{\mathcal O}_F^n)$**: correct the determinant at each prime by a
local reflection of $\mathfrak o_\mathfrak p^n$ (`exists_stdStab_det_neg_one`). -/
theorem exists_so_mul_locStab (hQ : Q₀.Nondegenerate) (hn : 0 < n) (g : OAf QF) :
    ∃ m ∈ soAf QF, ∃ k ∈ locStab QF (stdLat F n), g = m * k := by
  classical
  choose ρ hρ hρdet using fun v => exists_stdStab_det_neg_one v Q₀ hQ hn
  let kf : (v : HeightOneSpectrum (𝓞 F)) → orthGroup QF (v.adicCompletion F) := fun v =>
    if ((g v : orthGroup QF _) : GL (Fin n) (v.adicCompletion F)).val.det = 1 then 1 else ρ v
  have hkf : ∀ v, kf v ∈ stdStab QF v := by
    intro v; simp only [kf]; split_ifs
    · exact (stdStab QF v).one_mem
    · exact hρ v
  let k : OAf QF := ⟨kf, Filter.Eventually.of_forall hkf⟩
  have hk : k ∈ locStab QF (stdLat F n) := (mem_locStab_intVec QF k).mpr hkf
  refine ⟨g * k⁻¹, fun v => ?_, k, hk, by rw [inv_mul_cancel_right]⟩
  have hQF := nondegenerate_map Q₀ hQ
  show (((g v * (kf v)⁻¹ : orthGroup QF _)) : GL (Fin n) (v.adicCompletion F)).val.det = 1
  simp only [kf]
  split_ifs with h
  · rw [inv_one, mul_one]; exact h
  · rcases det_eq_one_or_neg_one QF hQF (g v) with h' | h'
    · exact absurd h' h
    · have h1 := (soSub QF (v.adicCompletion F)).mul_mem (show g v * (ρ v)⁻¹ ∈ soSub QF _ from by
        rw [mem_soSub, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, det_mul, h']
        have hi := congrArg Matrix.det
          (Units.inv_mul ((ρ v : orthGroup QF (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)))
        rw [det_mul, hρdet v, det_one] at hi
        linear_combination hi) (soSub QF _).one_mem
      rw [mul_one] at h1
      exact h1

theorem det_diagF (Q : QuadForm F n) (γ : orthGroup Q F) (v : HeightOneSpectrum (𝓞 F)) :
    (((diagF Q γ) v : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)).val.det =
      algebraMap F (v.adicCompletion F) (γ : GL (Fin n) F).val.det := by
  show (((orthMap Q (v.adicCompletion F) γ : orthGroup Q (v.adicCompletion F)) :
    GL (Fin n) (v.adicCompletion F))).val.det = _
  rw [orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- **$[O(V)(F) : SO(V)(F)] = 2$**, inside $O(V)(\mathbb A_f)$ (a rational reflection,
`exists_orthGroup_det_neg_one`). -/
theorem index_soAf_ratPoints (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    ((soAf QF).subgroupOf (ratPoints QF)).index = 2 := by
  have hQF := nondegenerate_map Q₀ hQ
  obtain ⟨ρ, hρ⟩ := exists_orthGroup_det_neg_one QF hQF hn
  obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have hmem : ∀ γ : orthGroup QF F, diagF QF γ ∈ soAf QF ↔ (γ : GL (Fin n) F).val.det = 1 := by
    intro γ
    constructor
    · intro h
      have := h v₀
      rw [det_diagF] at this
      exact (algebraMap F (v₀.adicCompletion F)).injective (by rw [this, map_one])
    · intro h v
      rw [det_diagF, h, map_one]
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨diagF QF ρ, ⟨ρ, rfl⟩⟩, fun b => ?_⟩
  obtain ⟨β, hβ⟩ := b.2
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rw [← hβ, ← map_mul, hmem, hmem, Subgroup.coe_mul, Units.val_mul, det_mul, hρ]
  have h1 : (1 : F) ≠ -1 := by
    intro h; have : (2 : F) = 0 := by linear_combination h
    exact two_ne_zero this
  rcases det_eq_one_or_neg_one QF hQF β with h | h <;> simp [h, h1.symm]

/-- **The $SO$-mass is twice the $O$-mass** (for $L = \mathcal O_F^n$, $n \ge 1$, $Q_0$ nondegenerate):
$$\sum_{\Gamma^0\alpha K^0}\frac{1}{|\Gamma^0\cap\alpha K^0\alpha^{-1}|} = 2\,\mathrm{Mass}(L),\qquad
  \Gamma^0 = SO(V)(F),\ K^0 = SO(\hat L) \text{ inside } SO(V)(\mathbb A_f).$$
(Equivalently: each $O$-class splits into two proper classes, or is one proper class with an improper automorphism.)
The integrality and definiteness hypotheses give the finiteness needed. -/
@[kb "conwaysloane1988" "§2 (proper vs improper classes) [unverified]"]
theorem mass_SO_eq_two_mul_mass (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) :
    dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF (stdLat F n)).subgroupOf (soAf QF)) =
      2 * mass QF (stdLat F n) := by
  have hidx := index_soAf_ratPoints Q₀ hQ hn
  have : ((soAf QF).subgroupOf (ratPoints QF)).FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  have := finite_orbits hpd (stdLat F n) hLi
  rw [dcMass_normal (ratPoints QF) (locStab QF (stdLat F n)) (soAf QF)
    (exists_so_mul_locStab Q₀ hQ hn) (finite_stabilizer hpd (stdLat F n) hLi), hidx,
    mass_eq_dcMass]
  norm_num

/-- **The mass is a ratio of volumes, independent of choices:** for any compact open $K' \le O(\hat L)$ of finite
index (e.g. a principal congruence subgroup) and any left Haar measure $\mu$ on the commensurability class of
$O(\hat L)$ (`idxVol`),
$$\mathrm{Mass}(L)\cdot\mu(O(\hat L)) = \mu(K')\cdot\mathrm{dcMass}(O(V)(F), K') =: \mathrm{vol}(O(V)(F)\backslash O(V)(\mathbb A_f)).$$ -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem mass_mul_vol_eq {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    (K₀ : Subgroup (OAf Q)) (c : ℝ) (K' : Subgroup (OAf Q)) (hle : K' ≤ locStab Q L)
    (hK : (locStab Q L).Commensurable K₀) (hK' : K'.Commensurable K₀) :
    mass Q L * idxVol K₀ c (locStab Q L) = idxVol K₀ c K' * dcMass (ratPoints Q) K' := by
  have := finite_orbits hQ L hLi
  have hfin : K'.relIndex (locStab Q L) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans hK'.1.relIndex_ne_zero hK.2.relIndex_ne_zero
  rw [dcMass_of_le (ratPoints Q) hle hfin (finite_stabilizer hQ L hLi), idxVol_of_le K₀ c hle hK hK',
    mass_eq_dcMass]
  ring

end SO

/-! ### The Tamagawa measure and the mass formula -/

section Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The archimedean volume** $\mathrm{vol}(SO(V_\sigma))$ of a positive definite real quadratic space of dimension
$n$ with Gram matrix $A$ ($A = H/2$, $Q(x) = x^{\mathsf T}Ax$), $\det A = d$, for the gauge form $dX/dQ$ in the
coefficient coordinates of `repCountForm`:
$$\mathrm{vol}(SO(V_\sigma)) = \frac12\cdot 2^{-n(n-1)/2}\cdot d^{-(n+1)/2}\prod_{j=1}^{n}\frac{\pi^{j/2}}{\Gamma(j/2)}.$$
*Proved (`ArchVol.archVolSO_eq_volume`):* for positive definite $Q$ and $n \ge 1$ this closed form equals
$\mathrm{vol}(SO(Q), dX/dS)$, defined as Siegel's limit (`ArchVol.archVolSOLim`). The factors: $\mathrm{vol}(O_n(\mathbb R)) =
\prod_{j=1}^n\pi^{j/2}/\Gamma(j/2)$ for $dX/dS$ at $S = I$ (Siegel 1935; Kitaoka 1993, §6.8 [unverified]; `ArchVol.lintegral_gram`);
$d^{-(n+1)/2}$ from $S \mapsto P^{\mathsf T}SP$; $2^{-n(n-1)/2}$ converts the Gram coordinates $a_{ij}$ to the coefficients
$c_{ij} = 2a_{ij}$ ($i < j$); $\tfrac12 = 1/[O_n(\mathbb R) : SO_n(\mathbb R)]$ ($n \ge 1$; for $n = 0$ the value is $\mathrm{vol}(O_0)/2$). Indices: the product
runs over $j = 0, \dots, n-1$ with $(j+1)/2$. -/
@[kb "siegel1935" "§? (volume of O_n(R)) [unverified]"]
def archVolSO (n : ℕ) (d : ℝ) : ℝ :=
  (1 / 2) * ((2 : ℝ) ^ (n * (n - 1) / 2))⁻¹ * d ^ (-((n : ℝ) + 1) / 2) *
    ∏ j ∈ Finset.range n, Real.pi ^ (((j : ℝ) + 1) / 2) / Real.Gamma (((j : ℝ) + 1) / 2)

/-- $\det A_\sigma = \sigma(\det(H/2))$ at a real embedding $\sigma$ (taken in absolute value; for totally positive
definite $Q$ it is positive). -/
def detGram (σ : F →ₐ[ℚ] ℂ) : ℝ := ‖σ (algebraMap (𝓞 F) F Q₀.hessian.det / 2 ^ n)‖

/-- **The Tamagawa measure of $K_{SO} = SO(V)(F\otimes\mathbb R)\times SO(\hat L)$** ($L = \mathcal O_F^n$):
$$\mu_{\mathrm{Tam}}(K_{SO}) = |d_F|^{-n(n-1)/4}\prod_{\sigma : F \to \mathbb R}\mathrm{vol}(SO(V_\sigma))\prod_{\mathfrak p}\alpha_\mathfrak p(L, L),$$
the product of the local gauge-form measures (`archVolSO`; $\mathrm{vol}(SO(L_\mathfrak p)) = \alpha_\mathfrak p$, `volSO_eq`) with
Weil's normalization $|d_F|^{-\dim/2}$, $\dim SO_n = n(n-1)/2$ (Weil 1982, §2.3 [unverified]). No convergence factors are
needed for $n \ge 3$ ($SO$ semisimple): the product converges absolutely (`hasProd_siegelDensity_odd`; for $n = 2$ it
would need $L(1,\chi)$). The embeddings are all $F \to \mathbb C$, which for totally positive definite $Q$ are real.

*Warning: meaningful only for rank $n \ge 3$.* For $n = 2$ the factors $\alpha_\mathfrak p = 1 - \chi(\mathfrak p)/N\mathfrak p$
are not unconditionally multipliable, so `tprod` returns its junk value $1$ and `tamagawaK` drops every finite factor; a
rank-2 Tamagawa measure needs the regularized product `RegProd.regProd χ (-1) α` ($\lambda_\mathfrak p = L_\mathfrak p(1,\chi)$). For $n = 1$ the product is finite-support and fine. -/
@[kb "weil1982" "§2.3 (Tamagawa measure) [unverified]"]
def tamagawaK : ℝ :=
  (|(discr F : ℝ)|) ^ (-((n : ℝ) * (n - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
    ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀

/-- **$\tau(SO(V))$ for totally definite $V$**: $\mu_{\mathrm{Tam}}(K_{SO})\cdot\sum_\alpha 1/|\Gamma_\alpha|$. Since
$SO(V)(F\otimes\mathbb R)$ is compact, $SO(V)(F)\backslash SO(V)(\mathbb A) = \bigsqcup_\alpha \Gamma_\alpha\backslash(SO(V)(F\otimes\mathbb R)\times
\alpha K_f)$ with $\Gamma_\alpha = SO(V)(F)\cap\alpha K_f\alpha^{-1}$ finite, so this is the Tamagawa volume of the quotient (the
unfolding; Weil 1982, §2.4, p. 23 for $\tau(G) = \mathrm{vol}(G_{\mathbb A}/G_k)$ and Lemma 2.4.2, p. 26 for the unfolding).
*Proved*: this definition equals the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for a genuine Haar measure
$\mu_{\mathbb A} = c_F\,\mu_\infty\times\mu_f$ (`Measure.tauSO_eq_covolume`, `Tamagawa/Measure/AdelicSO.lean`).
*Erratum:* an earlier version cited Weil 1982 "§3.5" here; §3.5 of Weil's book is the symplectic group. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); Lemma 2.4.2, p. 26 (unfolding)"]
def tauSO : ℝ :=
  tamagawaK Q₀ * dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF (stdLat F n)).subgroupOf (soAf QF))

/-- **Cited input: the Tamagawa number of $SO(V)$ is $2$** (Weil 1982, Thm 4.5.? [unverified]; Siegel; for $n \ge 2$).
It is a *hypothesis*, not an axiom.

*Meaning.* `tauSO` is defined as $\mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{mass}_{SO}$, and this is now a
**theorem** about a genuine measure: `Measure.tauSO_eq_covolume` (`Tamagawa/Measure/AdelicSO.lean`) proves
$$\texttt{tauSO}\ Q_0 = \mathrm{covol}\bigl(SO(V)(F)\backslash SO(V)(\mathbb A),\ \mu_{\mathbb A}\bigr),$$
with $SO(V)(F)$ embedded diagonally in $SO(V)(\mathbb A) = \prod_\sigma SO(V_\sigma)(\mathbb R)\times SO(V)(\mathbb A_f)$ and
$\mu_{\mathbb A} = |d_F|^{-n(n-1)/4}\,\mu_\infty\times\mu_f$ a Haar measure ($\mu_\infty = \prod_\sigma\mu_\sigma$ with
$\mu_\sigma(SO(V_\sigma)) = $ `archVolSO`; $\mu_f$ the Haar measure on the restricted product normalized by
$\mu_f(SO(\hat L)) = \prod'_v\mu_v(SO(L_v)) = \prod'_\mathfrak p\alpha_\mathfrak p(L,L)$). Hence (`Measure.tamagawaNumberTwo_iff_covolume`)
this hypothesis says exactly that the Tamagawa covolume is $2$ (Weil 1982, §2.4, p. 23: $\tau(G) = \mathrm{vol}(G_{\mathbb A}/G_k)$),
and it is no longer *definitionally* the mass formula. Remaining fidelity gaps: the
product characterization of $\mu_f$ on boxes and the identification of the local measures with gauge-form (Leray)
measures; the local masses themselves are proved ($\mathrm{vol}(SO(L_\mathfrak p)) = \alpha_\mathfrak p(L,L)$, the archimedean
volume). The mass formula still follows from this hypothesis by a short computation; what has changed is that the
hypothesis is now an independent statement about $\mathrm{vol}(SO(V)(F)\backslash SO(V)(\mathbb A))$. -/
@[kb "weil1982" "Ch. IV (τ(SO) = 2) [unverified]"]
def TamagawaNumberTwo : Prop := tauSO Q₀ = 2

/-- **The Smith–Minkowski–Siegel mass formula, conditional on $\tau(SO) = 2$:** for $Q_0$ over $\mathcal O_F$ nondegenerate,
$n \ge 1$, $Q_0 \otimes F$ totally positive definite and $L = \mathcal O_F^n$,
$$\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{1}{|O(M)|} = \frac{1}{\mu_{\mathrm{Tam}}(K_{SO})}
  = \frac{|d_F|^{n(n-1)/4}}{\prod_\sigma\mathrm{vol}(SO(V_\sigma))\cdot\prod_\mathfrak p\alpha_\mathfrak p(L,L)}.$$
*Proof:* $\tau(SO) = \mu(K_{SO})\cdot\mathrm{mass}_{SO} = \mu(K_{SO})\cdot 2\,\mathrm{Mass}(L)$ (`mass_SO_eq_two_mul_mass`). The factor
$2 = \tau(SO)$ cancels the factor $2 = [O:SO]$; in Siegel's normalization this is the classical
$\mathrm{Mass}(L) = 2\prod_p\alpha_p(L,L)^{-1}\cdot\prod_{j=1}^n\pi^{-j/2}\Gamma(j/2)\cdot\det(L)^{(n+1)/2}$ over $\mathbb Q$ (Kitaoka 1993,
Thm 6.8.1 [unverified]; Conway–Sloane 1988, (2)). -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula) [unverified]"]
theorem massFormula (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) (hτ : TamagawaNumberTwo Q₀) :
    mass QF (stdLat F n) = (tamagawaK Q₀)⁻¹ := by
  unfold TamagawaNumberTwo tauSO at hτ
  rw [mass_SO_eq_two_mul_mass Q₀ hQ hn hpd hLi] at hτ
  have h1 : tamagawaK Q₀ * mass QF (stdLat F n) = 1 := by linarith
  exact (eq_inv_of_mul_eq_one_right h1)

/-- **The mass formula, expanded.** -/
theorem massFormula' (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) (hτ : TamagawaNumberTwo Q₀) :
    mass QF (stdLat F n) = (|(discr F : ℝ)|) ^ ((n : ℝ) * (n - 1) / 4) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ))⁻¹ *
      (∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ := by
  rw [massFormula Q₀ hQ hn hpd hLi hτ, tamagawaK, mul_inv, mul_inv, ← Real.rpow_neg (abs_nonneg _), neg_neg]

/-! ### Convergence and the explicit form for odd $n$ -/

/-- **The bad primes** $\mathfrak p \mid 2\det H_{Q_0}$: a finite set (`finite_badPrimes`). -/
def badPrimes : Set (HeightOneSpectrum (𝓞 F)) := {v | 2 * Q₀.hessian.det ∈ v.asIdeal}

theorem finite_badPrimes (hQ : Q₀.Nondegenerate) : (badPrimes Q₀).Finite := by
  have h0 : (2 * Q₀.hessian.det : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hQ
  refine (Ideal.finite_factors (I := Ideal.span {2 * Q₀.hessian.det})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv

/-- The generic local factor $\lambda_\mathfrak p^{-1} = \prod_{i=1}^{m}(1 - N\mathfrak p^{-2i})$ for $n = 2m+1$
(index shift: $i = 0, \dots, m-1$ with exponent $2(i+1)$). -/
def genericOdd (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ∏ i ∈ Finset.range m, (1 - (NFEuler.normP v : ℝ) ^ (-((2 * (i + 1) : ℕ) : ℝ)))

theorem genericOdd_pos (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) : 0 < genericOdd m v := by
  refine Finset.prod_pos fun i _ => ?_
  have h2 := NFEuler.two_le_normP v
  have : (NFEuler.normP v : ℝ) ^ (-((2 * (i + 1) : ℕ) : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < NFEuler.normP v))
      (by have : (0 : ℝ) < ((2 * (i + 1) : ℕ) : ℝ) := by positivity
          linarith)
  linarith

/-- At a good prime, $\alpha_\mathfrak p$ is the generic factor (odd $n = 2m+1$, `volSO_good_odd`). -/
theorem siegelDensity_good_odd (m : ℕ) (Q₀ : QuadForm (𝓞 F) (2 * m + 1)) (hQ : Q₀.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badPrimes Q₀) :
    LocalDensity.NF.siegelDensity v Q₀ Q₀ = genericOdd m v := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hd : Q₀.hessian.det ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  rw [← volSO_eq v Q₀ hQ (by omega), volSO_good_odd v m Q₀ hQ h2 hd, genericOdd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]

/-- **Convergence of $\prod_\mathfrak p\alpha_\mathfrak p$ and its value, odd $n = 2m + 1$:**
$$\prod_{\mathfrak p}\alpha_\mathfrak p(L, L) = \prod_{\mathfrak p \mid 2\det H}\frac{\alpha_\mathfrak p}{\lambda_\mathfrak p^{-1}}
  \cdot\prod_{i=1}^{m}\zeta_F(2i)^{-1},\qquad \lambda_\mathfrak p = \prod_{i=1}^m(1 - N\mathfrak p^{-2i})^{-1}$$
(an unconditionally convergent product; the convergence factors $\lambda_\mathfrak p$ are the Euler factors of
$\zeta_F(2)\cdots\zeta_F(2m)$, `NFEuler.hasProd_one_sub_rpow`). Valid for every $m$; for $m = 0$ ($n = 1$) both products are
trivial. -/
@[kb "kitaoka1993" "§5.6, §6.8 [unverified]"]
theorem hasProd_siegelDensity_odd (m : ℕ) (Q₀ : QuadForm (𝓞 F) (2 * m + 1)) (hQ : Q₀.Nondegenerate) :
    HasProd (fun v => LocalDensity.NF.siegelDensity v Q₀ Q₀)
      ((∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericOdd m v) *
        ∏ i ∈ Finset.range m, (NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ))⁻¹) := by
  classical
  have hg : HasProd (genericOdd m) (∏ i ∈ Finset.range m, (NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ))⁻¹) :=
    hasProd_prod fun i _ => NFEuler.hasProd_one_sub_rpow (by
      have : (2 : ℝ) ≤ ((2 * (i + 1) : ℕ) : ℝ) := by
        have : 2 ≤ 2 * (i + 1) := by omega
        exact_mod_cast this
      linarith)
  have hh : HasProd (fun v => LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericOdd m v)
      (∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericOdd m v) := by
    refine hasProd_prod_of_ne_finset_one fun v hv => ?_
    have hv' : v ∉ badPrimes Q₀ := by simpa using hv
    rw [siegelDensity_good_odd m Q₀ hQ v hv', div_self (genericOdd_pos m v).ne']
  convert hh.mul hg using 1
  funext v
  rw [div_mul_cancel₀ _ (genericOdd_pos m v).ne']

/-- **The mass formula, explicit form for odd $n = 2m+1$** (conditional on $\tau(SO) = 2$):
$$\mathrm{Mass}(\mathcal O_F^n) = |d_F|^{n(n-1)/4}\Big(\prod_\sigma\mathrm{vol}(SO(V_\sigma))\Big)^{-1}
  \Big(\prod_{\mathfrak p\mid 2\det H}\alpha_\mathfrak p\lambda_\mathfrak p\Big)^{-1}\prod_{i=1}^m\zeta_F(2i).$$
The only non-explicit factors are the finitely many bad local densities $\alpha_\mathfrak p$, $\mathfrak p \mid 2\det H$ (closed forms
at odd bad primes and dyadic primes are not given here). -/
@[kb "kitaoka1993" "Thm 6.8.1 [unverified]"]
theorem massFormula_odd (m : ℕ) (Q₀ : QuadForm (𝓞 F) (2 * m + 1)) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (2 * m + 1)).1) (hτ : TamagawaNumberTwo Q₀) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (2 * m + 1)) =
      (|(discr F : ℝ)|) ^ (((2 * m + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) - 1) / 4) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (2 * m + 1) (detGram Q₀ σ))⁻¹ *
      (∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericOdd m v)⁻¹ *
      ∏ i ∈ Finset.range m, NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ) := by
  rw [massFormula' Q₀ hQ (by omega) hpd hLi hτ, (hasProd_siegelDensity_odd m Q₀ hQ).tprod_eq, mul_inv]
  simp only [Finset.prod_inv_distrib, inv_inv]
  ring

/-! ### The explicit form for even $n$ -/

theorem abs_chiP_le (v : HeightOneSpectrum (𝓞 F)) : |chiP v Q₀| ≤ 1 := by
  unfold chiP
  split_ifs
  · simp
  · unfold LocalDensity.DVR.chiDisc
    set a := ((-1 : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ^ (n / 2) *
      LocalDensity.DVR.resGramDet (LocalDensity.NF.Qp v Q₀))
    by_cases ha : a = 0
    · rw [(quadraticChar_eq_zero_iff).mpr ha]; simp
    · rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> simp

/-- The generic local factor $(1 - \chi(\mathfrak p)N\mathfrak p^{-m})\prod_{i=1}^{m-1}(1 - N\mathfrak p^{-2i})$ for $n = 2m$. -/
def genericEven (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (1 - chiP v Q₀ * (NFEuler.normP v : ℝ) ^ (-(m : ℝ))) * genericOdd (m - 1) v

theorem one_sub_chiP_eq (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    1 - chiP v Q₀ * (NFEuler.normP v : ℝ) ^ (-(m : ℝ)) = (NFEuler.lFactor (chiP · Q₀) m v)⁻¹ := by
  rw [NFEuler.lFactor, inv_inv]

theorem genericEven_pos (m : ℕ) (hm : 2 ≤ m) (v : HeightOneSpectrum (𝓞 F)) : 0 < genericEven Q₀ m v := by
  refine mul_pos ?_ (genericOdd_pos (m - 1) v)
  rw [one_sub_chiP_eq]
  exact inv_pos.mpr (NFEuler.lFactor_pos (fun v => abs_chiP_le Q₀ v) (by exact_mod_cast hm) v)

/-- At a good prime, $\alpha_\mathfrak p$ is the generic factor (even $n = 2m$, `volSO_good_even`). -/
theorem siegelDensity_good_even (m : ℕ) (hm : 1 ≤ m) (Q₀ : QuadForm (𝓞 F) (2 * m)) (hQ : Q₀.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badPrimes Q₀) :
    LocalDensity.NF.siegelDensity v Q₀ Q₀ = genericEven Q₀ m v := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hd : Q₀.hessian.det ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  rw [← volSO_eq v Q₀ hQ (by omega), volSO_good_even v m hm Q₀ hQ h2 hd, genericEven, genericOdd]
  congr 1
  · rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]

/-- **Convergence of $\prod_\mathfrak p\alpha_\mathfrak p$ and its value, even $n = 2m$, $m \ge 2$:**
$$\prod_{\mathfrak p}\alpha_\mathfrak p(L, L) = \prod_{\mathfrak p \mid 2\det H}\frac{\alpha_\mathfrak p}{\lambda_\mathfrak p^{-1}}
  \cdot L_F(m, \chi)^{-1}\prod_{i=1}^{m-1}\zeta_F(2i)^{-1},$$
$\chi$ = `chiP` (the quadratic character of the discriminant $(-1)^m\det(H/2)$; $\chi(\mathfrak p) = 0$ at bad $\mathfrak p$, where the
correction factor absorbs it), $L_F(m, \chi)$ = `NFEuler.LFunctionNF`. The convergence factors are the Euler factors of
$L_F(m,\chi)\,\zeta_F(2)\cdots\zeta_F(2m-2)$. -/
@[kb "kitaoka1993" "§5.6, §6.8 [unverified]"]
theorem hasProd_siegelDensity_even (m : ℕ) (hm : 2 ≤ m) (Q₀ : QuadForm (𝓞 F) (2 * m))
    (hQ : Q₀.Nondegenerate) :
    HasProd (fun v => LocalDensity.NF.siegelDensity v Q₀ Q₀)
      ((∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericEven Q₀ m v) *
        ((NFEuler.LFunctionNF (chiP · Q₀) m)⁻¹ *
          ∏ i ∈ Finset.range (m - 1), (NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ))⁻¹)) := by
  classical
  have hχ : ∀ v, |chiP v Q₀| ≤ 1 := fun v => abs_chiP_le Q₀ v
  have hs : (1 : ℝ) < m := by exact_mod_cast hm
  have hL := NFEuler.hasProd_LFunctionNF hχ hs
  have hLinv : HasProd (fun v => 1 - chiP v Q₀ * (NFEuler.normP v : ℝ) ^ (-(m : ℝ)))
      (NFEuler.LFunctionNF (chiP · Q₀) m)⁻¹ := by
    have := hL.inv₀ (NFEuler.LFunctionNF_pos hχ hs).ne'
    convert this using 1
    funext v
    rw [one_sub_chiP_eq]
  have hg : HasProd (genericOdd (m - 1))
      (∏ i ∈ Finset.range (m - 1), (NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ))⁻¹) :=
    hasProd_prod fun i _ => NFEuler.hasProd_one_sub_rpow (by
      have : (2 : ℝ) ≤ ((2 * (i + 1) : ℕ) : ℝ) := by
        have : 2 ≤ 2 * (i + 1) := by omega
        exact_mod_cast this
      linarith)
  have hge : HasProd (genericEven Q₀ m) ((NFEuler.LFunctionNF (chiP · Q₀) m)⁻¹ *
      ∏ i ∈ Finset.range (m - 1), (NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ))⁻¹) := hLinv.mul hg
  have hh : HasProd (fun v => LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericEven Q₀ m v)
      (∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericEven Q₀ m v) := by
    refine hasProd_prod_of_ne_finset_one fun v hv => ?_
    have hv' : v ∉ badPrimes Q₀ := by simpa using hv
    rw [siegelDensity_good_even m (by omega) Q₀ hQ v hv', div_self (genericEven_pos Q₀ m hm v).ne']
  convert hh.mul hge using 1
  funext v
  rw [div_mul_cancel₀ _ (genericEven_pos Q₀ m hm v).ne']

/-- **The mass formula, explicit form for even $n = 2m$, $m \ge 2$** (conditional on $\tau(SO) = 2$):
$$\mathrm{Mass}(\mathcal O_F^n) = |d_F|^{n(n-1)/4}\Big(\prod_\sigma\mathrm{vol}(SO(V_\sigma))\Big)^{-1}
  \Big(\prod_{\mathfrak p\mid 2\det H}\alpha_\mathfrak p\lambda_\mathfrak p\Big)^{-1} L_F(m,\chi)\prod_{i=1}^{m-1}\zeta_F(2i).$$ -/
@[kb "kitaoka1993" "Thm 6.8.1 [unverified]"]
theorem massFormula_even (m : ℕ) (hm : 2 ≤ m) (Q₀ : QuadForm (𝓞 F) (2 * m)) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (2 * m)).1) (hτ : TamagawaNumberTwo Q₀) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (2 * m)) =
      (|(discr F : ℝ)|) ^ (((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) - 1) / 4) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (2 * m) (detGram Q₀ σ))⁻¹ *
      (∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericEven Q₀ m v)⁻¹ *
      NFEuler.LFunctionNF (chiP · Q₀) m *
      ∏ i ∈ Finset.range (m - 1), NFEuler.dedekindZetaR F ((2 * (i + 1) : ℕ) : ℝ) := by
  rw [massFormula' Q₀ hQ (by omega) hpd hLi hτ, (hasProd_siegelDensity_even m hm Q₀ hQ).tprod_eq,
    mul_inv, mul_inv]
  simp only [Finset.prod_inv_distrib, inv_inv]
  ring

end Tamagawa

end QuadFormsKB.Tamagawa
