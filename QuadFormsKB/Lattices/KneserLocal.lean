/-
# Kneser's local lemma: lattices agreeing away from $\pi$ are joined by $\pi$-neighbours

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`Lattices/Local.lean`, `Lattices/Genus.lean`),
$\pi$-neighbours `IsNbrL` (`Lattices/NeighborGenus.lean`), the named input `LocalNeighborChain F` (`Lattices/Kneser.lean`).

**Proves** `localNeighborChain : LocalNeighborChain F`, hence Kneser's neighbour theorem `kneser_reach_uncond`
unconditionally (Kneser 1957, §2 [unverified]).

**Proof** (Kneser's induction, done globally). Write $B(x, y) = x^{\mathsf T}Hy$, $\mathcal O = \mathcal O_F$, $v = (\pi)$.
Call $N$ *weakly unimodular at $v$* (`WeakUnimod`) if every $z$ with $B(N, z) \subseteq \mathcal O$ and $z \in N_w$ for all
$w \ne v$ lies in $N$; for a lattice this follows from unimodularity at $v$ (`IsUnimodularAt`).
1. *The step* (`isNbrL_nbr`). Let $N$ be integral and weakly unimodular at $v$, $x \notin N$ with $\pi x \in N$, $Q(x) \in \mathcal O$
   and $x \in N_w$ for $w \ne v$. Put $N_x = \{y \in N : B(y, x) \in \mathcal O\}$ and $N' = N_x + \mathcal O x$ (`nbr`). The map
   $y \mapsto B(y, \pi x) \bmod \pi$, $N \to \mathcal O/\pi$, is onto (else $B(N, x) \subseteq \mathcal O$, so $x \in N$), with kernel
   $N_x = N \cap N'$; and $a \mapsto a x$ induces $\mathcal O/\pi \cong N'/N_x$ ($a x \in N \Rightarrow \pi \mid a$). So
   $[N : N \cap N'] = [N' : N \cap N'] = N\pi$, and $N'$ is a $\pi$-neighbour of $N$. Moreover $N'$ is again integral, weakly
   unimodular (`weakUnimod_nbr`: correct $z$ by a multiple of $x$) and agrees with $N$ away from $v$ (`loc_nbr`).
2. *The induction* (`chain_aux`): for $M$ integral, weakly unimodular, agreeing with $N$ away from $v$: if $M \not\subseteq N$, pick
   $y \in M \setminus N$, the least $k$ with $\pi^k y \in N$, and $x = \pi^{k-1}y$; then $N' \cap M \supsetneq N \cap M$ (Noetherian
   induction in $M$). If $M \subseteq N$, weak unimodularity of $M$ gives $N \subseteq M$.
3. *Local input* (`isUnimodularAt_of_sameGenus`): unimodularity at $v$ is a genus invariant. The global definition
   (`IsUnimodularAt`, quantifying over $x \in F^n$) is converted to the local one ($L_v^\# = L_v$, `locDual_le`) by
   approximation and the Chinese remainder theorem.

The hypothesis $\pi \nmid 2$ of `LocalNeighborChain` is not needed.
-/
import QuadFormsKB.Lattices.Kneser
import QuadFormsKB.Lattices.Finite
import QuadFormsKB.Lattices.SATernaryAway
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.HilbertModular.GenusTheta
import QuadFormsKB.LocalDensity.NFLocalGeneral

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

noncomputable section

namespace QuadFormsKB.Lattices.KneserLocal

open Nbr

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)


/-! ### Elementary facts -/

theorem algebraMap_injective : Function.Injective (algebraMap (𝓞 F) F) :=
  IsFractionRing.injective (𝓞 F) F

theorem bil_osmul_left (a : 𝓞 F) (y z : Fin n → F) :
    bil Q (a • y) z = algebraMap (𝓞 F) F a * bil Q y z := by
  rw [← algebraMap_smul F a y, bil_smul_left]

theorem bil_osmul_right (a : 𝓞 F) (y z : Fin n → F) :
    bil Q y (a • z) = algebraMap (𝓞 F) F a * bil Q y z := by
  rw [← algebraMap_smul F a z, bil_smul_right]

theorem bil_add_left (y y' z : Fin n → F) : bil Q (y + y') z = bil Q y z + bil Q y' z := by
  simp [bil, add_dotProduct]

theorem bil_add_right (y z z' : Fin n → F) : bil Q y (z + z') = bil Q y z + bil Q y z' := by
  simp [bil, mulVec_add, dotProduct_add]

theorem bil_sub_left (y y' z : Fin n → F) : bil Q (y - y') z = bil Q y z - bil Q y' z := by
  simp [bil, sub_dotProduct]

theorem bil_sub_right (y z z' : Fin n → F) : bil Q y (z - z') = bil Q y z - bil Q y z' := by
  simp [bil, mulVec_sub, dotProduct_sub]

theorem evalIn_add (y z : Fin n → F) :
    Q.evalIn F (y + z) = Q.evalIn F y + Q.evalIn F z + bil Q y z := by
  have h := QuadForm.polar_eq_hessian F Q y z
  have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  rw [e] at h
  rw [bil, ← h]; ring

theorem evalIn_osmul (a : 𝓞 F) (y : Fin n → F) :
    Q.evalIn F (a • y) = (algebraMap (𝓞 F) F a) ^ 2 * Q.evalIn F y := by
  rw [← algebraMap_smul F a y, evalIn_smul']

/-- If $\pi b \in \mathcal O$ with $\pi b = \pi c$... : cancel $\pi$ in $F$. -/
theorem mem_of_pi_mul {π : 𝓞 F} (hπ : π ≠ 0) {b : F} {c : 𝓞 F}
    (h : algebraMap (𝓞 F) F π * b = algebraMap (𝓞 F) F (π * c)) : b = algebraMap (𝓞 F) F c := by
  have hp : algebraMap (𝓞 F) F π ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ algebraMap_injective]
  rw [map_mul] at h
  exact mul_left_cancel₀ hp h

/-- $\pi$ is a unit at every place $w \ne (\pi)$. -/
theorem valued_pi_eq_one {π : 𝓞 F} (hπ : Prime π) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ hosOf hπ) :
    Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) π) = 1 := by
  rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hw
  have hle : Ideal.span {π} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have := (isMaximal_span hπ).eq_of_le w.isPrime.ne_top hle
  exact HeightOneSpectrum.ext this.symm

/-- Division by $\pi$ at a place $w \ne (\pi)$. -/
theorem locVec_mem_of_smul {π : 𝓞 F} (hπ : Prime π) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ hosOf hπ)
    {N : Submodule (𝓞 F) (Fin n → F)} {y : Fin n → F} (h : locVec w (π • y) ∈ loc w N) :
    locVec w y ∈ loc w N := by
  have h1 := valued_pi_eq_one hπ hw
  set c : w.adicCompletion F := algebraMap (𝓞 F) (w.adicCompletion F) π
  have hc0 : c ≠ 0 := by intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hci : Valued.v c⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
  rw [locVec_smul_int] at h
  have := (loc w N).smul_mem (toO w c⁻¹ hci) h
  rw [smul_smul] at this
  convert this using 1
  funext i
  rw [smul_apply_coe]
  change locVec w y i = (c⁻¹ * c) * locVec w y i
  rw [inv_mul_cancel₀ hc0, one_mul]

/-- $a x \in N$, $x \notin N$, $\pi x \in N$ force $\pi \mid a$. -/
theorem dvd_of_smul_mem {π : 𝓞 F} (hπ : Prime π) {N : Submodule (𝓞 F) (Fin n → F)} {x : Fin n → F}
    (hxN : x ∉ N) (hx : π • x ∈ N) {a : 𝓞 F} (ha : a • x ∈ N) : π ∣ a := by
  by_contra hna
  have hnot : a ∉ Ideal.span {π} := by rwa [Ideal.mem_span_singleton]
  obtain ⟨b, i, hi, hbi⟩ := (isMaximal_span hπ).exists_inv hnot
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  apply hxN
  have : x = b • (a • x) + c • (π • x) := by
    rw [smul_smul, smul_smul, ← add_smul, hbi, one_smul]
  rw [this]
  exact N.add_mem (N.smul_mem _ ha) (N.smul_mem _ hx)

/-- The index of the kernel of a surjective additive map. -/
theorem index_ker_of_surjective {A B : Type*} [AddGroup A] [AddGroup B] (f : A →+ B)
    (hf : Function.Surjective f) : f.ker.index = Nat.card B := by
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf]
  exact Nat.card_congr (Equiv.Set.univ B)

/-! ### Weak unimodularity -/

/-- **Weakly unimodular at $v$:** every $z$ with $B(N, z) \subseteq \mathcal O_F$ that lies in $N_w$ for every $w \ne v$ lies
in $N$. For a lattice, this follows from `IsUnimodularAt` (`weakUnimod_of_isUnimodularAt`). -/
def WeakUnimod (N : Submodule (𝓞 F) (Fin n → F)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ z : Fin n → F, (∀ y ∈ N, bil Q y z ∈ (algebraMap (𝓞 F) F).range) → (∀ w, w ≠ v → locVec w z ∈ loc w N) → z ∈ N

theorem weakUnimod_of_isUnimodularAt {N : Submodule (𝓞 F) (Fin n → F)} (hN : N.IsLattice F)
    {v : HeightOneSpectrum (𝓞 F)} (h : IsUnimodularAt Q N v) : WeakUnimod Q N v := by
  intro z hz hw
  rw [mem_iff_forall_loc hN]
  intro w
  by_cases hwv : w = v
  · subst hwv; exact h z hz
  · exact hw w hwv

/-! ### The neighbour $N' = N_x + \mathcal O x$ -/

/-- Hypotheses of the step. -/
structure StepHyp (Q : QuadForm F n) (N : Submodule (𝓞 F) (Fin n → F)) (x : Fin n → F) (π : 𝓞 F) : Prop where
  int : IsIntegral Q N
  pix : π • x ∈ N
  notMem : x ∉ N
  qx : Q.evalIn F x ∈ (algebraMap (𝓞 F) F).range

section Step

variable (N : Submodule (𝓞 F) (Fin n → F)) (x : Fin n → F)

/-- $N_x = \{y \in N : B(y, x) \in \mathcal O_F\}$. -/
def kerN : Submodule (𝓞 F) (Fin n → F) where
  carrier := {y | y ∈ N ∧ bil Q y x ∈ (algebraMap (𝓞 F) F).range}
  add_mem' {a b} ha hb := ⟨N.add_mem ha.1 hb.1, by rw [bil_add_left]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨N.zero_mem, ⟨0, by simp [bil]⟩⟩
  smul_mem' c a ha := ⟨N.smul_mem c ha.1, by
    rw [bil_osmul_left]; exact mul_mem (RingHom.mem_range.mpr ⟨c, rfl⟩) ha.2⟩

theorem mem_kerN {y : Fin n → F} : y ∈ kerN Q N x ↔ y ∈ N ∧ bil Q y x ∈ (algebraMap (𝓞 F) F).range := Iff.rfl

/-- **The neighbour** $N' = N_x + \mathcal O_F\,x$. -/
def nbr : Submodule (𝓞 F) (Fin n → F) := kerN Q N x ⊔ Submodule.span (𝓞 F) {x}

theorem mem_nbr {z : Fin n → F} : z ∈ nbr Q N x ↔ ∃ y ∈ kerN Q N x, ∃ a : 𝓞 F, y + a • x = z := by
  rw [nbr, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z', hz', rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz'
    exact ⟨y, hy, a, rfl⟩
  · rintro ⟨y, hy, a, rfl⟩
    exact ⟨y, hy, a • x, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, rfl⟩

theorem x_mem_nbr : x ∈ nbr Q N x := (mem_nbr Q N x).mpr ⟨0, (kerN Q N x).zero_mem, 1, by simp⟩

theorem kerN_le_nbr : kerN Q N x ≤ nbr Q N x := le_sup_left

variable {Q N x}
variable {π : 𝓞 F} (hπ : Prime π)

include hπ

theorem pix_mem_kerN (h : StepHyp Q N x π) : π • x ∈ kerN Q N x := by
  refine ⟨h.pix, ?_⟩
  rw [bil_osmul_left, bil_self]
  exact mul_mem (RingHom.mem_range.mpr ⟨π, rfl⟩) (mul_mem (RingHom.mem_range.mpr ⟨2, map_ofNat _ 2⟩) h.qx)

theorem mem_kerN_of_mem_nbr (h : StepHyp Q N x π) {y : Fin n → F} (hyN : y ∈ N) (hy : y ∈ nbr Q N x) :
    y ∈ kerN Q N x := by
  obtain ⟨y', hy', a, rfl⟩ := (mem_nbr Q N x).mp hy
  have hax : a • x ∈ N := by
    have := N.sub_mem hyN hy'.1
    rwa [add_sub_cancel_left] at this
  obtain ⟨d, rfl⟩ := dvd_of_smul_mem hπ h.notMem h.pix hax
  rw [mul_comm, mul_smul]
  exact (kerN Q N x).add_mem hy' ((kerN Q N x).smul_mem d (pix_mem_kerN hπ h))

/-- $B(y, \pi x) \in \mathcal O$ for $y \in N$. -/
theorem bil_pix_mem (h : StepHyp Q N x π) {y : Fin n → F} (hy : y ∈ N) : bil Q y (π • x) ∈ (algebraMap (𝓞 F) F).range :=
  bil_mem Q h.int hy h.pix

/-- The map $y \mapsto B(y, \pi x) \bmod \pi$, $N \to \mathcal O/\pi$. -/
def phi (h : StepHyp Q N x π) : N →+ Res π where
  toFun y := Ideal.Quotient.mk _ (bil_pix_mem hπ h y.2).choose
  map_zero' := by
    have h0 := (bil_pix_mem hπ h (N.zero_mem)).choose_spec
    have : (bil_pix_mem hπ h (N.zero_mem)).choose = 0 := by
      apply algebraMap_injective; rw [h0, map_zero]; simp [bil]
    simp only [ZeroMemClass.coe_zero]
    rw [this, map_zero]
  map_add' a b := by
    have ha := (bil_pix_mem hπ h a.2).choose_spec
    have hb := (bil_pix_mem hπ h b.2).choose_spec
    have hab := (bil_pix_mem hπ h (a + b).2).choose_spec
    have : (bil_pix_mem hπ h (a + b).2).choose =
        (bil_pix_mem hπ h a.2).choose + (bil_pix_mem hπ h b.2).choose := by
      apply algebraMap_injective
      rw [hab, map_add, ha, hb, Submodule.coe_add, bil_add_left]
    rw [this, map_add]

theorem phi_spec (h : StepHyp Q N x π) (y : N) :
    ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = bil Q y (π • x) ∧ phi hπ h y = Ideal.Quotient.mk _ c :=
  ⟨_, (bil_pix_mem hπ h y.2).choose_spec, rfl⟩

theorem phi_eq_zero_iff (h : StepHyp Q N x π) (y : N) : phi hπ h y = 0 ↔ (y : Fin n → F) ∈ kerN Q N x := by
  obtain ⟨c, hc, he⟩ := phi_spec hπ h y
  rw [he, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mem_kerN]
  simp only [y.2, true_and]
  rw [bil_osmul_right] at hc
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, (mem_of_pi_mul hπ.ne_zero hc.symm).symm⟩
  · rintro ⟨d, hd⟩
    refine ⟨d, algebraMap_injective ?_⟩
    rw [hc, ← hd, map_mul]

theorem phi_smul (h : StepHyp Q N x π) (a : 𝓞 F) (y : N) :
    phi hπ h (a • y) = Ideal.Quotient.mk _ a * phi hπ h y := by
  obtain ⟨c, hc, he⟩ := phi_spec hπ h y
  obtain ⟨c', hc', he'⟩ := phi_spec hπ h (a • y)
  rw [he, he', ← map_mul]
  congr 1
  apply algebraMap_injective
  rw [hc', map_mul, hc, Submodule.coe_smul, bil_osmul_left]

/-- There is $y_0 \in N$ with $B(y_0, \pi x) \not\equiv 0 \pmod \pi$ (weak unimodularity). -/
theorem exists_phi_ne_zero (h : StepHyp Q N x π) {v : HeightOneSpectrum (𝓞 F)} (hP : WeakUnimod Q N v)
    (hxloc : ∀ w, w ≠ v → locVec w x ∈ loc w N) : ∃ y : N, phi hπ h y ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h.notMem
  refine hP x (fun y hy => ((phi_eq_zero_iff hπ h ⟨y, hy⟩).mp (hall _)).2) hxloc

theorem phi_surjective (h : StepHyp Q N x π) {v : HeightOneSpectrum (𝓞 F)} (hP : WeakUnimod Q N v)
    (hxloc : ∀ w, w ≠ v → locVec w x ∈ loc w N) : Function.Surjective (phi hπ h) := by
  letI := isMaximal_span hπ
  obtain ⟨y₀, hy₀⟩ := exists_phi_ne_zero hπ h hP hxloc
  intro q
  refine ⟨((phi hπ h y₀)⁻¹ * q).out • y₀, ?_⟩
  rw [phi_smul, Ideal.Quotient.mk_out, mul_comm, ← mul_assoc, mul_inv_cancel₀ hy₀, one_mul]

/-- $[N : N \cap N'] = N\pi$. -/
theorem relIndex_left (h : StepHyp Q N x π) {v : HeightOneSpectrum (𝓞 F)} (hP : WeakUnimod Q N v)
    (hxloc : ∀ w, w ≠ v → locVec w x ∈ loc w N) :
    (nbr Q N x).toAddSubgroup.relIndex N.toAddSubgroup = HilbertModular.nm π := by
  have hk : (nbr Q N x).toAddSubgroup.addSubgroupOf N.toAddSubgroup = (phi hπ h).ker := by
    ext y
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (y : Fin n → F) ∈ nbr Q N x ↔ phi hπ h y = 0
    rw [phi_eq_zero_iff]
    exact ⟨mem_kerN_of_mem_nbr hπ h y.2, fun hy => kerN_le_nbr Q N x hy⟩
  rw [AddSubgroup.relIndex, hk]
  change (phi hπ h).ker.index = HilbertModular.nm π
  rw [index_ker_of_surjective _ (phi_surjective hπ h hP hxloc), natCard_res]

/-- The map $a \mapsto a x$, $\mathcal O \to N'/(N \cap N')$. -/
def chi : 𝓞 F →+ (nbr Q N x).toAddSubgroup ⧸ N.toAddSubgroup.addSubgroupOf (nbr Q N x).toAddSubgroup :=
  (QuotientAddGroup.mk' _).comp
    { toFun a := ⟨a • x, (nbr Q N x).smul_mem a (x_mem_nbr Q N x)⟩
      map_zero' := by ext; simp
      map_add' a b := by ext; simp [add_smul] }

theorem chi_surjective (h : StepHyp Q N x π) : Function.Surjective (chi (Q := Q) (N := N) (x := x)) := by
  intro q
  obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  obtain ⟨y, hy, a, rfl⟩ := (mem_nbr Q N x).mp hz
  refine ⟨a, ?_⟩
  simp only [chi, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
    QuotientAddGroup.mk'_apply]
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
  change -(a • x) + (y + a • x) ∈ N
  rw [show -(a • x) + (y + a • x) = y by abel]
  exact hy.1

theorem chi_ker (h : StepHyp Q N x π) :
    (chi (Q := Q) (N := N) (x := x)).ker = (Ideal.Quotient.mk (Ideal.span {π})).toAddMonoidHom.ker := by
  ext a
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  simp only [chi, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  change a • x ∈ N ↔ π ∣ a
  refine ⟨dvd_of_smul_mem hπ h.notMem h.pix, ?_⟩
  rintro ⟨d, rfl⟩
  rw [mul_comm, mul_smul]
  exact N.smul_mem d h.pix

/-- $[N' : N \cap N'] = N\pi$. -/
theorem relIndex_right (h : StepHyp Q N x π) :
    N.toAddSubgroup.relIndex (nbr Q N x).toAddSubgroup = HilbertModular.nm π := by
  rw [AddSubgroup.relIndex, AddSubgroup.index]
  have h1 := index_ker_of_surjective _ (chi_surjective hπ h (Q := Q))
  rw [chi_ker hπ h, index_ker_of_surjective _ Ideal.Quotient.mk_surjective, natCard_res] at h1
  exact h1.symm

theorem smul_left (h : StepHyp Q N x π) {z : Fin n → F} (hz : z ∈ nbr Q N x) :
    algebraMap (𝓞 F) F π • z ∈ N := by
  rw [algebraMap_smul]
  obtain ⟨y, hy, a, rfl⟩ := (mem_nbr Q N x).mp hz
  rw [smul_add, smul_comm]
  exact N.add_mem (N.smul_mem _ hy.1) (N.smul_mem _ h.pix)

theorem smul_right (h : StepHyp Q N x π) {y : Fin n → F} (hy : y ∈ N) :
    algebraMap (𝓞 F) F π • y ∈ nbr Q N x := by
  rw [algebraMap_smul]
  refine kerN_le_nbr Q N x ⟨N.smul_mem _ hy, ?_⟩
  rw [bil_osmul_left, ← bil_osmul_right]
  exact bil_pix_mem hπ h hy

theorem isIntegral_nbr (h : StepHyp Q N x π) : IsIntegral Q (nbr Q N x) := by
  intro z hz
  obtain ⟨y, hy, a, rfl⟩ := (mem_nbr Q N x).mp hz
  rw [evalIn_add, evalIn_osmul, bil_osmul_right]
  exact add_mem (add_mem (h.int y hy.1) (mul_mem (pow_mem (RingHom.mem_range.mpr ⟨a, rfl⟩) 2) h.qx)) (mul_mem (RingHom.mem_range.mpr ⟨a, rfl⟩) hy.2)

/-- **The step: $N'$ is a $\pi$-neighbour of $N$.** -/
theorem isNbrL_nbr (h : StepHyp Q N x π) {v : HeightOneSpectrum (𝓞 F)} (hP : WeakUnimod Q N v)
    (hxloc : ∀ w, w ≠ v → locVec w x ∈ loc w N) : IsNbrL Q π N (nbr Q N x) where
  index_left := relIndex_left hπ h hP hxloc
  index_right := relIndex_right hπ h
  smul_left _ hz := smul_left hπ h hz
  smul_right _ hy := smul_right hπ h hy
  int_left := h.int
  int_right := isIntegral_nbr hπ h

/-- $N'$ agrees with $N$ at every $w \ne (\pi)$. -/
theorem loc_nbr (h : StepHyp Q N x π) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ hosOf hπ)
    (hxw : locVec w x ∈ loc w N) : loc w (nbr Q N x) = loc w N := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, a, rfl⟩ := (mem_nbr Q N x).mp hz
    rw [map_add, locVec_smul_int]
    exact (loc w N).add_mem (locVec_mem_loc w hy.1) ((loc w N).smul_mem _ hxw)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    refine locVec_mem_of_smul hπ hw (locVec_mem_loc w ?_)
    rw [← algebraMap_smul F]
    exact smul_right hπ h hy

theorem isLattice_nbr (h : StepHyp Q N x π) (hN : N.IsLattice F) : (nbr Q N x).IsLattice F := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hN
  refine isLattice_of_global_bounds (d := π * d) (mul_ne_zero hπ.ne_zero hd) (fun z hz => ?_) (fun z hz => ?_)
  · rw [mul_smul, ← algebraMap_smul F]
    exact smul_right hπ h (h1 z hz)
  · rw [mul_comm, mul_smul, ← algebraMap_smul F π]
    exact h2 _ (smul_left hπ h hz)

/-- **$N'$ is again weakly unimodular.** -/
theorem weakUnimod_nbr (h : StepHyp Q N x π) (hP : WeakUnimod Q N (hosOf hπ))
    (hxloc : ∀ w, w ≠ hosOf hπ → locVec w x ∈ loc w N) : WeakUnimod Q (nbr Q N x) (hosOf hπ) := by
  intro z hz hzloc
  obtain ⟨y₀, hy₀⟩ := exists_phi_ne_zero hπ h hP hxloc
  obtain ⟨u, hu, hue⟩ := phi_spec hπ h y₀
  have hu' : u ∉ Ideal.span {π} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hue]; exact hy₀
  obtain ⟨u', i, hi, hui⟩ := (isMaximal_span hπ).exists_inv hu'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  -- `π B(y₀, z) = b`
  have hux : algebraMap (𝓞 F) F π * bil Q y₀ x = algebraMap (𝓞 F) F u := by rw [hu, bil_osmul_right]
  obtain ⟨b, hb⟩ := hz _ (smul_right hπ h y₀.2)
  rw [algebraMap_smul, bil_osmul_left] at hb
  set t : 𝓞 F := b * u'
  set z' := z - t • x
  -- `B(y₀, z') ∈ (algebraMap (𝓞 F) F).range`
  have hy₀z' : bil Q y₀ z' = algebraMap (𝓞 F) F (b * c) := by
    apply mem_of_pi_mul hπ.ne_zero
    calc algebraMap (𝓞 F) F π * bil Q y₀ z' = algebraMap (𝓞 F) F π * bil Q y₀ z -
          algebraMap (𝓞 F) F t * (algebraMap (𝓞 F) F π * bil Q y₀ x) := by
          rw [bil_sub_right, bil_osmul_right]; ring
      _ = algebraMap (𝓞 F) F b - algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F u := by rw [← hb, hux]
      _ = algebraMap (𝓞 F) F (π * (b * c)) := by
          rw [← map_mul, ← map_sub]; congr 1; simp only [t]; linear_combination (-b) * hui
  have hxz : bil Q x z ∈ (algebraMap (𝓞 F) F).range := hz x (x_mem_nbr Q N x)
  have hxx : bil Q x x ∈ (algebraMap (𝓞 F) F).range := by rw [bil_self]; exact mul_mem (RingHom.mem_range.mpr ⟨2, map_ofNat _ 2⟩) h.qx
  -- `B(N, z') ⊆ (algebraMap (𝓞 F) F).range`
  have hNz' : ∀ y ∈ N, bil Q y z' ∈ (algebraMap (𝓞 F) F).range := by
    intro y hy
    obtain ⟨s, hs⟩ := bil_pix_mem hπ h hy
    set y₁ := y - (s * u') • (y₀ : Fin n → F)
    have hy₁ : y₁ ∈ kerN Q N x := by
      refine ⟨N.sub_mem hy (N.smul_mem _ y₀.2), ⟨s * c, ?_⟩⟩
      symm
      apply mem_of_pi_mul hπ.ne_zero
      calc algebraMap (𝓞 F) F π * bil Q y₁ x = algebraMap (𝓞 F) F π * bil Q y x -
            algebraMap (𝓞 F) F (s * u') * (algebraMap (𝓞 F) F π * bil Q y₀ x) := by
            simp only [y₁]; rw [bil_sub_left, bil_osmul_left]; ring
        _ = algebraMap (𝓞 F) F s - algebraMap (𝓞 F) F (s * u') * algebraMap (𝓞 F) F u := by
            rw [← bil_osmul_right, ← hs, hux]
        _ = algebraMap (𝓞 F) F (π * (s * c)) := by
            rw [← map_mul, ← map_sub]; congr 1; linear_combination (-s) * hui
    have h1 : bil Q y₁ z' ∈ (algebraMap (𝓞 F) F).range := by
      rw [bil_sub_right, bil_osmul_right]
      exact sub_mem (hz _ (kerN_le_nbr Q N x hy₁)) (mul_mem (RingHom.mem_range.mpr ⟨t, rfl⟩) hy₁.2)
    have e : y = y₁ + (s * u') • (y₀ : Fin n → F) := by simp [y₁]
    rw [e, bil_add_left, bil_osmul_left, hy₀z']
    exact add_mem h1 (mul_mem (RingHom.mem_range.mpr ⟨_, rfl⟩) (RingHom.mem_range.mpr ⟨_, rfl⟩))
  have hz'N : z' ∈ N := by
    refine hP z' hNz' fun w hw => ?_
    rw [map_sub, locVec_smul_int]
    have := hzloc w hw
    rw [loc_nbr hπ h hw (hxloc w hw)] at this
    exact (loc w N).sub_mem this ((loc w N).smul_mem _ (hxloc w hw))
  have hz'x : bil Q z' x ∈ (algebraMap (𝓞 F) F).range := by
    rw [bil_comm, bil_sub_right, bil_osmul_right]
    exact sub_mem hxz (mul_mem (RingHom.mem_range.mpr ⟨t, rfl⟩) hxx)
  have : z = z' + t • x := by simp [z']
  rw [this]
  exact (mem_nbr Q N x).mpr ⟨z', ⟨hz'N, hz'x⟩, t, rfl⟩

end Step

/-! ### Local duality: unimodularity is a genus invariant -/

section LocalDual

theorem exists_bound_coords {v : HeightOneSpectrum (𝓞 F)} (y : Fin n → v.adicCompletion F) :
    ∃ k : ℕ, ∀ i, Valued.v (y i) ≤ exp (k : ℤ) := by
  choose k hk using fun i => exists_valued_le v (y i)
  refine ⟨∑ i, k i, fun i => (hk i).trans (exp_le_exp.mpr ?_)⟩
  exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)

theorem bilR_add_right {R : Type*} [CommRing R] [Algebra F R] (y z z' : Fin n → R) :
    bilR Q R y (z + z') = bilR Q R y z + bilR Q R y z' := by
  simp [bilR, mulVec_add, dotProduct_add]

/-- **Local duality from global unimodularity:** if $L$ is an integral lattice, unimodular at $v$ in the global sense
(`IsUnimodularAt`), then every $\zeta \in F_v^n$ with $B(L_v, \zeta) \subseteq \mathfrak o_v$ lies in $L_v$ ($L_v^\# \subseteq L_v$).
*Proof:* approximate $\zeta$ by $x \in F^n$ within $L_v$, make $t\,x$ integral at all $w \ne v$ with $t \equiv 1$ at $v$ (CRT); then
$B(L, t x) \subseteq \mathcal O_F$, so $t x \in L_v$. -/
theorem mem_loc_of_locDual {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) (hLi : IsIntegral Q L)
    {v : HeightOneSpectrum (𝓞 F)} (hLu : IsUnimodularAt Q L v) {ζ : Fin n → v.adicCompletion F}
    (hζ : ∀ l ∈ loc v L, Valued.v (bilR Q (v.adicCompletion F) l ζ) ≤ 1) : ζ ∈ loc v L := by
  obtain ⟨K, hK, -⟩ := exists_local_bounds v (loc_isLattice v hL)
  choose x hx using fun i => exists_approx v (ζ i) (K : ℤ)
  obtain ⟨k, hk⟩ := exists_bound_coords (locVec v x)
  obtain ⟨t, ht1, htw⟩ := (locFamily hL).exists_crt v x (K + k)
  have hδ : locVec v (t • x) - ζ ∈ loc v L := by
    apply hK
    rw [mem_ball]
    intro i
    have e : (locVec v (t • x) - ζ) i = (algebraMap (𝓞 F) (v.adicCompletion F) t - 1) *
        algebraMap F (v.adicCompletion F) (x i) + -(ζ i - algebraMap F (v.adicCompletion F) (x i)) := by
      rw [Pi.sub_apply, locVec_smul_int_apply]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul]
      have h1 := valued_sub_one_le v ht1
      have h2 := hk i
      rw [locVec_apply] at h2
      calc _ ≤ exp (-((K + k : ℕ) : ℤ)) * exp (k : ℤ) := mul_le_mul' h1 h2
        _ = exp (-(K : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    · rw [Valuation.map_neg]; exact hx i
  have hzL : ∀ y ∈ L, bil Q y (t • x) ∈ (algebraMap (𝓞 F) F).range := by
    intro y hy
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one F
    intro w
    rw [← valued_algebraMap, ← bilR_locVec]
    by_cases hw : w = v
    · subst hw
      have e : locVec w (t • x) = ζ + (locVec w (t • x) - ζ) := by abel
      rw [e, bilR_add_right]
      exact Valuation.map_add_le _ (hζ _ (locVec_mem_loc w hy))
        (valued_bilR_loc_le_one Q w hLi (locVec_mem_loc w hy) hδ)
    · exact valued_bilR_loc_le_one Q w hLi (locVec_mem_loc w hy) (htw w hw)
  have h := hLu _ hzL
  have e : ζ = locVec v (t • x) - (locVec v (t • x) - ζ) := by abel
  rw [e]
  exact (loc v L).sub_mem h hδ

/-- **Unimodularity at $v$ is a genus invariant** (O'Meara §82, §102 [unverified]). -/
@[kb "omeara1963" "§82, §102 (unimodular lattices in a genus) [unverified]"]
theorem isUnimodularAt_of_sameGenus {L M : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F)
    (hLi : IsIntegral Q L) {v : HeightOneSpectrum (𝓞 F)} (hLu : IsUnimodularAt Q L v) (hgen : SameGenus Q L M) :
    IsUnimodularAt Q M v := by
  intro z hz
  obtain ⟨g, hg, hgL⟩ := hgen v
  have hζ : ∀ l ∈ loc v L, Valued.v (bilR Q (v.adicCompletion F) l (g⁻¹.val *ᵥ locVec v z)) ≤ 1 := by
    intro l hl
    have hgl : g.val *ᵥ l ∈ loc v M := hgL ▸ ⟨l, hl, rfl⟩
    rw [← bilR_isometry Q hg, mulVec_inv_mulVec, bilR_comm]
    exact valued_bilR_le_one Q v (fun m hm => by rw [bil_comm]; exact hz m hm) hgl
  have hmem := mem_loc_of_locDual Q hL hLi hLu hζ
  rw [← hgL]
  exact ⟨_, hmem, mulVec_inv_mulVec g _⟩

end LocalDual

/-- **$\mathcal O_F^n$ is unimodular at $v$ for $Q_0 \otimes F$ when $v \nmid \det H(Q_0)$** ($Q_0$ a form over $\mathcal O_F$):
if $B(\mathcal O_F^n, x) \subseteq \mathcal O_F$ then $Hx \in \mathcal O_F^n$, so $\det H \cdot x = \operatorname{adj}(H)\,Hx$ is integral, and
$\det H$ is a unit at $v$. -/
theorem isUnimodularAt_intVec (Q₀ : QuadForm (𝓞 F) n) {v : HeightOneSpectrum (𝓞 F)}
    (hdv : Q₀.hessian.det ∉ v.asIdeal) : IsUnimodularAt (HilbertModular.formF Q₀) intVec v := by
  intro x hx
  set φ := algebraMap (𝓞 F) F
  have hH : (HilbertModular.formF Q₀).hessian = Q₀.hessian.map φ := by
    ext i j; simp [QuadForm.hessian, QuadForm.map, φ]
  have hcoord : ∀ i, (Q₀.hessian.map φ *ᵥ x) i ∈ (algebraMap (𝓞 F) F).range := by
    intro i
    have := hx (Pi.single i 1) (single_one_mem_intVec i)
    rw [bil, hH, single_dotProduct, one_mul] at this
    exact this
  choose w hw using hcoord
  have hw' : intCoe w = Q₀.hessian.map φ *ᵥ x := funext hw
  have hdx : φ Q₀.hessian.det • x = intCoe (Q₀.hessian.adjugate *ᵥ w) := by
    rw [← map_mulVec_intCoe, hw', mulVec_mulVec, ← Matrix.map_mul, adjugate_mul]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, apply_ite, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  rw [loc_intVec, mem_ball]
  intro i
  set u := Q₀.hessian.adjugate *ᵥ w
  have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) Q₀.hessian.det) *
      Valued.v (locVec v x i) = Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (u i)) := by
    rw [← map_mul, locVec_apply, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
      IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) (u i), ← map_mul]
    congr 2
    have := congrFun hdx i
    simpa using this
  rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff.mpr hdv, one_mul] at h1
  rw [h1, neg_zero, exp_zero]
  exact valued_int_le_one v _

/-! ### The induction -/

/-- **Kneser's induction.** Let $M$ be an integral lattice, weakly unimodular at $v = (\pi)$. Every integral lattice $N$, weakly
unimodular at $v$ and agreeing with $M$ at all $w \ne v$, is joined to $M$ by a chain of $\pi$-neighbours. -/
theorem chain_aux {π : 𝓞 F} (hπ : Prime π) {M : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F)
    (hMi : IsIntegral Q M) (hMP : WeakUnimod Q M (hosOf hπ)) :
    ∀ N : Submodule (𝓞 F) (Fin n → F), N.IsLattice F → IsIntegral Q N → WeakUnimod Q N (hosOf hπ) →
      (∀ w, w ≠ hosOf hπ → loc w N = loc w M) → Relation.ReflTransGen (IsNbrL Q π) N M := by
  haveI : IsNoetherian (𝓞 F) M := isNoetherian_of_fg_of_noetherian M hM.fg
  suffices H : ∀ S : Submodule (𝓞 F) M, ∀ N : Submodule (𝓞 F) (Fin n → F), (N ⊓ M).comap M.subtype = S →
      N.IsLattice F → IsIntegral Q N → WeakUnimod Q N (hosOf hπ) →
      (∀ w, w ≠ hosOf hπ → loc w N = loc w M) → Relation.ReflTransGen (IsNbrL Q π) N M from
    fun N => H _ N rfl
  intro S
  induction S using WellFoundedGT.induction with
  | _ S IH => ?_
  intro N hS hN hNi hNP hloc
  by_cases hMN : M ≤ N
  · have : N = M := by
      refine le_antisymm (fun z hz => hMP z (fun y hy => bil_mem Q hNi (hMN hy) hz) fun w hw => ?_) hMN
      rw [← hloc w hw]; exact locVec_mem_loc w hz
    subst this; exact Relation.ReflTransGen.refl
  obtain ⟨y, hyM, hyN⟩ := Set.not_subset.mp hMN
  have hex : ∃ k : ℕ, (π ^ k) • y ∈ N := by
    obtain ⟨K, hK, -⟩ := exists_local_bounds (hosOf hπ) (loc_isLattice (hosOf hπ) hN)
    obtain ⟨k, hk⟩ := exists_bound_coords (locVec (hosOf hπ) y)
    refine ⟨K + k, (mem_iff_forall_loc hN _).mpr fun w => ?_⟩
    rw [locVec_smul_int]
    by_cases hw : w = hosOf hπ
    · subst hw
      apply hK
      rw [mem_ball]
      intro i
      rw [smul_apply_coe, algebraMap_int_coe, map_mul]
      have hpi : π ∈ (hosOf hπ).asIdeal := by
        rw [hosOf_asIdeal]; exact Ideal.mem_span_singleton_self π
      have h1 := valued_le_of_mem_pow (hosOf hπ) (Ideal.pow_mem_pow hpi (K + k))
      calc _ ≤ exp (-((K + k : ℕ) : ℤ)) * exp (k : ℤ) := mul_le_mul' h1 (hk i)
        _ = exp (-(K : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    · exact (loc w N).smul_mem _ (by rw [hloc w hw]; exact locVec_mem_loc w hyM)
  classical
  have hk₀ : (π ^ Nat.find hex) • y ∈ N := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    refine Nat.pos_of_ne_zero fun h0 => hyN ?_
    rw [h0, pow_zero, one_smul] at hk₀; exact hk₀
  set x := (π ^ (Nat.find hex - 1)) • y with hxdef
  have hxM : x ∈ M := M.smul_mem _ hyM
  have hxN : x ∉ N := Nat.find_min hex (Nat.sub_lt hpos one_pos)
  have hpix : π • x ∈ N := by
    rw [hxdef, smul_smul, ← pow_succ', Nat.sub_add_cancel hpos]; exact hk₀
  have hh : StepHyp Q N x π := ⟨hNi, hpix, hxN, hMi x hxM⟩
  have hxloc : ∀ w, w ≠ hosOf hπ → locVec w x ∈ loc w N := fun w hw => by
    rw [hloc w hw]; exact locVec_mem_loc w hxM
  have hloc' : ∀ w, w ≠ hosOf hπ → loc w (nbr Q N x) = loc w M := fun w hw => by
    rw [loc_nbr hπ hh hw (hxloc w hw), hloc w hw]
  have hlt : S < ((nbr Q N x) ⊓ M).comap M.subtype := by
    rw [← hS]
    refine lt_of_le_of_ne ?_ ?_
    · intro z hz
      simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.coe_subtype] at hz ⊢
      exact ⟨kerN_le_nbr Q N x ⟨hz.1, bil_mem Q hMi hz.2 hxM⟩, hz.2⟩
    · intro heq
      have hmem : (⟨x, hxM⟩ : M) ∈ ((nbr Q N x) ⊓ M).comap M.subtype := by
        simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.coe_subtype]
        exact ⟨x_mem_nbr Q N x, hxM⟩
      rw [← heq] at hmem
      simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.coe_subtype] at hmem
      exact hxN hmem.1
  exact Relation.ReflTransGen.head (isNbrL_nbr hπ hh hNP hxloc)
    (IH _ hlt _ rfl (isLattice_nbr hπ hh hN) (isIntegral_nbr hπ hh) (weakUnimod_nbr hπ hh hNP hxloc) hloc')

/-- **Kneser's local lemma, proved** (Kneser 1957, §2 [unverified]): the named input `LocalNeighborChain F` holds for every
number field $F$. (The hypothesis $\pi \nmid 2$ is not used.) -/
@[kb "kneser1957" "§2 [unverified]"]
theorem localNeighborChain : LocalNeighborChain F := by
  refine ⟨fun {n} Q {π} hπ _ L M hLi hLu hgen hloc => ?_⟩
  have hMi := SameGenus.isIntegral Q hLi hgen
  have hMu := isUnimodularAt_of_sameGenus Q L.2 hLi hLu hgen
  exact chain_aux Q hπ M.2 hMi (weakUnimod_of_isUnimodularAt Q M.2 hMu) L.1 L.2 hLi
    (weakUnimod_of_isUnimodularAt Q L.2 hLu) fun w hw => (hloc w hw).symm

end QuadFormsKB.Lattices.KneserLocal

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **Kneser's neighbour theorem, unconditional** (Kneser 1957, Satz 2 [unverified]). Let $n \ge 3$, $Q$ nondegenerate,
$\pi$ a prime element with $\pi \nmid 2$ and $Q$ isotropic over $F_\pi$, and $L$ integral and unimodular at $(\pi)$. Then for every $M$
in the spinor genus of $L$ there is a lattice $M' \cong M$ reachable from $L$ by a chain of $\pi$-neighbours. -/
@[kb "kneser1957" "Satz 2 [unverified]"]
theorem kneser_reach_uncond {n : ℕ} (Q : QuadForm F n) (hn : 3 ≤ n) (hQ : Q.Nondegenerate) {π : 𝓞 F}
    (hπ : Prime π) (h2 : ¬ π ∣ 2) (hiso : Q.IsotropicIn ((Nbr.hosOf hπ).adicCompletion F)) {L M : Lat F n}
    (hLi : IsIntegral Q L.1) (hLu : IsUnimodularAt Q L.1 (Nbr.hosOf hπ)) (hM : SameSpinorGenus Q L M) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ Relation.ReflTransGen (Nbr.IsNbrL Q π) L.1 M'.1 :=
  kneser_reach_of_localChain KneserLocal.localNeighborChain Q hn hQ hπ h2 hiso hLi hLu hM

/-- **Kneser's theorem for a genus that is one spinor genus, unconditional**: the $\pi$-neighbour graph starting at $L$
reaches every class of the genus of $L$ (hypotheses as `kneser_reach_uncond`, plus gen $=$ spn for $L$). -/
@[kb "kneser1957" "Satz 2 [unverified]"]
theorem kneser_reach_genus_uncond {n : ℕ} (Q : QuadForm F n) (hn : 3 ≤ n) (hQ : Q.Nondegenerate) {π : 𝓞 F}
    (hπ : Prime π) (h2 : ¬ π ∣ 2) (hiso : Q.IsotropicIn ((Nbr.hosOf hπ).adicCompletion F)) {L : Lat F n}
    (hLi : IsIntegral Q L.1) (hLu : IsUnimodularAt Q L.1 (Nbr.hosOf hπ))
    (hgs : ∀ M : Lat F n, SameGenus Q L.1 M.1 → SameSpinorGenus Q L M) {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ Relation.ReflTransGen (Nbr.IsNbrL Q π) L.1 M'.1 :=
  kneser_reach_uncond Q hn hQ hπ h2 hiso hLi hLu (hgs M hM)

/-- **Forms of rank $\ge 5$ are isotropic at every finite place** (O'Meara 63:19 [unverified]): for $n \ge 5$ and $Q$
nondegenerate over $F$, $Q$ is isotropic over $F_v$ for every finite place $v$. So the isotropy hypothesis of Kneser's
theorem (`kneser_reach_uncond`) is automatic in rank $\ge 5$ (`kneser_reach_uncond_of_five_le`). -/
@[kb "omeara1963" "63:19 [unverified]"]
theorem isotropicIn_adicCompletion_of_five_le {n : ℕ} (Q : QuadForm F n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 F)) : Q.IsotropicIn (v.adicCompletion F) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  set Q' : QuadForm (v.adicCompletion F) (5 + m) := Q.map (algebraMap F (v.adicCompletion F))
  have hQ' : Q'.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr hQ
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q' hQ'
  obtain ⟨z, hz, hz0⟩ := LocalRankFive.isotropic_diag_five v (fun i : Fin 5 => a (Fin.castAdd m i))
    (fun i => ha _)
  have hd : (QuadForm.diag a).IsotropicIn (v.adicCompletion F) := by
    refine ⟨Fin.append z 0, fun h0 => hz (funext fun i => ?_), ?_⟩
    · have := congrFun h0 (Fin.castAdd m i)
      simpa using this
    · rw [PadicClass.evalIn_diag_self, Fin.sum_univ_add]
      rw [PadicClass.evalIn_diag_self] at hz0
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
      simpa using hz0
  obtain ⟨x, hx, hx0⟩ := (FieldGen.isotropicIn_iff_of_isometricIn _ hiso).mpr hd
  exact ⟨x, hx, by rw [evalIn_eq_eval_map]; exact hx0⟩

/-- **Kneser's neighbour theorem in rank $\ge 5$** (no isotropy hypothesis). -/
@[kb "kneser1957" "Satz 2 [unverified]"]
theorem kneser_reach_uncond_of_five_le {n : ℕ} (Q : QuadForm F n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate) {π : 𝓞 F}
    (hπ : Prime π) (h2 : ¬ π ∣ 2) {L M : Lat F n} (hLi : IsIntegral Q L.1)
    (hLu : IsUnimodularAt Q L.1 (Nbr.hosOf hπ)) (hM : SameSpinorGenus Q L M) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ Relation.ReflTransGen (Nbr.IsNbrL Q π) L.1 M'.1 :=
  kneser_reach_uncond Q (by omega) hQ hπ h2 (isotropicIn_adicCompletion_of_five_le Q hn hQ _) hLi hLu hM

/-- **Unimodular forms of rank $\ge 3$ at a non-dyadic place are isotropic** (Hanke 2004, Remark 3.8.1 [unverified];
O'Meara 92:1 [unverified]): for $Q_0$ over $\mathcal O_F$ with $v \nmid 2\det H$ and $n \ge 3$, $Q_0 \otimes F$ is isotropic over $F_v$
(from `LocalDensity.NF.isotropicIn_of_notDvdLevel`: Chevalley–Warning mod $v$ and Hensel). So in the setting of Kneser's
theorem with $L = \mathcal O_F^n$ the isotropy hypothesis is automatic in every rank $n \ge 3$. -/
@[kb "hanke2004" "Remark 3.8.1, p. 364 [unverified]"]
theorem isotropicIn_formF_of_unimodular {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hn : 3 ≤ n) {v : HeightOneSpectrum (𝓞 F)}
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : Q₀.hessian.det ∉ v.asIdeal) :
    (HilbertModular.formF Q₀).IsotropicIn (v.adicCompletion F) := by
  obtain ⟨x, hx, h0⟩ :=
    LocalDensity.NF.isotropicIn_of_notDvdLevel v Q₀ ((LocalDensity.NF.notDvdLevel_iff v Q₀ h2).2 hdet) hn
  refine ⟨x, hx, ?_⟩
  rw [← h0]
  simp [QuadForm.evalIn, QuadForm.map, ← IsScalarTower.algebraMap_apply]

end QuadFormsKB.Lattices
