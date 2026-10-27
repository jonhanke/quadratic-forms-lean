/-
# The transformation law of $\alpha_\mathfrak p$ under a change of lattice

**Layer:** first an abstract group with two groups of integral isometries (a DVR $R$, every residue characteristic), then the
completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime, with **local** forms
$Q_v$ over $F_\mathfrak p$ given by integral models $Q_o$ over $\mathfrak o_\mathfrak p$.

For lattices $\Lambda_1 \subseteq \Lambda_2$ of a quadratic space $(V, Q)$ over $F_\mathfrak p$ with stabilizers $K_i = O(\Lambda_i)$, the
index ratio $r(K_1, K_2) = [K_1 : K_1\cap K_2]/[K_2 : K_1\cap K_2]$ is Weil's ratio of Haar measures $\mu(K_1)/\mu(K_2)$. The
**$\alpha$ transformation law** (`AlphaLawAt`) is its combinatorial evaluation: for $\Lambda_1 = P\Lambda_2$,
$$r(K_1, K_2)\cdot\beta(\Lambda_2) = \beta(\Lambda_1)\cdot\|\det P\|^{N+1},$$
$\beta(\Lambda) = \beta_\mathfrak p(Q_\Lambda, Q_\Lambda)$ the self-density of the Gram form of $\Lambda$ (`DVR.localDensityForm`). It is the finite
form of the normalization $\mu(O(\Lambda)) \propto \alpha(\Lambda)|\det\Lambda|^{(N+1)/2}$ of Weil's gauge-form measures, proved here by
counting (no Haar measure is used).

**Proves (this part)**
* `rel_nearCount` (**REL, the lattice change of orbit counts**): for $y \in \Lambda_1$,
  $N_1(K_1y)\,[\mathrm{St}_{K_1}y : \mathrm{St}_Jy]\,[K_2:J] = [\Lambda_2:\Lambda_1]\,[K_1:J]\,N_2(K_2y)\,[\mathrm{St}_{K_2}y : \mathrm{St}_Jy]$,
  $J = K_1\cap K_2$: the orbit comparison `nearCount_mul_relIndex` in each lattice, and the lattice change
  `nearCount_compMat` for the $J$-orbit (which is open in both lattices, `exists_openMat`).

Sources: Weil 1982, §3.4 [unverified]; Hanke 2004, §3, pp. 359–360 (the reduction maps $\pi_Z$, $\pi_{B'}$, $\pi_{B''}$ change the lattice).
Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.AlphaLawIndex

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity LocalDensity.DVR

/-! ### REL: the lattice change of orbit counts (abstract form) -/

section RelAbstract

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {N : ℕ}
  [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {G : Type*} [Group G] (K₁ K₂ : Subgroup G)
  (ρ₁ : K₁ →* Matrix (Fin N) (Fin N) R) (ρ₂ : K₂ →* Matrix (Fin N) (Fin N) R)

/-- **REL: the lattice change of orbit counts** (Weil 1982, §3.4 [unverified]). Abstract setting: $K_1, K_2$ are subgroups of a
group $G$ (the stabilizers of $\Lambda_1 = PR^N \subseteq \Lambda_2 = R^N$ in $O(V)$), acting on $\Lambda_1$, $\Lambda_2$ by all integral
isometries of $Q\circ P$, resp. $Q$ ($\rho_1$, $\rho_2$), compatibly on $J = K_1\cap K_2$ ($P\rho_1 = \rho_2P$), and elements
$\equiv 1 \bmod \pi^d$ of either lie in the other. For $y \in R^N$ with $(Q\circ P)(y) = t \ne 0$ ($\pi^e\,\Vert\,2t$, $\pi^f\,\Vert\,4t$),
$r \ge f + 1 + d$, $k \ge r + c + e$, $k \ge 2e + 1$:
$$N_{k,r}^{Q\circ P}(K_1y)\cdot[\mathrm{St}_{K_1}y : \mathrm{St}_{K_1}y\cap J]\cdot[K_2 : J]
  = |\ker(P\bmod\pi^k)|\cdot[K_1:J]\cdot N^Q_{k,r}(K_2Py)\cdot[\mathrm{St}_{K_2}Py : \mathrm{St}_{K_2}Py\cap J].$$ -/
@[kb "weil1982" "§3.4 (orbit measures under a change of lattice) [unverified]"]
theorem rel_nearCount {π : R} (hπ : Irreducible π) (Q : QuadForm R N) (P : Matrix (Fin N) (Fin N) R)
    (hP : P.det ≠ 0) {c : ℕ} (hc : ∀ u : Fin N → R, ∃ w, P *ᵥ w = π ^ c • u)
    (hρ₁ : ∀ κ, (Q.compMat P).compMat (ρ₁ κ) = Q.compMat P) (hρ₂ : ∀ κ, Q.compMat (ρ₂ κ) = Q)
    (hsurj₁ : ∀ X, (Q.compMat P).compMat X = Q.compMat P → ∃ κ, ρ₁ κ = X)
    (hsurj₂ : ∀ X, Q.compMat X = Q → ∃ κ, ρ₂ κ = X)
    (hcompat : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂), P * ρ₁ ⟨g, h₁⟩ = ρ₂ ⟨g, h₂⟩ * P)
    {d : ℕ} (hJ₁ : ∀ κ : K₁, (∀ i j, π ^ d ∣ ρ₁ κ i j - (1 : Matrix (Fin N) (Fin N) R) i j) → (κ : G) ∈ K₂)
    (hJ₂ : ∀ κ : K₂, (∀ i j, π ^ d ∣ ρ₂ κ i j - (1 : Matrix (Fin N) (Fin N) R) i j) → (κ : G) ∈ K₁)
    {t : R} (ht : t ≠ 0) {e f : ℕ} (he : π ^ e ∣ 2 * t) (he' : ¬ π ^ (e + 1) ∣ 2 * t)
    (hf : π ^ f ∣ 4 * t) (hf' : ¬ π ^ (f + 1) ∣ 4 * t)
    (y : Fin N → R) (hy : (Q.compMat P).eval y = t)
    {k r : ℕ} (hr : f + 1 + d ≤ r) (hk : r + c + e ≤ k) (hk2 : 2 * e + 1 ≤ k) :
    nearCount (Q.compMat P) π t k r (orbitOf ρ₁ ⊤ y) * (K₂.subgroupOf K₁).relIndex (stabOf ρ₁ y) *
        K₁.relIndex K₂ =
      Nat.card (redMat π k P).ker * K₂.relIndex K₁ * nearCount Q π t k r (orbitOf ρ₂ ⊤ (P *ᵥ y)) *
        (K₁.subgroupOf K₂).relIndex (stabOf ρ₂ (P *ᵥ y)) := by
  classical
  set Q₁ := Q.compMat P
  set J₁ := K₂.subgroupOf K₁
  set J₂ := K₁.subgroupOf K₂
  have hrk : r ≤ k := by omega
  have hevalρ₁ : ∀ κ z, Q₁.eval (ρ₁ κ *ᵥ z) = Q₁.eval z := fun κ z => by rw [← eval_compMat, hρ₁]
  have hevalρ₂ : ∀ κ z, Q.eval (ρ₂ κ *ᵥ z) = Q.eval z := fun κ z => by rw [← eval_compMat, hρ₂]
  have hPy : Q.eval (P *ᵥ y) = t := by rw [← eval_compMat]; exact hy
  -- compatibility on vectors
  have hcv : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂) (z : Fin N → R),
      P *ᵥ (ρ₁ ⟨g, h₁⟩ *ᵥ z) = ρ₂ ⟨g, h₂⟩ *ᵥ (P *ᵥ z) := by
    intro g h₁ h₂ z
    rw [mulVec_mulVec, mulVec_mulVec, hcompat g h₁ h₂]
  -- openness in the coordinates of `Λ₁`
  have hopen₁ : ∀ κ ∈ congrSub ρ₁ π r y, ∃ γ ∈ J₁, ρ₁ γ *ᵥ y = ρ₁ κ *ᵥ y := by
    intro κ hκ
    obtain ⟨T, hT, hTy, hT1⟩ := exists_openMat hπ Q₁ ht hf hf' (s := r) (by omega) hy
      (by rw [hevalρ₁]; exact hy) hκ
    obtain ⟨γ, rfl⟩ := hsurj₁ T hT
    exact ⟨γ, hJ₁ γ fun i j => (pow_dvd_pow π (by omega)).trans (hT1 i j), hTy⟩
  have hopen₂ : ∀ κ ∈ congrSub ρ₂ π r (P *ᵥ y), ∃ γ ∈ J₂, ρ₂ γ *ᵥ (P *ᵥ y) = ρ₂ κ *ᵥ (P *ᵥ y) := by
    intro κ hκ
    obtain ⟨T, hT, hTy, hT1⟩ := exists_openMat hπ Q ht hf hf' (s := r) (by omega) hPy
      (by rw [hevalρ₂]; exact hPy) hκ
    obtain ⟨γ, rfl⟩ := hsurj₂ T hT
    exact ⟨γ, hJ₂ γ fun i j => (pow_dvd_pow π (by omega)).trans (hT1 i j), hTy⟩
  -- the orbit comparison in each lattice
  have hc₁ := nearCount_mul_relIndex ρ₁ Q₁ hρ₁ π t hrk hπ J₁ y hopen₁
  have hc₂ := nearCount_mul_relIndex ρ₂ Q hρ₂ π t hrk hπ J₂ (P *ᵥ y) hopen₂
  -- `P (J y) = J (P y)`
  have himg : (P *ᵥ ·) '' orbitOf ρ₁ J₁ y = orbitOf ρ₂ J₂ (P *ᵥ y) := by
    ext z
    constructor
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      have hγ' : ((γ : K₁) : G) ∈ K₂ := Subgroup.mem_subgroupOf.mp hγ
      exact ⟨⟨γ, hγ'⟩, Subgroup.mem_subgroupOf.mpr γ.2, (hcv γ γ.2 hγ' y).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      have hγ' : ((γ : K₂) : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hγ
      exact ⟨ρ₁ ⟨γ, hγ'⟩ *ᵥ y, ⟨⟨γ, hγ'⟩, Subgroup.mem_subgroupOf.mpr γ.2, rfl⟩, hcv γ hγ' γ.2 y⟩
  -- the `J`-orbit is saturated in the coordinates of `Λ₂`
  have hsat : ∀ a ∈ orbitOf ρ₁ J₁ y, ∀ z, Q.eval z = t → (∀ i, π ^ (f + 1 + d) ∣ z i - (P *ᵥ a) i) →
      ∃ a' ∈ orbitOf ρ₁ J₁ y, z = P *ᵥ a' := by
    rintro _ ⟨γ, hγ, rfl⟩ z hz hza
    have hγ2 : ((γ : K₁) : G) ∈ K₂ := hγ
    rw [hcv γ γ.2 hγ2 y] at hza
    have hb : Q.eval (ρ₂ ⟨γ, hγ2⟩ *ᵥ (P *ᵥ y)) = t := by rw [hevalρ₂]; exact hPy
    obtain ⟨T, hT, hTy, hT1⟩ := exists_openMat hπ Q ht hf hf' (s := f + 1 + d) (by omega) hb hz hza
    obtain ⟨δ, rfl⟩ := hsurj₂ T hT
    have hδ1 : ((δ : K₂) : G) ∈ K₁ := hJ₂ δ fun i j => (pow_dvd_pow π (by omega)).trans (hT1 i j)
    have hγ1 : ((γ : K₁) : G) ∈ K₁ := γ.2
    set g := (δ : G) * (γ : G)
    have hg1 : g ∈ K₁ := K₁.mul_mem hδ1 hγ1
    have hg2 : g ∈ K₂ := K₂.mul_mem δ.2 hγ2
    refine ⟨ρ₁ ⟨g, hg1⟩ *ᵥ y, ⟨⟨g, hg1⟩, hg2, rfl⟩, ?_⟩
    rw [hcv g hg1 hg2, ← hTy]
    have : (⟨g, hg2⟩ : K₂) = δ * ⟨γ, hγ2⟩ := rfl
    rw [this, map_mul, ← mulVec_mulVec]
  have hlat := nearCount_compMat hπ Q he he' P hP hc hsat hr hk hk2
  rw [himg] at hlat
  -- assemble
  have e1 : J₁.index = K₂.relIndex K₁ := rfl
  have e2 : J₂.index = K₁.relIndex K₂ := rfl
  rw [e1] at hc₁
  rw [e2] at hc₂
  calc nearCount Q₁ π t k r (orbitOf ρ₁ ⊤ y) * J₁.relIndex (stabOf ρ₁ y) * K₁.relIndex K₂
      = K₂.relIndex K₁ * nearCount Q₁ π t k r (orbitOf ρ₁ J₁ y) * K₁.relIndex K₂ := by rw [hc₁]
    _ = K₂.relIndex K₁ * (Nat.card (redMat π k P).ker * nearCount Q π t k r (orbitOf ρ₂ J₂ (P *ᵥ y))) *
          K₁.relIndex K₂ := by rw [hlat]
    _ = Nat.card (redMat π k P).ker * K₂.relIndex K₁ *
          (K₁.relIndex K₂ * nearCount Q π t k r (orbitOf ρ₂ J₂ (P *ᵥ y))) := by ring
    _ = _ := by rw [← hc₂]; ring

end RelAbstract

/-! ### Local forms, lattices and their stabilizers -/

section LocalGroups

open NumberField IsDedekindDomain Lattices

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The isometry group** $O(Q_v)(F_\mathfrak p) = \{g \in \mathrm{GL}_N(F_\mathfrak p) : Q_v\circ g = Q_v\}$ of a local form. -/
def LO (Qv : QuadForm Fv N) : Subgroup (GL (Fin N) Fv) where
  carrier := {g | Qv.compMat g.val = Qv}
  mul_mem' {a b} ha hb := by
    show Qv.compMat (a * b).val = Qv
    rw [Units.val_mul, ← compMat_mul, show Qv.compMat a.val = Qv from ha, show Qv.compMat b.val = Qv from hb]
  one_mem' := compMat_one Qv
  inv_mem' {a} ha := by
    show Qv.compMat a⁻¹.val = Qv
    have ha' : Qv.compMat a.val = Qv := ha
    conv_lhs => rw [← ha']
    rw [compMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compMat_one]

theorem mem_LO {Qv : QuadForm Fv N} {g : GL (Fin N) Fv} : g ∈ LO v Qv ↔ Qv.compMat g.val = Qv := Iff.rfl

/-- **The stabilizer** $K(\Lambda) = O(\Lambda) = \{g \in O(Q_v)(F_\mathfrak p) : g\Lambda = \Lambda\}$ of an $\mathfrak o_\mathfrak p$-lattice, as a subgroup of
$\mathrm{GL}_N(F_\mathfrak p)$. -/
def KL (Qv : QuadForm Fv N) (Λ : Submodule 𝔬 (Fin N → Fv)) : Subgroup (GL (Fin N) Fv) :=
  (stabLat v (LO v Qv).subtype Λ).map (LO v Qv).subtype

theorem mem_KL {Qv : QuadForm Fv N} {Λ : Submodule 𝔬 (Fin N → Fv)} {g : GL (Fin N) Fv} :
    g ∈ KL v Qv Λ ↔ Qv.compMat g.val = Qv ∧ locAct v g Λ = Λ := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, h1⟩, h2, rfl⟩

theorem commens_KL (Qv : QuadForm Fv N) {Λ₁ Λ₂ : Submodule 𝔬 (Fin N → Fv)} (h₁ : Λ₁.IsLattice Fv)
    (h₂ : Λ₂.IsLattice Fv) : Commens (KL v Qv Λ₁) (KL v Qv Λ₂) :=
  (commens_stabLat v (LO v Qv).subtype h₁ h₂).map (LO v Qv).subtype_injective

/-- **Change of coordinates:** $K_{Q_v}(h\Lambda) = h\,K_{Q_v\circ h}(\Lambda)\,h^{-1}$. -/
theorem KL_locAct (Qv : QuadForm Fv N) (h : GL (Fin N) Fv) (Λ : Submodule 𝔬 (Fin N → Fv)) :
    KL v Qv (locAct v h Λ) = (KL v (Qv.compMat h.val) Λ).map (MulAut.conj h).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv (f := MulAut.conj h), MulAut.conj_symm_apply, mem_KL, mem_KL]
  have hQ : (Qv.compMat h.val).compMat (h⁻¹ * g * h).val = (Qv.compMat g.val).compMat h.val := by
    rw [compMat_mul, compMat_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [hQ, locAct_mul, locAct_mul]
  have e2 : locAct v h⁻¹ (locAct v g (locAct v h Λ)) = Λ ↔ locAct v g (locAct v h Λ) = locAct v h Λ := by
    rw [locAct_eq_iff, inv_inv]
  rw [e2]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h1; rw [h1]
  · intro h1
    have := congrArg (fun S : QuadForm Fv N => S.compMat h⁻¹.val) h1
    simp only [compMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compMat_one] at this
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this

/-- Scaling a lattice does not change its stabilizer. -/
theorem KL_smul (Qv : QuadForm Fv N) (Λ : Submodule 𝔬 (Fin N → Fv)) {c : Fv} (hc : c ≠ 0) :
    KL v Qv (Λ.map ((LinearMap.lsmul Fv (Fin N → Fv) c).restrictScalars 𝔬)) = KL v Qv Λ := by
  ext g
  rw [mem_KL, mem_KL]
  refine and_congr_right fun _ => ?_
  have key : ∀ M : Submodule 𝔬 (Fin N → Fv),
      locAct v g (M.map ((LinearMap.lsmul Fv (Fin N → Fv) c).restrictScalars 𝔬)) =
        (locAct v g M).map ((LinearMap.lsmul Fv (Fin N → Fv) c).restrictScalars 𝔬) := by
    intro M
    ext x
    simp only [locAct, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
      LinearMap.lsmul_apply]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨g.val *ᵥ y, ⟨y, hy, rfl⟩, by rw [mulVec_smul]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨c • y, ⟨y, hy, rfl⟩, by rw [mulVec_smul]⟩
  have hinj : Function.Injective (Submodule.map ((LinearMap.lsmul Fv (Fin N → Fv) c).restrictScalars 𝔬)) := by
    apply Submodule.map_injective_of_injective
    intro x y hxy
    simpa [hc] using hxy
  rw [key]
  exact hinj.eq_iff

/-- Scaling the form does not change the isometries. -/
theorem KL_formSmul {Qv : QuadForm Fv N} {c : Fv} (hc : c ≠ 0) (Λ : Submodule 𝔬 (Fin N → Fv))
    {Qv' : QuadForm Fv N} (hQ : ∀ x, Qv'.eval x = c * Qv.eval x) : KL v Qv' Λ = KL v Qv Λ := by
  ext g
  rw [mem_KL, mem_KL]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h
    refine eq_of_eval_eq fun x => ?_
    have := congrArg (fun S : QuadForm Fv N => S.eval x) h
    simp only [eval_compMat, hQ] at this
    rw [eval_compMat]
    exact mul_left_cancel₀ hc this
  · intro h
    refine eq_of_eval_eq fun x => ?_
    rw [eval_compMat, hQ, hQ, ← eval_compMat, h]

/-- **The lattice $P\,\mathfrak o_\mathfrak p^N$** of an integral matrix $P$. -/
def latOf (P : Matrix (Fin N) (Fin N) 𝔬) : Submodule 𝔬 (Fin N → Fv) :=
  (std v).map ((P.map (algebraMap 𝔬 Fv)).mulVecLin.restrictScalars 𝔬)

theorem det_map_ne_zero {P : Matrix (Fin N) (Fin N) 𝔬} (hP : P.det ≠ 0) : (P.map (algebraMap 𝔬 Fv)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h => hP (Subtype.ext (by simpa using h))

/-- $P$ as an element of $\mathrm{GL}_N(F_\mathfrak p)$. -/
def glOf (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) : GL (Fin N) Fv :=
  Matrix.nonsingInvUnit (P.map (algebraMap 𝔬 Fv)) (isUnit_iff_ne_zero.mpr (det_map_ne_zero v hP))

theorem glOf_val (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) : (glOf v P hP).val = P.map (algebraMap 𝔬 Fv) :=
  rfl

theorem latOf_eq (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) : latOf v P = locAct v (glOf v P hP) (std v) := rfl

theorem latOf_one : latOf v (1 : Matrix (Fin N) (Fin N) 𝔬) = std v := by
  rw [latOf_eq v 1 (by simp), show glOf v (1 : Matrix (Fin N) (Fin N) 𝔬) (by simp) = 1 from
    Units.ext (by rw [glOf_val, Matrix.map_one _ (map_zero _) (map_one _)]; rfl), locAct_one]

theorem latOf_isLattice (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) : (latOf v P).IsLattice Fv := by
  rw [latOf_eq v P hP]; exact locAct_isLattice _ (std_isLattice v)

/-! #### Integral matrices of the stabilizers -/

theorem map_o_inj {r s : ℕ} : Function.Injective
    (fun M : Matrix (Fin r) (Fin s) 𝔬 => M.map (algebraMap 𝔬 Fv)) :=
  fun _ _ h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)

theorem quadForm_map_o_inj {Q₁ Q₂ : QuadForm 𝔬 N} (h : Q₁.map (algebraMap 𝔬 Fv) = Q₂.map (algebraMap 𝔬 Fv)) :
    Q₁ = Q₂ := by
  refine QuadForm.ext (Matrix.ext fun i j => ?_)
  have := congrArg (fun S : QuadForm Fv N => S.coeff i j) h
  simpa [QuadForm.map] using this

theorem exists_intMat_of_std {g : GL (Fin N) Fv} (hg : locAct v g (std v) = std v) :
    ∃ P : Matrix (Fin N) (Fin N) 𝔬, P.map (algebraMap 𝔬 Fv) = g.val := by
  obtain ⟨P₀, hP₀⟩ := exists_gl_o_of_locAct_eq v hg
  exact ⟨P₀.val, congrArg Units.val hP₀⟩

/-- The integral matrix of $\kappa \in K(\mathfrak o_\mathfrak p^N)$ (a choice). -/
def repStdFun (Qv : QuadForm Fv N) (κ : KL v Qv (std v)) : Matrix (Fin N) (Fin N) 𝔬 :=
  (exists_intMat_of_std v ((mem_KL v).mp κ.2).2).choose

theorem repStdFun_map (Qv : QuadForm Fv N) (κ : KL v Qv (std v)) :
    (repStdFun v Qv κ).map (algebraMap 𝔬 Fv) = (κ : GL (Fin N) Fv).val :=
  (exists_intMat_of_std v ((mem_KL v).mp κ.2).2).choose_spec

/-- **The integral matrix** of $\kappa \in K(\mathfrak o_\mathfrak p^N)$. -/
def repStd (Qv : QuadForm Fv N) : KL v Qv (std v) →* Matrix (Fin N) (Fin N) 𝔬 where
  toFun := repStdFun v Qv
  map_one' := map_o_inj v (by
    show (repStdFun v Qv 1).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [repStdFun_map, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl)
  map_mul' a b := map_o_inj v (by
    show (repStdFun v Qv (a * b)).map _ = (repStdFun v Qv a * repStdFun v Qv b).map _
    rw [repStdFun_map, Matrix.map_mul, repStdFun_map, repStdFun_map]
    rfl)

theorem repStd_map (Qv : QuadForm Fv N) (κ : KL v Qv (std v)) :
    (repStd v Qv κ).map (algebraMap 𝔬 Fv) = (κ : GL (Fin N) Fv).val :=
  repStdFun_map v Qv κ

theorem compMat_repStd {Qv : QuadForm Fv N} {Qo : QuadForm 𝔬 N} (hQo : Qo.map (algebraMap 𝔬 Fv) = Qv)
    (κ : KL v Qv (std v)) : Qo.compMat (repStd v Qv κ) = Qo := by
  apply quadForm_map_o_inj v
  rw [← map_compMat, repStd_map, hQo]
  exact ((mem_KL v).mp κ.2).1

/-- An isometry with integral matrix and integral inverse lies in $K(\mathfrak o_\mathfrak p^N)$. -/
theorem mem_KL_std_of_integral {Qv : QuadForm Fv N} (g : GL (Fin N) Fv) (hg : Qv.compMat g.val = Qv)
    (G₀ G₁ : Matrix (Fin N) (Fin N) 𝔬) (h₀ : G₀.map (algebraMap 𝔬 Fv) = g.val)
    (h₁ : G₁.map (algebraMap 𝔬 Fv) = g⁻¹.val) : g ∈ KL v Qv (std v) := by
  have e01 : G₀ * G₁ = 1 := map_o_inj v (by
    show (G₀ * G₁).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [Matrix.map_mul, h₀, h₁, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel]
    rfl)
  have e10 : G₁ * G₀ = 1 := map_o_inj v (by
    show (G₁ * G₀).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [Matrix.map_mul, h₀, h₁, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, inv_mul_cancel]
    rfl)
  have := locAct_map_std v (⟨G₀, G₁, e01, e10⟩ : GL (Fin N) 𝔬)
  have hg' : Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) (⟨G₀, G₁, e01, e10⟩ : GL (Fin N) 𝔬) = g :=
    Units.ext h₀
  rw [hg'] at this
  exact (mem_KL v).mpr ⟨hg, this⟩

/-- **Every integral isometry of a nondegenerate integral model comes from $K(\mathfrak o_\mathfrak p^N)$.** -/
theorem exists_repStd_eq {Qv : QuadForm Fv N} {Qo : QuadForm 𝔬 N} (hQo : Qo.map (algebraMap 𝔬 Fv) = Qv)
    (hQ : Qo.Nondegenerate) (X : Matrix (Fin N) (Fin N) 𝔬) (hX : Qo.compMat X = Qo) :
    ∃ κ, repStd v Qv κ = X := by
  have hH := congrArg QuadForm.hessian hX
  rw [hessian_compMat] at hH
  have hdet : X.det * X.det * Qo.hessian.det = Qo.hessian.det := by
    have := congrArg Matrix.det hH
    rw [det_mul, det_mul, det_transpose] at this
    linear_combination this
  have hdet1 : X.det * X.det = 1 := by
    have : (X.det * X.det - 1) * Qo.hessian.det = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hQ
  have hu : IsUnit X.det := ⟨⟨X.det, X.det, hdet1, hdet1⟩, rfl⟩
  let P₀ : GL (Fin N) 𝔬 := Matrix.nonsingInvUnit X hu
  let g : GL (Fin N) Fv := Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) P₀
  have hgval : g.val = X.map (algebraMap 𝔬 Fv) := rfl
  have hmem : g ∈ KL v Qv (std v) := by
    refine (mem_KL v).mpr ⟨?_, locAct_map_std v P₀⟩
    rw [hgval, ← hQo, map_compMat, hX]
  refine ⟨⟨g, hmem⟩, map_o_inj v ?_⟩
  show (repStd v Qv ⟨g, hmem⟩).map _ = X.map _
  rw [repStd_map]
  exact hgval

/-- **Conjugation to standard coordinates:** $g \mapsto h^{-1}gh$, $K_{Q_v}(h\,\mathfrak o_\mathfrak p^N) \to K_{Q_v\circ h}(\mathfrak o_\mathfrak p^N)$. -/
def conjStd (Qv : QuadForm Fv N) (h : GL (Fin N) Fv) :
    KL v Qv (locAct v h (std v)) →* KL v (Qv.compMat h.val) (std v) where
  toFun g := ⟨h⁻¹ * g * h, by
    have hg : (g : GL (Fin N) Fv) ∈ (KL v (Qv.compMat h.val) (std v)).map (MulAut.conj h).toMonoidHom := by
      rw [← KL_locAct]; exact g.2
    rw [Subgroup.mem_map_equiv (f := MulAut.conj h), MulAut.conj_symm_apply] at hg
    exact hg⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjStd_val (Qv : QuadForm Fv N) (h : GL (Fin N) Fv) (g : KL v Qv (locAct v h (std v))) :
    ((conjStd v Qv h g : KL v (Qv.compMat h.val) (std v)) : GL (Fin N) Fv) = h⁻¹ * g * h := rfl

/-- **The integral matrix in the coordinates of $\Lambda = h\,\mathfrak o_\mathfrak p^N$**: $\kappa \mapsto h^{-1}\kappa h$. -/
def repAt (Qv : QuadForm Fv N) (h : GL (Fin N) Fv) :
    KL v Qv (locAct v h (std v)) →* Matrix (Fin N) (Fin N) 𝔬 :=
  (repStd v (Qv.compMat h.val)).comp (conjStd v Qv h)

theorem repAt_map (Qv : QuadForm Fv N) (h : GL (Fin N) Fv) (κ : KL v Qv (locAct v h (std v))) :
    (repAt v Qv h κ).map (algebraMap 𝔬 Fv) = (h⁻¹ * κ * h : GL (Fin N) Fv).val := by
  show (repStd v (Qv.compMat h.val) (conjStd v Qv h κ)).map _ = _
  rw [repStd_map, conjStd_val]

theorem integralModel_compMat {Qv : QuadForm Fv N} {Qo : QuadForm 𝔬 N} (hQo : Qo.map (algebraMap 𝔬 Fv) = Qv)
    (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) :
    (Qo.compMat P).map (algebraMap 𝔬 Fv) = Qv.compMat (glOf v P hP).val := by
  rw [glOf_val, ← hQo, map_compMat]

theorem compMat_repAt {Qv : QuadForm Fv N} (h : GL (Fin N) Fv) {Qo : QuadForm 𝔬 N}
    (hQo : Qo.map (algebraMap 𝔬 Fv) = Qv.compMat h.val) (κ : KL v Qv (locAct v h (std v))) :
    Qo.compMat (repAt v Qv h κ) = Qo :=
  compMat_repStd v hQo _

theorem exists_repAt_eq {Qv : QuadForm Fv N} (h : GL (Fin N) Fv) {Qo : QuadForm 𝔬 N}
    (hQo : Qo.map (algebraMap 𝔬 Fv) = Qv.compMat h.val) (hQ : Qo.Nondegenerate)
    (X : Matrix (Fin N) (Fin N) 𝔬) (hX : Qo.compMat X = Qo) :
    ∃ κ, repAt v Qv h κ = X := by
  obtain ⟨κ', hκ'⟩ := exists_repStd_eq v hQo hQ X hX
  have hmem : h * (κ' : GL (Fin N) Fv) * h⁻¹ ∈ KL v Qv (locAct v h (std v)) := by
    rw [KL_locAct]
    exact ⟨κ', κ'.2, rfl⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  have : conjStd v Qv h ⟨_, hmem⟩ = κ' := Subtype.ext (by rw [conjStd_val]; group)
  show repStd v (Qv.compMat h.val) (conjStd v Qv h ⟨_, hmem⟩) = X
  rw [this, hκ']

/-! #### Congruence elements of one stabilizer lie in the other -/

theorem map_mul_glOf_inv {A B : Matrix (Fin N) (Fin N) Fv} (h : GL (Fin N) Fv) (hAB : A * h.val = h.val * B) :
    A = h.val * B * h⁻¹.val := by
  rw [← hAB, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

/-- $P(1 + \pi^cE)P^{-1}$ is integral when $\det P \mid \pi^c$. -/
theorem exists_conj_integral (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) {c : ℕ} (hc : P.det ∣ NF.π v ^ c)
    (E : Matrix (Fin N) (Fin N) 𝔬) :
    ∃ G : Matrix (Fin N) (Fin N) 𝔬, G.map (algebraMap 𝔬 Fv) =
      (glOf v P hP).val * (1 + NF.π v ^ c • E).map (algebraMap 𝔬 Fv) * (glOf v P hP)⁻¹.val := by
  obtain ⟨u, hu⟩ := hc
  refine ⟨1 + P * E * (u • P.adjugate), map_mul_glOf_inv v _ ?_⟩
  rw [glOf_val, ← Matrix.map_mul, ← Matrix.map_mul]
  congr 1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.smul_mul, adjugate_mul,
    smul_smul, mul_comm u, ← hu, Matrix.mul_add, Matrix.mul_one]
  simp only [Matrix.mul_smul, Matrix.mul_one]

/-- $P^{-1}(1 + \pi^cE)P$ is integral when $\det P \mid \pi^c$. -/
theorem exists_conj_integral' (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) {c : ℕ} (hc : P.det ∣ NF.π v ^ c)
    (E : Matrix (Fin N) (Fin N) 𝔬) :
    ∃ G : Matrix (Fin N) (Fin N) 𝔬, G.map (algebraMap 𝔬 Fv) =
      (glOf v P hP)⁻¹.val * (1 + NF.π v ^ c • E).map (algebraMap 𝔬 Fv) * (glOf v P hP).val := by
  obtain ⟨u, hu⟩ := hc
  refine ⟨1 + (u • P.adjugate) * E * P, ?_⟩
  have key : (glOf v P hP).val * (1 + (u • P.adjugate) * E * P).map (algebraMap 𝔬 Fv) =
      (1 + NF.π v ^ c • E).map (algebraMap 𝔬 Fv) * (glOf v P hP).val := by
    rw [glOf_val, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_smul, mul_adjugate,
      smul_smul, mul_comm u, ← hu, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have := congrArg (fun M => (glOf v P hP)⁻¹.val * M) key
  simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
  exact this

/-- An integral matrix $\equiv 1 \bmod \pi^c$ and its inverse: $X^{-1} = 1 + \pi^c E'$. -/
theorem inv_congr_one {R : Type*} [CommRing R] {X Y E : Matrix (Fin N) (Fin N) R} {π : R} {c : ℕ}
    (hYX : Y * X = 1) (hX : X = 1 + π ^ c • E) : Y = 1 + π ^ c • (-(Y * E)) := by
  rw [hX, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at hYX
  rw [smul_neg, ← hYX]; abel

theorem eq_one_add_of_dvd {R : Type*} [CommRing R] {X : Matrix (Fin N) (Fin N) R} {π : R} {c : ℕ}
    (h : ∀ i j, π ^ c ∣ X i j - (1 : Matrix (Fin N) (Fin N) R) i j) : ∃ E, X = 1 + π ^ c • E := by
  choose E hE using h
  refine ⟨Matrix.of E, Matrix.ext fun i j => ?_⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  linear_combination (hE i j)

end LocalGroups

/-! ### REL in the local setting -/

section RelLocal

open NumberField IsDedekindDomain Lattices

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem nondegenerate_compMat {Qo : QuadForm 𝔬 N} (hQo : Qo.Nondegenerate) {P : Matrix (Fin N) (Fin N) 𝔬}
    (hP : P.det ≠ 0) : (Qo.compMat P).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero hP hQo) hP

/-- **REL for $\Lambda_1 = P\mathfrak o_\mathfrak p^N \subseteq \Lambda_2 = \mathfrak o_\mathfrak p^N$** in the local setting: `rel_nearCount` with
$K_1 = K(\Lambda_1)$, $K_2 = K(\Lambda_2)$ acting through their integral matrices (`repAt`, `repStd`). -/
theorem rel_local (Qo : QuadForm 𝔬 N) (hQo : Qo.Nondegenerate) (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0)
    {c : ℕ} (hc : P.det ∣ NF.π v ^ c) {t : 𝔬} (ht : t ≠ 0) {e f : ℕ} (he : NF.π v ^ e ∣ 2 * t)
    (he' : ¬ NF.π v ^ (e + 1) ∣ 2 * t) (hf : NF.π v ^ f ∣ 4 * t) (hf' : ¬ NF.π v ^ (f + 1) ∣ 4 * t)
    (y : Fin N → 𝔬) (hy : (Qo.compMat P).eval y = t) {k r : ℕ} (hr : f + 1 + c ≤ r) (hk : r + c + e ≤ k)
    (hk2 : 2 * e + 1 ≤ k) :
    nearCount (Qo.compMat P) (NF.π v) t k r
        (orbitOf (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP)) ⊤ y) *
        ((KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)).subgroupOf
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)))).relIndex
          (stabOf (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP)) y) *
        (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v))).relIndex
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)) =
      Nat.card (redMat (NF.π v) k P).ker *
        (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)).relIndex
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v))) *
        nearCount Qo (NF.π v) t k r (orbitOf (repStd v (Qo.map (algebraMap 𝔬 Fv))) ⊤ (P *ᵥ y)) *
        ((KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v))).subgroupOf
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v))).relIndex
          (stabOf (repStd v (Qo.map (algebraMap 𝔬 Fv))) (P *ᵥ y)) := by
  set Qv := Qo.map (algebraMap 𝔬 Fv)
  set h := glOf v P hP
  set K₁ := KL v Qv (locAct v h (std v))
  set K₂ := KL v Qv (std v)
  have hπ := NF.irreducible_π v
  have hQ₁ : (Qo.compMat P).map (algebraMap 𝔬 Fv) = Qv.compMat h.val := integralModel_compMat v rfl P hP
  have hQ₁nd := nondegenerate_compMat v hQo hP
  refine rel_nearCount K₁ K₂ (repAt v Qv h) (repStd v Qv) hπ Qo P hP (exists_mulVec_eq_smul P hc)
    (compMat_repAt v h hQ₁) (compMat_repStd v rfl) (exists_repAt_eq v h hQ₁ hQ₁nd)
    (exists_repStd_eq v rfl hQo) ?_ ?_ ?_ ht he he' hf hf' y hy hr hk hk2
  · -- compatibility
    intro g h₁ h₂
    apply map_o_inj v
    show (P * repAt v Qv h ⟨g, h₁⟩).map _ = (repStd v Qv ⟨g, h₂⟩ * P).map _
    rw [Matrix.map_mul, Matrix.map_mul, repAt_map, repStd_map, ← glOf_val v P hP]
    simp only [Units.val_mul, ← Matrix.mul_assoc]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  · -- congruence elements of `K₁` lie in `K₂`
    intro κ hκ
    obtain ⟨E, hE⟩ := eq_one_add_of_dvd hκ
    obtain ⟨E', hE'⟩ : ∃ E', repAt v Qv h κ⁻¹ = 1 + NF.π v ^ c • E' :=
      ⟨_, inv_congr_one (by rw [← map_mul, inv_mul_cancel, map_one]) hE⟩
    obtain ⟨G₀, hG₀⟩ := exists_conj_integral v P hP hc E
    obtain ⟨G₁, hG₁⟩ := exists_conj_integral v P hP hc E'
    have hκv : ∀ κ' : K₁, (κ' : GL (Fin N) Fv).val = h.val * (repAt v Qv h κ').map (algebraMap 𝔬 Fv) * h⁻¹.val := by
      intro κ'
      rw [repAt_map]
      simp only [Units.val_mul, ← Matrix.mul_assoc]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine mem_KL_std_of_integral v _ ((mem_KL v).mp κ.2).1 G₀ G₁ ?_ ?_
    · rw [hG₀, ← hE, ← hκv]
    · rw [hG₁, ← hE', ← hκv]; rfl
  · -- congruence elements of `K₂` lie in `K₁`
    intro κ hκ
    obtain ⟨E, hE⟩ := eq_one_add_of_dvd hκ
    obtain ⟨E', hE'⟩ : ∃ E', repStd v Qv κ⁻¹ = 1 + NF.π v ^ c • E' :=
      ⟨_, inv_congr_one (by rw [← map_mul, inv_mul_cancel, map_one]) hE⟩
    obtain ⟨G₀, hG₀⟩ := exists_conj_integral' v P hP hc E
    obtain ⟨G₁, hG₁⟩ := exists_conj_integral' v P hP hc E'
    have hκQ : Qv.compMat (κ : GL (Fin N) Fv).val = Qv := ((mem_KL v).mp κ.2).1
    have hmem : h⁻¹ * (κ : GL (Fin N) Fv) * h ∈ KL v (Qv.compMat h.val) (std v) := by
      refine mem_KL_std_of_integral v _ ?_ G₀ G₁ ?_ ?_
      · have e1 : h.val * (h⁻¹ * (κ : GL (Fin N) Fv) * h).val = (κ : GL (Fin N) Fv).val * h.val := by
          rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
        rw [compMat_mul, e1, ← compMat_mul, hκQ]
      · rw [hG₀, ← hE, repStd_map]; simp only [Units.val_mul]; rfl
      · rw [hG₁, ← hE', repStd_map]
        simp only [Units.val_mul, _root_.mul_inv_rev, inv_inv, InvMemClass.coe_inv, Matrix.mul_assoc]; rfl
    have : (κ : GL (Fin N) Fv) ∈ KL v Qv (locAct v h (std v)) := by
      rw [KL_locAct]
      refine ⟨_, hmem, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact this

end RelLocal

end QuadFormsKB.Tamagawa
