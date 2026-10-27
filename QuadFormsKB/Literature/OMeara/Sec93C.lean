/-
# O'Meara §93B: changing a splitting $L = A(\alpha, 0) \perp K$ (93:12, 93:13)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`. O'Meara works over a dyadic local field; the arguments
below use only the discrete valuation ring.

**Proves**
* `exists_isOrthSum_shift` (**93:12**, p. 256, in the scaled form used for 93:13): if $L = J \perp K$ with
  $J = \mathfrak ox + \mathfrak oy$ of matrix $\xi A(\alpha, 0)$ and $z \in K^{\xi\mathfrak o}$, then
  $J' = \mathfrak o(x + z) + \mathfrak oy$ splits $L = J' \perp K'$ with $K' \cong K$ (O'Meara's isometry
  $\varphi u = u - \xi^{-1}B(u, z)y$; here $K' = \varphi K$ is checked directly instead of by volumes);
* `exists_isOrthSum_matA` (**93:13**, p. 256): $L = \xi A(\alpha, 0) \perp K$ gives
  $L \cong \xi A(\alpha + \xi^{-1}\beta, 0) \perp K$ for every $\beta \in \mathfrak g K^{\xi\mathfrak o}$.
-/
import QuadFormsKB.Literature.OMeara.Sec91Chain
import QuadFormsKB.Literature.OMeara.Sec92

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- **The complement of a regular component is unique** (O'Meara 1963, §82D, p. 226): if $L = J \perp K$ with $J$
regular then $K = \{x \in L : B(x, J) = 0\}$. -/
@[kb "omeara1963" "§82D, p. 226 (K = {x ∈ J | B(x, L) = 0} is determined by J and L)"]
theorem IsOrthSum.eq_splitComp {L J K : Submodule R V} (h : IsOrthSum Q L J K) (hJ : IsRegular Q J) :
    K = splitComp Q L J := by
  apply le_antisymm
  · intro k hk
    exact ⟨h.sup_eq ▸ mem_sup_right hk, fun j hj => by rw [bil_comm]; exact h.orth j hj k hk⟩
  · rintro w ⟨hwL, hwJ⟩
    rw [← h.sup_eq] at hwL
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hwL
    have hj0 : j = 0 := hJ j hj fun j' hj' => by
      have := hwJ j' hj'
      rw [bil_add_left, bil_comm Q k j', h.orth j' hj' k hk, add_zero] at this
      exact this
    rw [hj0, zero_add]; exact hk

/-- **Proposition 93:12** (O'Meara 1963, p. 256), scaled by $\xi$ as in 93:13: let $L = J \perp K$ where $J$ has a base
$x, y$ with $Q(x) = \xi\alpha$, $B(x, y) = \xi$, $Q(y) = 0$ ($J \cong \xi A(\alpha, 0)$, $\alpha \in \mathfrak o$,
$\xi \ne 0$), and let $z \in K^{\xi\mathfrak o}$, i.e. $z \in K$ with $B(z, K) \subseteq \xi\mathfrak o$. Then
$J' = \mathfrak o(x + z) + \mathfrak oy$ splits $L = J' \perp K'$ (with $K' = \{w \in L : B(w, J') = 0\}$) and
$K' \cong K$. (O'Meara states the case $\xi = 1$; the scaled case is how 93:13 is obtained "by scaling".) -/
@[kb "omeara1963" "§93B, 93:12, p. 256"]
theorem exists_isOrthSum_shift {L J K : Submodule R V} (hs : IsOrthSum Q L J K) {x y z : V} {ξ : F} (hξ : ξ ≠ 0)
    {α : R} (hJ : J = span R {x, y}) (hQx : Q x = ξ * algebraMap R F α) (hxy : bil Q x y = ξ) (hQy : Q y = 0)
    (hzK : z ∈ K) (hz : ∀ k ∈ K, bil Q z k ∈ R ∙ ξ) :
    IsOrthSum Q L (span R {x + z, y}) (splitComp Q L (span R {x + z, y})) ∧
      IsometricLat Q Q K (splitComp Q L (span R {x + z, y})) := by
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hyJ : y ∈ J := hJ ▸ subset_span (by simp)
  have hJL : J ≤ L := hs.sup_eq ▸ le_sup_left
  have hKL : K ≤ L := hs.sup_eq ▸ le_sup_right
  have hxz : bil Q x z = 0 := hs.orth x hxJ z hzK
  have hyz : bil Q y z = 0 := hs.orth y hyJ z hzK
  have hyk : ∀ k ∈ K, bil Q y k = 0 := fun k hk => hs.orth y hyJ k hk
  have hxk : ∀ k ∈ K, bil Q x k = 0 := fun k hk => hs.orth x hxJ k hk
  -- coefficients `B(k, z)/ξ` lie in `R`
  choose c hc using fun k : K => mem_span_singleton.mp (hz k k.2)
  -- the matrix of `x + z, y` is `ξ A(α + Q(z)/ξ, 0)`; `Q z ∈ ξ o`
  have hzz : Q z ∈ R ∙ ξ := by rw [← bil_self]; exact hz z hzK
  obtain ⟨q, hq⟩ := mem_span_singleton.mp hzz
  set J' := span R {x + z, y} with hJ'
  have hJ'L : J' ≤ L := by
    rw [hJ', span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact L.add_mem (hJL hxJ) (hKL hzK)
    · exact hJL hyJ
  let v : Fin 2 → V := ![x + z, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![α + q, 1; 1, 0]
  have hG : gram Q v = ξ • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, bil_add_left, bil_add_right, bil_self, Q_add, hQx, hxy, hQy, hxz, hyz, bil_comm Q y x,
        bil_comm Q z x, bil_comm Q y z, bil_comm Q z y, ← hq, Algebra.smul_def] <;> ring
  have hU : IsUnit U.det := by simp [U, Matrix.det_fin_two_of]
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q hξ hU hG
  have hv : Set.range v = {x + z, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv] at hmod
  -- `B(J', L) ⊆ ξ o`
  have hxj : ∀ j ∈ J, bil Q x j ∈ R ∙ ξ := by
    intro j hj
    rw [hJ] at hj
    obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hj
    rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, bil_self, hQx, hxy]
    exact add_mem (mem_span_singleton.mpr ⟨a * α, by rw [Algebra.smul_def, map_mul]; ring⟩)
      (mem_span_singleton.mpr ⟨b, by rw [Algebra.smul_def]⟩)
  have hyj : ∀ j ∈ J, bil Q y j ∈ R ∙ ξ := by
    intro j hj
    rw [hJ] at hj
    obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hj
    rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, bil_self, hQy, bil_comm Q y x, hxy]
    exact mem_span_singleton.mpr ⟨a, by rw [Algebra.smul_def]; ring⟩
  have hgen : ∀ w ∈ ({x + z, y} : Set V), ∀ l ∈ L, bil Q w l ∈ R ∙ ξ := by
    intro w hw l hl
    rw [← hs.sup_eq] at hl
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · rw [bil_add_left, bil_add_right, bil_add_right, hxk k hk]
      have hzj : bil Q z j = 0 := by rw [bil_comm]; exact hs.orth j hj z hzK
      rw [hzj, add_zero, zero_add]
      exact add_mem (hxj j hj) (hz k hk)
    · rw [bil_add_right, hyk k hk, add_zero]; exact hyj j hj
  have hBJ'L : ∀ w ∈ J', ∀ l ∈ L, bil Q w l ∈ R ∙ ξ := by
    intro w hw l hl
    refine span_induction (p := fun w _ => bil Q w l ∈ R ∙ ξ) (fun w hw => hgen w hw l hl)
      (by simp [bil]) (fun a b _ _ ha hb => by rw [bil_add_left]; exact add_mem ha hb)
      (fun r a _ ha => by rw [bil_rsmul_left, ← Algebra.smul_def]; exact smul_mem _ r ha) hw
  have hsplit : IsOrthSum Q L J' (splitComp Q L J') := by
    obtain ⟨K'', hK''⟩ := (splits_iff_of_isModular Q hJ'L hmod (fg_span (by simp))).mpr hBJ'L
    rwa [IsOrthSum.eq_splitComp Q hK'' (hmod.isRegular Q (fg_span (by simp)))] at hK''
  refine ⟨hsplit, ?_⟩
  -- O'Meara's isometry `φ u = u - ξ⁻¹ B(z, u) y`
  let t : V → F := fun u => ξ⁻¹ * bil Q z u
  have ht : ∀ k ∈ K, ∃ r : R, t k = algebraMap R F r := by
    intro k hk
    obtain ⟨r, hr⟩ := mem_span_singleton.mp (hz k hk)
    exact ⟨r, by simp only [t]; rw [← hr, Algebra.smul_def]; field_simp⟩
  let φ : V →ₗ[R] V := LinearMap.id - ((ξ⁻¹ • QuadraticMap.associated Q z).smulRight y).restrictScalars R
  have hφ : ∀ u, φ u = u - t u • y := by
    intro u; simp [φ, t, bil, LinearMap.smul_apply, smul_smul]
  have hφK : ∀ k ∈ K, φ k ∈ splitComp Q L J' := by
    intro k hk
    obtain ⟨r, hr⟩ := ht k hk
    refine ⟨?_, fun w hw => ?_⟩
    · rw [hφ, hr, algebraMap_smul]; exact L.sub_mem (hKL hk) (L.smul_mem r (hJL hyJ))
    · refine bil_eq_zero_of_mem_span Q (z := ![x + z, y]) ?_ (by
        rw [show Set.range ![x + z, y] = {x + z, y} from hv]; exact hw)
      intro i
      fin_cases i
      · show bil Q (φ k) (x + z) = 0
        rw [hφ, bil_sub_left, bil_add_right, bil_add_right, bil_smul_left, bil_smul_left, bil_comm Q k x,
          hxk k hk, bil_comm Q y x, hxy, hyz, bil_comm Q k z]
        simp only [t]; field_simp; ring
      · show bil Q (φ k) y = 0
        rw [hφ, bil_sub_left, bil_smul_left, bil_self, hQy, bil_comm Q k y, hyk k hk]; ring
  let f : K →ₗ[R] splitComp Q L J' :=
    (φ.comp K.subtype).codRestrict _ fun k => show (φ.comp K.subtype) k ∈ _ from hφK k.1 k.2
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : φ (a - b : V) = 0 := by
      have := congrArg Subtype.val hab
      change φ a = φ b at this
      rw [map_sub, this, sub_self]
    rw [hφ] at h1
    have hab' : ((a - b : K) : V) ∈ J ⊓ K := by
      refine ⟨?_, (a - b).2⟩
      obtain ⟨r, hr⟩ := ht _ (a - b).2
      have : ((a - b : K) : V) = t (a - b : K) • y := sub_eq_zero.mp (by simpa using h1)
      rw [this, hr, algebraMap_smul]; exact J.smul_mem r hyJ
    rw [hs.disjoint.eq_bot, mem_bot] at hab'
    exact sub_eq_zero.mp (Subtype.ext (by simpa using hab'))
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hwL, hwJ'⟩
    have hwL' := hwL
    rw [← hs.sup_eq] at hwL'
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hwL'
    rw [hJ] at hj
    obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hj
    have hy' := hwJ' y (subset_span (by simp))
    rw [bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, hxy, bil_self, hQy, mul_zero, add_zero,
      bil_comm Q k y, hyk k hk, add_zero] at hy'
    have ha : a = 0 := by
      have : algebraMap R F a = 0 := (mul_eq_zero.mp hy').resolve_right hξ
      exact (IsFractionRing.injective R F) (this.trans (map_zero _).symm)
    subst ha
    have hx' := hwJ' (x + z) (subset_span (by simp))
    rw [zero_smul, zero_add, bil_add_left, bil_add_right, bil_add_right, bil_rsmul_left, bil_rsmul_left,
      bil_comm Q y x, hxy, hyz, bil_comm Q k x, hxk k hk, bil_comm Q k z] at hx'
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    change φ k = 0 • x + b • y + k
    rw [zero_smul, zero_add, hφ]
    have : t k = -algebraMap R F b := by
      simp only [t]; field_simp; linear_combination hx'
    rw [this, neg_smul, sub_neg_eq_add, add_comm, algebraMap_smul]
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun u => ?_⟩
  change Q (φ u) = Q u
  rw [hφ, sub_eq_add_neg, Q_add, ← neg_smul, QuadraticMap.map_smul, bil_smul_right, hQy,
    bil_comm, hyk u u.2]
  simp

/-- **Example 93:13** (O'Meara 1963, p. 256): if $L = J \perp K$ with $J \cong \xi A(\alpha, 0)$ ($\xi \ne 0$,
$\alpha \in \mathfrak o$) and $\beta \in \mathfrak g K^{\xi\mathfrak o}$, i.e. $\beta = Q(z) + 2c$ with $z \in K^{\xi\mathfrak o}$
and $c \in \mathfrak s K^{\xi\mathfrak o}$, then $L = J' \perp K'$ with $J' \cong \xi A(\alpha + \xi^{-1}\beta, 0)$ and
$K' \cong K$: $L \cong \langle\xi A(\alpha + \xi^{-1}\beta, 0)\rangle \perp K$. -/
@[kb "omeara1963" "§93B, 93:13, p. 256"]
theorem exists_isOrthSum_matA {L J K : Submodule R V} (hs : IsOrthSum Q L J K) {x y : V} {ξ : F} (hξ : ξ ≠ 0)
    {α : R} (hJ : J = span R {x, y}) (hQx : Q x = ξ * algebraMap R F α) (hxy : bil Q x y = ξ) (hQy : Q y = 0)
    {z : V} (hz : z ∈ subA Q (R ∙ ξ) K) {c : F} (hc : c ∈ scale Q (subA Q (R ∙ ξ) K)) :
    ∃ x' y' : V, ∃ α' : R, algebraMap R F α' = algebraMap R F α + ξ⁻¹ * (Q z + 2 * c) ∧
      Q x' = ξ * algebraMap R F α' ∧ bil Q x' y' = ξ ∧ Q y' = 0 ∧
      IsOrthSum Q L (span R {x', y'}) (splitComp Q L (span R {x', y'})) ∧
      IsometricLat Q Q K (splitComp Q L (span R {x', y'})) := by
  obtain ⟨hzK, hzB⟩ := hz
  obtain ⟨h1, h2⟩ := exists_isOrthSum_shift Q hs hξ hJ hQx hxy hQy hzK hzB
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hyJ : y ∈ J := hJ ▸ subset_span (by simp)
  have hxz : bil Q x z = 0 := hs.orth x hxJ z hzK
  have hyz : bil Q y z = 0 := hs.orth y hyJ z hzK
  obtain ⟨q, hq⟩ := mem_span_singleton.mp (by rw [← bil_self]; exact hzB z hzK : Q z ∈ R ∙ ξ)
  obtain ⟨γ, hγ⟩ := mem_span_singleton.mp (scale_subA_le Q (R ∙ ξ) K hc)
  have hspan : span R {x + z + γ • y, y} = span R {x + z, y} := by
    apply le_antisymm <;> rw [span_le] <;> intro w hw <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw <;> rcases hw with rfl | rfl
    · exact add_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))
    · exact subset_span (by simp)
    · have : x + z = (x + z + γ • y) - γ • y := by abel
      rw [this]; exact sub_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))
    · exact subset_span (by simp)
  refine ⟨x + z + γ • y, y, α + q + 2 * γ, ?_, ?_, ?_, hQy, ?_, ?_⟩
  · rw [← hq, ← hγ, Algebra.smul_def, Algebra.smul_def]; simp only [map_add, map_mul, map_ofNat]
    field_simp; ring
  · have e1 : bil Q (x + z) (γ • y) = algebraMap R F γ * ξ := by
      rw [bil_rsmul_right, bil_add_left, hxy, bil_comm Q z y, hyz, add_zero]
    rw [Q_add, e1, Q_add, hxz, Q_rsmul, hQy, hQx, ← hq, Algebra.smul_def]
    simp only [map_add, map_mul, map_ofNat]; ring
  · rw [bil_add_left, bil_add_left, bil_rsmul_left, hxy, bil_comm Q z y, hyz, bil_self, hQy]; ring
  · rw [hspan]; exact h1
  · rw [hspan]; exact h2

/-- Transitivity of `IsometricLat` (composition of the linear equivalences). -/
theorem isometricLat_trans_aux {L K M : Submodule R V} (h1 : IsometricLat Q Q L K)
    (h2 : IsometricLat Q Q K M) : IsometricLat Q Q L M := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨f.trans g, fun x => by rw [LinearEquiv.trans_apply, hg, hf]⟩

/-- Vectors $x, y$ with $Q(x) = Q(y) = 0$, $B(x, y) = 1$ span a unimodular lattice. -/
theorem isModular_hyp {x y : V} (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) :
    IsModular Q 1 (span R {x, y}) := by
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
  have hG : gram Q v = (1 : F) • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hQy, hxy, bil_comm Q y x]
  have hU : IsUnit U.det := by simp [U, Matrix.det_fin_two_of]
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q one_ne_zero hU hG
  have hv : Set.range v = {x, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv, ← Submodule.one_eq_span] at hmod
  exact hmod

/-- A hyperbolic splitting component lies in $L^{\mathfrak o}$ (O'Meara p. 256). -/
theorem hyp_le_subA {L J K : Submodule R V} (h : IsOrthSum Q L J K) {x y : V}
    (hJ : J = span R {x, y}) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) :
    J ≤ subA Q 1 L := by
  intro w hw
  have hJL : J ≤ L := h.sup_eq ▸ le_sup_left
  refine ⟨hJL hw, fun l hl => ?_⟩
  rw [← h.sup_eq] at hl
  obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hl
  rw [bil_add_right, h.orth w hw k hk, add_zero]
  rw [hJ] at hw hj
  obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hw
  obtain ⟨c, d, rfl⟩ := mem_span_pair.mp hj
  refine Submodule.mem_one.mpr ⟨a * d + b * c, ?_⟩
  simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, bil_self, hQx, hQy, hxy,
    bil_comm Q y x]
  simp only [map_add, map_mul]
  ring

/-- Shifting the first base vector of a pair by a multiple of the second. -/
theorem span_pair_shift (a : R) (x y : V) : span R {y + a • x, x} = span R {x, y} := by
  apply le_antisymm <;> rw [span_le] <;> intro w hw <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw <;> rcases hw with rfl | rfl
  · exact add_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))
  · exact subset_span (by simp)
  · exact subset_span (by simp)
  · have : w = (w + a • x) - a • x := by abel
    rw [this]; exact sub_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))

/-- **Step 2** of O'Meara's proof of 93:14: two hyperbolic splittings sharing the first base vector $x$ have
isometric complements (an application of 93:12). -/
theorem isometricLat_of_common_hyperbolic {L J K J' K' : Submodule R V} (h : IsOrthSum Q L J K)
    (h' : IsOrthSum Q L J' K') {x y y' : V} (hJ : J = span R {x, y}) (hJ' : J' = span R {x, y'})
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) (hQy' : Q y' = 0)
    (hxy' : bil Q x y' = 1) : IsometricLat Q Q K K' := by
  have hreg : IsRegular Q J' := by
    rw [hJ']; exact (isModular_hyp Q hQx hQy' hxy').isRegular Q (fg_span (Set.toFinite _))
  have hJ'o := hyp_le_subA Q h' hJ' hQx hQy' hxy'
  have hy'J' : y' ∈ J' := hJ' ▸ subset_span (by simp)
  have hy'L : y' ∈ L := h'.sup_eq ▸ mem_sup_left hy'J'
  rw [← h.sup_eq] at hy'L
  obtain ⟨j, hj, k, hk, hjk⟩ := mem_sup.mp hy'L
  have hj' := hj
  rw [hJ] at hj'
  obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hj'
  have hxk : ∀ k' ∈ K, bil Q x k' = 0 := fun k' hk' => h.orth x (hJ ▸ subset_span (by simp)) k' hk'
  have hyk : ∀ k' ∈ K, bil Q y k' = 0 := fun k' hk' => h.orth y (hJ ▸ subset_span (by simp)) k' hk'
  have hb : b = 1 := by
    have h1 : bil Q x y' = algebraMap R F b := by
      rw [← hjk]
      simp only [bil_add_right, bil_rsmul_right, hxy, bil_self, hQx, hxk k hk]
      ring
    rw [hxy'] at h1
    exact (IsFractionRing.injective R F (by rw [map_one]; exact h1.symm))
  subst hb
  have hyeq : y + a • x + k = y' := by rw [← hjk, one_smul]; abel
  obtain ⟨h1, h2⟩ := exists_isOrthSum_shift Q h (x := y + a • x) (y := x) (z := k) (ξ := 1) one_ne_zero
    (α := 2 * a) (by rw [hJ, span_pair_shift]) (by
      rw [Q_add, Q_rsmul, hQy, hQx, bil_rsmul_right, bil_comm Q y x, hxy]
      simp only [map_mul, map_ofNat, one_mul]; ring)
    (by rw [bil_add_left, bil_rsmul_left, bil_self, hQx, bil_comm Q y x, hxy]; ring) hQx hk (by
      intro k' hk'
      rw [← Submodule.one_eq_span]
      have hk'L : k' ∈ L := h.sup_eq ▸ mem_sup_right hk'
      have := (hJ'o hy'J').2 k' hk'L
      rw [← hyeq, bil_add_left, bil_add_left, bil_rsmul_left, hxk k' hk', hyk k' hk'] at this
      simpa using this)
  rw [hyeq] at h1 h2
  have e : span R {y', x} = J' := by rw [hJ', Set.pair_comm]
  rw [e] at h2
  rw [IsOrthSum.eq_splitComp Q h' hreg]
  exact h2

/-- A hyperbolic pair in $L^{\mathfrak o}$ spans a unimodular sublattice, which splits $L$ (82:15). -/
theorem exists_isOrthSum_span_hyp {L : Submodule R V} {x z : V} (hx : x ∈ subA Q 1 L)
    (hz : z ∈ subA Q 1 L) (hQx : Q x = 0) (hQz : Q z = 0) (hxz : bil Q x z = 1) :
    ∃ K'', IsOrthSum Q L (span R {x, z}) K'' := by
  have hle : span R {x, z} ≤ subA Q 1 L := by
    rw [span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw <;> rw [hw]
    · exact hx
    · exact hz
  exact (splits_iff_of_isModular Q (fun w hw => (hle hw).1) (isModular_hyp Q hQx hQz hxz)
    (fg_span (Set.toFinite _))).mpr (fun w hw l hl => (hle hw).2 l hl)

/-- $1 + m$ is a unit for $m$ in the maximal ideal. -/
theorem isUnit_one_add_aux {m : R} (hm : m ∈ maximalIdeal R) : IsUnit (1 + m) := by
  have := isUnit_one_sub_self_of_mem_nonunits (-m) ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hm))
  simpa [sub_neg_eq_add] using this

/-- **Step 3** of O'Meara's proof of 93:14: if $B(x, y')$ is a unit, then $K \cong K'$. -/
theorem isometricLat_of_unit_hyperbolic {L J K J' K' : Submodule R V} (h : IsOrthSum Q L J K)
    (h' : IsOrthSum Q L J' K') {x y x' y' : V} (hJ : J = span R {x, y}) (hJ' : J' = span R {x', y'})
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) (hQx' : Q x' = 0) (hQy' : Q y' = 0)
    (hxy' : bil Q x' y' = 1) {r : R} (hr : IsUnit r) (hrb : bil Q x y' = algebraMap R F r) :
    IsometricLat Q Q K K' := by
  obtain ⟨ri, hri⟩ := hr.exists_left_inv
  have hrF : algebraMap R F ri * algebraMap R F r = 1 := by rw [← map_mul, hri, map_one]
  obtain ⟨y'', hy''⟩ : ∃ y'', y'' = ri • y' := ⟨_, rfl⟩
  obtain ⟨x'', hx''⟩ : ∃ x'', x'' = r • x' := ⟨_, rfl⟩
  have hQy'' : Q y'' = 0 := by rw [hy'', Q_rsmul, hQy', mul_zero]
  have hQx'' : Q x'' = 0 := by rw [hx'', Q_rsmul, hQx', mul_zero]
  have hxy'' : bil Q x y'' = 1 := by rw [hy'', bil_rsmul_right, hrb, hrF]
  have hx''y'' : bil Q x'' y'' = 1 := by
    rw [hx'', hy'', bil_rsmul_left, bil_rsmul_right, hxy', mul_one, mul_comm, hrF]
  have hspan : span R {x'', y''} = J' := by
    rw [hJ']
    apply le_antisymm
    · rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw <;> rw [hw]
      · rw [hx'']; exact smul_mem _ _ (subset_span (by simp))
      · rw [hy'']; exact smul_mem _ _ (subset_span (by simp))
    · rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw <;> rw [hw]
      · have : x' = ri • x'' := by rw [hx'', smul_smul, hri, one_smul]
        rw [this]; exact smul_mem _ _ (subset_span (by simp))
      · have : y' = r • y'' := by rw [hy'', smul_smul, mul_comm, hri, one_smul]
        rw [this]; exact smul_mem _ _ (subset_span (by simp))
  have hJo := hyp_le_subA Q h hJ hQx hQy hxy
  have hJ'o := hyp_le_subA Q h' hJ' hQx' hQy' hxy'
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hy''J' : y'' ∈ J' := by rw [hy'']; exact smul_mem _ _ (hJ' ▸ subset_span (by simp))
  obtain ⟨K'', hK''⟩ := exists_isOrthSum_span_hyp Q (hJo hxJ) (hJ'o hy''J') hQx hQy'' hxy''
  refine isometricLat_trans_aux Q (isometricLat_of_common_hyperbolic Q h hK'' hJ rfl hQx hQy hxy hQy'' hxy'')
    (isometricLat_of_common_hyperbolic Q (J := span R {x, y''}) hK'' h' (x := y'') (y := x) (y' := x'')
      (by rw [Set.pair_comm]) (by rw [← hspan, Set.pair_comm]) hQy'' hQx (by rw [bil_comm]; exact hxy'')
      hQx'' (by rw [bil_comm]; exact hx''y''))

/-- **Hyperbolic lattice** $J = \xi_1A(0,0) \perp \cdots \perp \xi_rA(0,0)$ (O'Meara 1963, §93C, p. 257, the lattices
used in a hyperbolic adjunction): $J$ is spanned by $x_1, y_1, \dots, x_r, y_r$ with $Q(x_i) = Q(y_i) = 0$,
$B(x_i, y_i) = \xi_i$, and the planes $\mathfrak ox_i + \mathfrak oy_i$ pairwise orthogonal. It is an
$\mathfrak a$-modular hyperbolic lattice when every $\xi_i\mathfrak o = \mathfrak a$ (`IsModularHyperbolic`). (The
adjunction itself, passing to a larger space $W = U \perp V$, is not formalized.) -/
@[kb "omeara1963" "§93C, p. 257 (hyperbolic adjunction: J = ξ₁A(0,0) ⊥ ⋯ ⊥ ξ_rA(0,0))"]
def IsHyperbolicLattice (J : Submodule R V) {r : ℕ} (ξ : Fin r → F) : Prop :=
  ∃ x y : Fin r → V, span R (Set.range x ∪ Set.range y) = J ∧
    (∀ i, Q (x i) = 0 ∧ Q (y i) = 0 ∧ bil Q (x i) (y i) = ξ i) ∧
    ∀ i j, i ≠ j → bil Q (x i) (x j) = 0 ∧ bil Q (x i) (y j) = 0 ∧ bil Q (y i) (y j) = 0

/-- **$\mathfrak a$-modular hyperbolic lattice** (O'Meara 1963, §93C, p. 257): $J = \xi_1A(0,0) \perp \cdots \perp
\xi_rA(0,0)$ with $\xi_i\mathfrak o = \mathfrak a$ for every $i$. -/
@[kb "omeara1963" "§93C, p. 257 (a-modular hyperbolic adjunction)"]
def IsModularHyperbolic (a : Submodule R F) (J : Submodule R V) : Prop :=
  ∃ r, ∃ ξ : Fin r → F, (∀ i, R ∙ ξ i = a) ∧ IsHyperbolicLattice Q J ξ

/-- **Theorem 93:14** (O'Meara 1963, p. 256): cancellation of a unimodular hyperbolic plane. If a lattice $L$ has
splittings $L = J \perp K$ and $L = J' \perp K'$ with $J \cong J' \cong A(0,0)$ (bases $x, y$ and $x', y'$ with
$Q(x) = Q(y) = Q(x') = Q(y') = 0$, $B(x, y) = B(x', y') = 1$), then $K \cong K'$. (O'Meara's dyadic local field and
regular ambient space are not needed for the argument.) -/
@[kb "omeara1963" "§93C, 93:14, p. 256"]
theorem isometricLat_of_cancel_hyperbolic {L J K J' K' : Submodule R V} (h : IsOrthSum Q L J K)
    (h' : IsOrthSum Q L J' K') {x y x' y' : V} (hJ : J = span R {x, y}) (hJ' : J' = span R {x', y'})
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) (hQx' : Q x' = 0) (hQy' : Q y' = 0)
    (hxy' : bil Q x' y' = 1) : IsometricLat Q Q K K' := by
  have hJo := hyp_le_subA Q h hJ hQx hQy hxy
  have hJ'o := hyp_le_subA Q h' hJ' hQx' hQy' hxy'
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hyJ : y ∈ J := hJ ▸ subset_span (by simp)
  have hx'J' : x' ∈ J' := hJ' ▸ subset_span (by simp)
  have hy'J' : y' ∈ J' := hJ' ▸ subset_span (by simp)
  have hprod : ∀ u ∈ J, ∀ v ∈ J', ∃ r : R, bil Q u v = algebraMap R F r := fun u hu v hv =>
    (Submodule.mem_one.mp ((hJo hu).2 v (h'.sup_eq ▸ mem_sup_left hv))).imp fun r hr => hr.symm
  obtain ⟨a1, ha1⟩ := hprod x hxJ x' hx'J'
  obtain ⟨a2, ha2⟩ := hprod x hxJ y' hy'J'
  obtain ⟨a3, ha3⟩ := hprod y hyJ x' hx'J'
  obtain ⟨a4, ha4⟩ := hprod y hyJ y' hy'J'
  have hJf : J = span R {y, x} := by rw [hJ, Set.pair_comm]
  have hJ'f : J' = span R {y', x'} := by rw [hJ', Set.pair_comm]
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  have hy'x' : bil Q y' x' = 1 := by rw [bil_comm]; exact hxy'
  by_cases c2 : IsUnit a2
  · exact isometricLat_of_unit_hyperbolic Q h h' hJ hJ' hQx hQy hxy hQx' hQy' hxy' c2 ha2
  by_cases c1 : IsUnit a1
  · exact isometricLat_of_unit_hyperbolic Q h h' hJ hJ'f hQx hQy hxy hQy' hQx' hy'x' c1 ha1
  by_cases c3 : IsUnit a3
  · exact isometricLat_of_unit_hyperbolic Q h h' hJf hJ'f hQy hQx hyx hQy' hQx' hy'x' c3 ha3
  by_cases c4 : IsUnit a4
  · exact isometricLat_of_unit_hyperbolic Q h h' hJf hJ' hQy hQx hyx hQx' hQy' hxy' c4 ha4
  -- step 4: all four products lie in the maximal ideal
  have n1 : a1 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr c1)
  have n2 : a2 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr c2)
  have n3 : a3 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr c3)
  have n4 : a4 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr c4)
  obtain ⟨wi, hwi⟩ := (isUnit_one_add_aux n2).exists_left_inv
  have e1 : algebraMap R F wi * (1 + algebraMap R F a2) = 1 := by
    have := congrArg (algebraMap R F) hwi
    simpa [map_mul, map_add] using this
  obtain ⟨y'', hy''⟩ : ∃ y'', y'' = wi • (y + y') + (-(wi * a4 * wi)) • x := ⟨_, rfl⟩
  have hBxv : bil Q x (y + y') = 1 + algebraMap R F a2 := by rw [bil_add_right, hxy, ha2]
  have hBvx : bil Q (y + y') x = 1 + algebraMap R F a2 := by rw [bil_comm]; exact hBxv
  have hQv : Q (y + y') = 2 * algebraMap R F a4 := by
    rw [Q_add, hQy, hQy', ha4]; ring
  have hQy'' : Q y'' = 0 := by
    rw [hy'', Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, hBvx, hQv, hQx]
    simp only [map_neg, map_mul]
    linear_combination (-2 * algebraMap R F wi ^ 2 * algebraMap R F a4) * e1
  have hxy'' : bil Q x y'' = 1 := by
    rw [hy'', bil_add_right, bil_rsmul_right, bil_rsmul_right, hBxv, bil_self, hQx, mul_zero, add_zero]
    exact e1
  have hy''o : y'' ∈ subA Q 1 L := by
    rw [hy'']
    exact add_mem (smul_mem _ _ (add_mem (hJo hyJ) (hJ'o hy'J'))) (smul_mem _ _ (hJo hxJ))
  obtain ⟨K'', hK''⟩ := exists_isOrthSum_span_hyp Q (hJo hxJ) hy''o hQx hQy'' hxy''
  refine isometricLat_trans_aux Q
    (isometricLat_of_common_hyperbolic Q h hK'' hJ rfl hQx hQy hxy hQy'' hxy'') ?_
  have hK''f : IsOrthSum Q L (span R {y'', x}) K'' := by rwa [Set.pair_comm] at hK''
  have hr : IsUnit (wi * (1 + (a3 - a4 * wi * a1))) :=
    (isUnit_iff_exists_inv.mpr ⟨_, hwi⟩).mul (isUnit_one_add_aux (sub_mem n3 (Ideal.mul_mem_left _ _ n1)))
  refine isometricLat_of_unit_hyperbolic Q hK''f h' (x := y'') (y := x) (x' := y') (y' := x') rfl hJ'f
    hQy'' hQx (by rw [bil_comm]; exact hxy'') hQy' hQx' hy'x' hr ?_
  rw [hy'', bil_add_left, bil_rsmul_left, bil_rsmul_left, bil_add_left, ha3, hy'x', ha1]
  have : wi * (1 + (a3 - a4 * wi * a1)) = wi * (a3 + 1) + (-(wi * a4 * wi)) * a1 := by ring
  rw [this]
  simp only [map_add, map_mul, map_neg, map_one]

end DVR

end QuadFormsKB.OMeara
