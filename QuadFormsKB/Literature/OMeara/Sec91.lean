/-
# O'Meara §91: generalities on lattices over local fields (maximal lattices, symmetries of a lattice)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
quadratic space $(V, Q)$ over $F$ with O'Meara's bilinear form $B$ = `bil Q` ($B(x,x) = Q(x)$), lattices
= `Submodule R V`. O'Meara's local field (Chapter IX, p. 239) has a complete discrete valuation ring of integers;
of completeness only the Henselian property of $R$ is used here (`HenselianLocalRing R`), and only where it is
needed (the Local Square Theorem).

**Proves**
* `isSquare_one_add_four_mul` (Local Square Theorem, O'Meara 1963, 63:1, p. 159, in the form used in §91):
  $1 + 4\alpha$ is a square for $\alpha \in \mathfrak p$;
* `mem_iff_of_isMaximal` (**91:1**): on an anisotropic space an $\mathfrak a$-maximal lattice is
  $L = \{x \in V : Q(x) \in \mathfrak a\}$; `eq_of_isMaximal` (all $\mathfrak a$-maximal lattices are equal);
* `orthLat_eq_orth_of_isMaximal` (**91:5**): $O(L) = O(V)$ for a maximal lattice on an anisotropic space;
* `symmetry_mem_orthLat_iff` (**the criterion of §91B**): for a maximal anisotropic vector $u$ of $L$,
  $\tau_u \in O(L) \iff 2B(u, L) \subseteq Q(u)\mathfrak o$;
* `exists_symmetry_mem_orthLat` (**91:4**): $O(L)$ contains a symmetry of $V$.

The symmetry $\tau_u x = x - \frac{2B(x,u)}{Q(u)}u$ (O'Meara 1963, §42E, p. 102) is `symmetry Q u hu`, built from
Mathlib's `Module.reflection`.
-/
import QuadFormsKB.Literature.OMeara.Sec82

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### The Local Square Theorem over a Henselian ring -/

section LocalSquare

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- **Local Square Theorem** (O'Meara 1963, 63:1, p. 159, in the form $1 + 4\alpha \in \mathfrak o^{2}$ for
$\alpha \in \mathfrak p$, as used in the proof of 91:1): over a Henselian local ring, $1 + 4\alpha$ is a square
for every $\alpha$ in the maximal ideal. *Proof:* Hensel's lemma gives a root $r$ of $X^2 - X - \alpha$ (simple
root $0$ modulo $\mathfrak p$), and $(2r - 1)^2 = 1 + 4\alpha$. -/
@[kb "omeara1963" "§63A, 63:1, p. 159 (Local Square Theorem, 1 + 4α with α ∈ p)"]
theorem isSquare_one_add_four_mul {α : R} (hα : α ∈ maximalIdeal R) : IsSquare (1 + 4 * α) := by
  open Polynomial in
  let f : R[X] := X ^ 2 - X - C α
  have hf : f.Monic := by
    have : f = X ^ 2 - (X + C α) := by simp only [f]; ring
    rw [this]
    refine Monic.sub_of_left (monic_X_pow 2) ?_
    calc (X + C α : R[X]).degree ≤ 1 := by
          refine (degree_add_le _ _).trans (max_le degree_X_le ?_)
          exact degree_C_le.trans (by exact_mod_cast zero_le_one)
      _ < (X ^ 2 : R[X]).degree := by
          rw [degree_X_pow]
          by_cases h : (1 : R) = 0
          · exfalso; exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ zero_mem _))
          · haveI : Nontrivial R := ⟨⟨1, 0, h⟩⟩
            exact_mod_cast (by norm_num : (1 : WithBot ℕ) < 2)
  have h0 : f.eval 0 ∈ maximalIdeal R := by
    simpa [f] using neg_mem hα
  have h1 : IsUnit (f.derivative.eval 0) := by
    simp [f, derivative_X_pow]
  obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian f hf 0 h0 h1
  refine ⟨2 * r - 1, ?_⟩
  have : r ^ 2 - r - α = 0 := by simpa [f] using hr
  linear_combination (-4) * this

end LocalSquare

/-! ### Divisibility in a valuation ring -/

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- In a valuation ring: if $d \in \mathfrak a$ and $c \notin \mathfrak a$ for an $R$-submodule $\mathfrak a$ of
$F$, then $d = m c$ with $m \in \mathfrak p$ ($|d| < |c|$). -/
theorem exists_maximalIdeal_mul_of_mem_of_notMem {a : Submodule R F} {c d : F} (hd : d ∈ a) (hc : c ∉ a) :
    ∃ m ∈ maximalIdeal R, d = algebraMap R F m * c := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc a.zero_mem
  by_cases hd0 : d = 0
  · exact ⟨0, zero_mem _, by simp [hd0]⟩
  rcases ValuationRing.isInteger_or_isInteger R (d / c) with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨r, ?_, by rw [hr, div_mul_cancel₀ _ hc0]⟩
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hc
    obtain ⟨u, rfl⟩ := hu
    have : c = (↑u⁻¹ : R) • d := by
      rw [Algebra.smul_def, ← div_mul_cancel₀ d hc0, ← hr, ← mul_assoc, ← map_mul, Units.inv_mul,
        map_one, one_mul]
    rw [this]; exact a.smul_mem _ hd
  · exfalso; apply hc
    have : c = r • d := by
      rw [Algebra.smul_def, hr, inv_div, div_mul_cancel₀ _ hd0]
    rw [this]; exact a.smul_mem _ hd

end Valuation

/-! ### §91A. Maximal lattices on anisotropic spaces -/

section Maximal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Step 1 of the proof of 91:1:** on an anisotropic space, $\{x : Q(x) \in \mathfrak a\}$ is closed under
addition. If $Q(x), Q(y) \in \mathfrak a$ but $Q(x+y) \notin \mathfrak a$, then $|2B(x,y)| > |Q(x)|, |Q(y)|$, so
$-d(x,y) = B(x,y)^2 - Q(x)Q(y) = B(x,y)^2(1 + 4\alpha)$ with $\alpha \in \mathfrak p$ is a non-zero square (Local
Square Theorem), and $Fx + Fy$ is a hyperbolic plane, contradicting anisotropy. -/
theorem Q_add_mem_of_anisotropic (hQ : Q.Anisotropic) {a : Submodule R F} {x y : V} (hx : Q x ∈ a)
    (hy : Q y ∈ a) : Q (x + y) ∈ a := by
  by_contra h
  set b := bil Q x y with hb
  have hc : 2 * b ∉ a := by
    intro hc
    apply h
    rw [Q_add]
    exact add_mem (add_mem hx hc) hy
  obtain ⟨m₁, hm₁, h₁⟩ := exists_maximalIdeal_mul_of_mem_of_notMem hx hc
  obtain ⟨m₂, hm₂, h₂⟩ := exists_maximalIdeal_mul_of_mem_of_notMem hy hc
  have hb0 : b ≠ 0 := by rintro hb0; apply hc; rw [hb0, mul_zero]; exact a.zero_mem
  obtain ⟨s', hs'⟩ := isSquare_one_add_four_mul (R := R) (neg_mem (Ideal.mul_mem_left _ m₁ hm₂))
  set s := b * algebraMap R F s' with hs
  have hss : s ^ 2 = b ^ 2 - Q x * Q y := by
    have := congrArg (algebraMap R F) hs'
    simp only [map_add, map_one, map_mul, map_neg, map_ofNat] at this
    rw [hs, h₁, h₂, mul_pow, _root_.sq (algebraMap R F s'), ← this]
    ring
  have hs0 : s ≠ 0 := by
    rw [hs]
    refine mul_ne_zero hb0 fun h0 => ?_
    have : (1 : R) + 4 * -(m₁ * m₂) = 0 := by
      rw [hs', (IsFractionRing.injective R F) (h0.trans (map_zero _).symm), mul_zero]
    have hu : IsUnit ((1 : R) + 4 * -(m₁ * m₂)) := by
      have : 4 * -(m₁ * m₂) ∈ maximalIdeal R :=
        Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ m₁ hm₂))
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem this)
      rwa [sub_neg_eq_add] at this
    exact hu.ne_zero this
  by_cases hQx : Q x = 0
  · have hx0 : x = 0 := hQ x hQx
    apply h; rw [hx0, zero_add]; exact hy
  · set t := (s - b) / Q x with ht
    have hQt : Q (t • x + y) = 0 := by
      rw [Q_add, Q_smul, bil_smul_left, ← hb, ht]
      field_simp
      linear_combination hss
    have hdep : t • x + y = 0 := hQ _ hQt
    have hy' : y = -t • x := by rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hdep
    apply hs0
    have hB : b = -t * Q x := by rw [hb, hy', bil_smul_right, bil_self]
    have hQy : Q y = t ^ 2 * Q x := by rw [hy', Q_smul]; ring
    have : s ^ 2 = 0 := by rw [hss, hB, hQy]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- The set $X = \{x \in V : Q(x) \in \mathfrak a\}$ as an $R$-submodule, on an anisotropic space. -/
def anisoSub (hQ : Q.Anisotropic) (a : Submodule R F) : Submodule R V where
  carrier := {x | Q x ∈ a}
  add_mem' := fun hx hy => Q_add_mem_of_anisotropic Q hQ hx hy
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    change Q (c • x) ∈ a
    rw [Q_rsmul, _root_.sq, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
    exact a.smul_mem _ (a.smul_mem _ hx)

/-- **Theorem 91:1** (O'Meara 1963, p. 239): if $V$ is an anisotropic quadratic space over a local field and $L$ is
an $\mathfrak a$-maximal lattice on $V$, then $L = \{x \in V : Q(x) \in \mathfrak a\}$. Here the local field is
replaced by the fraction field $F$ of a Henselian discrete valuation ring (completeness is used only through
the Local Square Theorem); $V$ need not be finite-dimensional or regular beyond anisotropy. -/
@[kb "omeara1963" "§91A, 91:1, p. 239"]
theorem mem_iff_of_isMaximal (hQ : Q.Anisotropic) {a : Submodule R F} {L : Submodule R V}
    (hL : IsMaximal Q a L) (x : V) : x ∈ L ↔ Q x ∈ a := by
  obtain ⟨hlat, hn, hmax⟩ := hL
  refine ⟨fun hx => hn (Q_mem_normIdeal Q hx), fun hx => ?_⟩
  by_contra hxL
  let K := L ⊔ (R ∙ x)
  have hKlat : K.IsLattice F :=
    { fg := hlat.fg.sup (fg_span_singleton x)
      span_eq_top := eq_top_iff.mpr (hlat.span_eq_top ▸ span_mono (by
        intro y hy; exact (le_sup_left : L ≤ K) hy)) }
  have hKX : K ≤ anisoSub Q hQ a := by
    refine sup_le (fun y hy => hn (Q_mem_normIdeal Q hy)) ?_
    rw [span_singleton_le_iff_mem]; exact hx
  have hnK : normIdeal Q K ≤ a := by
    rw [normIdeal, span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hKX hy
  have := hmax K hKlat le_sup_left hnK
  exact hxL (this ▸ (le_sup_right : (R ∙ x) ≤ K) (mem_span_singleton_self x))

/-- **91:1, second part** (O'Meara 1963, p. 239): on an anisotropic space all $\mathfrak a$-maximal lattices are
equal. -/
@[kb "omeara1963" "§91A, 91:1, p. 239 (all a-maximal lattices on V are equal)"]
theorem eq_of_isMaximal (hQ : Q.Anisotropic) {a : Submodule R F} {L K : Submodule R V}
    (hL : IsMaximal Q a L) (hK : IsMaximal Q a K) : L = K := by
  ext x; rw [mem_iff_of_isMaximal Q hQ hL, mem_iff_of_isMaximal Q hQ hK]

/-- **Proposition 91:5** (O'Meara 1963, p. 242): if $L$ is a maximal lattice on an anisotropic quadratic space
$V$ over a local field, then $O(L) = O(V)$. -/
@[kb "omeara1963" "§91A, 91:5, p. 242"]
theorem orthLat_eq_orth_of_isMaximal (hQ : Q.Anisotropic) {a : Submodule R F} {L : Submodule R V}
    (hL : IsMaximal Q a L) : orthLat Q L = orth Q := by
  ext σ
  refine ⟨fun h => h.1, fun hσ => ⟨hσ, ?_⟩⟩
  ext x
  simp only [latMap, mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_iff_of_isMaximal Q hQ hL] at hy ⊢
    rwa [hσ y]
  · intro hx
    refine ⟨σ⁻¹ x, ?_, by simp⟩
    rw [mem_iff_of_isMaximal Q hQ hL] at hx ⊢
    have := hσ (σ⁻¹ x)
    simp only [LinearEquiv.coe_inv] at this ⊢
    rw [← this]; simpa using hx

end Maximal

/-! ### §91B. Symmetries in the group of units of a lattice -/

section Symmetry

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The linear form $x \mapsto 2B(x, u)/Q(u)$ defining the symmetry $\tau_u$. -/
def symmForm (u : V) : Module.Dual F V := (2 / Q u) • QuadraticMap.associated Q u

theorem symmForm_apply (u x : V) : symmForm Q u x = 2 * bil Q x u / Q u := by
  simp only [symmForm, LinearMap.smul_apply, smul_eq_mul]
  rw [bil_comm]; ring

theorem symmForm_self {u : V} (hu : Q u ≠ 0) : symmForm Q u u = 2 := by
  rw [symmForm_apply, bil_self]; field_simp

/-- **The symmetry** $\tau_u$ of $V$ with respect to an anisotropic vector $u$ (O'Meara 1963, §42E, p. 102):
$\tau_u x = x - \frac{2B(x,u)}{Q(u)}\,u$. It is Mathlib's `Module.reflection` for the linear form
$x \mapsto 2B(x,u)/Q(u)$. -/
@[kb "omeara1963" "§42E, p. 102 (the symmetry τ_u)"]
def symmetry (u : V) (hu : Q u ≠ 0) : V ≃ₗ[F] V :=
  Module.reflection (symmForm_self Q hu)

theorem symmetry_apply {u : V} (hu : Q u ≠ 0) (x : V) :
    symmetry Q u hu x = x - (2 * bil Q x u / Q u) • u := by
  rw [symmetry, Module.reflection_apply, symmForm_apply]

theorem symmetry_mem_orth {u : V} (hu : Q u ≠ 0) : symmetry Q u hu ∈ orth Q := by
  intro x
  rw [symmetry_apply, sub_eq_add_neg, Q_add, ← neg_smul, QuadraticMap.map_smul, bil_smul_right,
    smul_eq_mul]
  field_simp
  ring

theorem symmetry_symmetry {u : V} (hu : Q u ≠ 0) (x : V) : symmetry Q u hu (symmetry Q u hu x) = x :=
  Module.involutive_reflection (symmForm_self Q hu) x

/-- A vector $u$ is **maximal** in $L$ (O'Meara 1963, §81D, p. 216): $u \in L$ and $cu \in L$ with $c \in F$
forces $c \in \mathfrak o$. -/
@[kb "omeara1963" "§81D, p. 216 (maximal vector of a lattice)"]
def IsMaxVec (F : Type*) [Field F] [Algebra R F] [Module F V] [IsScalarTower R F V]
    (L : Submodule R V) (u : V) : Prop :=
  u ∈ L ∧ ∀ c : F, c • u ∈ L → c ∈ (algebraMap R F).range

/-- If $\tau_u L \subseteq L$ then $\tau_u \in O(L)$ (as $\tau_u$ is an involution; compare 82:12). -/
theorem symmetry_mem_orthLat_of_le {L : Submodule R V} {u : V} (hu : Q u ≠ 0)
    (h : ∀ x ∈ L, symmetry Q u hu x ∈ L) : symmetry Q u hu ∈ orthLat Q L := by
  refine ⟨symmetry_mem_orth Q hu, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx
  · intro x hx
    exact ⟨symmetry Q u hu x, h x hx, symmetry_symmetry Q hu x⟩

/-- **The criterion of §91B** (O'Meara 1963, p. 241): for a maximal anisotropic vector $u$ of the lattice $L$,
the symmetry $\tau_u$ is a unit of $L$ if and only if $2B(u, L) \subseteq Q(u)\,\mathfrak o$. -/
@[kb "omeara1963" "§91B, p. 241 (τ_u ∈ O(L) iff 2B(u,L) ⊆ Q(u)o)"]
theorem symmetry_mem_orthLat_iff {L : Submodule R V} {u : V} (hu : Q u ≠ 0) (hmax : IsMaxVec F L u) :
    symmetry Q u hu ∈ orthLat Q L ↔ ∀ x ∈ L, 2 * bil Q u x ∈ R ∙ Q u := by
  constructor
  · rintro ⟨-, hL⟩ x hx
    have hτ : symmetry Q u hu x ∈ L := hL ▸ ⟨x, hx, rfl⟩
    have : (2 * bil Q x u / Q u) • u ∈ L := by
      have := L.sub_mem hx hτ
      rwa [symmetry_apply, sub_sub_cancel] at this
    obtain ⟨r, hr⟩ := hmax.2 _ this
    refine mem_span_singleton.mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, bil_comm]; field_simp
  · intro h
    refine symmetry_mem_orthLat_of_le Q hu fun x hx => ?_
    obtain ⟨r, hr⟩ := mem_span_singleton.mp (h x hx)
    rw [symmetry_apply]
    have : (2 * bil Q x u / Q u) • u = r • u := by
      rw [← algebraMap_smul F r u]
      congr 1
      rw [bil_comm, ← hr, Algebra.smul_def]; field_simp
    rw [this]
    exact L.sub_mem hx (L.smul_mem r hmax.1)

end Symmetry

section SymmetryDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- On a regular non-zero quadratic space, $Q$ does not vanish on a lattice on $V$. -/
theorem exists_mem_Q_ne_zero (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    {L : Submodule R V} (hL : L.IsLattice F) : ∃ x ∈ L, Q x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- `B` vanishes on `L`, hence on `FL = V`
  have hBL : ∀ x ∈ L, ∀ y ∈ L, bil Q x y = 0 := by
    intro x hx y hy
    have h := Q_add Q x y
    rw [hcon _ (L.add_mem hx hy), hcon x hx, hcon y hy] at h
    have : (2 : F) * bil Q x y = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have hBV : ∀ x y : V, bil Q x y = 0 := by
    intro x y
    have hx : x ∈ span F (L : Set V) := hL.span_eq_top ▸ mem_top
    have hy : y ∈ span F (L : Set V) := hL.span_eq_top ▸ mem_top
    refine span_induction (p := fun x _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hx
    · intro x hx
      refine span_induction (p := fun y _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hy
      · intro y hy; exact hBL x hx y hy
      · intro a b _ _ ha hb; rw [bil_add_right, ha, hb, add_zero]
      · intro c a _ ha; rw [bil_smul_right, ha, mul_zero]
    · intro a b _ _ ha hb; rw [bil_add_left, ha, hb, add_zero]
    · intro c a _ ha; rw [bil_smul_left, ha, mul_zero]
  obtain ⟨m, hm⟩ := exists_ne (0 : V)
  exact hm (hV.1 m fun n => hBV m n)

/-- **Proposition 91:4** (O'Meara 1963, p. 241): if $L$ is a lattice on the regular non-zero quadratic space $V$
over a local field, then $O(L)$ contains a symmetry of $V$. *Proof:* take $u \in L$ with
$Q(u)\mathfrak o = \mathfrak nL$; then $2B(u, L) \subseteq 2\,\mathfrak sL \subseteq \mathfrak nL = Q(u)\mathfrak o$,
so $\tau_u \in O(L)$ by the criterion of §91B. (Only the discrete valuation ring is used.) -/
@[kb "omeara1963" "§91B, 91:4, p. 241"]
theorem exists_symmetry_mem_orthLat (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    {L : Submodule R V} (hL : L.IsLattice F) :
    ∃ u ∈ L, ∃ hu : Q u ≠ 0, symmetry Q u hu ∈ orthLat Q L := by
  obtain ⟨u, hu, hn⟩ := exists_normIdeal_eq Q hL.fg
  have hu0 : Q u ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hQx⟩ := exists_mem_Q_ne_zero Q hV hL
    have : Q x ∈ R ∙ Q u := hn ▸ Q_mem_normIdeal Q hx
    rw [h0, mem_span_singleton] at this
    obtain ⟨r, hr⟩ := this
    exact hQx (by rw [← hr, smul_zero])
  refine ⟨u, hu, hu0, symmetry_mem_orthLat_of_le Q hu0 fun x hx => ?_⟩
  have h2 : 2 * bil Q u x ∈ R ∙ Q u := hn ▸ two_mul_mem_normIdeal Q (bil_mem_scale Q hu hx)
  obtain ⟨r, hr⟩ := mem_span_singleton.mp h2
  rw [symmetry_apply]
  have : (2 * bil Q x u / Q u) • u = r • u := by
    rw [← algebraMap_smul F r u]
    congr 1
    rw [bil_comm, ← hr, Algebra.smul_def]; field_simp
  rw [this]
  exact L.sub_mem hx (L.smul_mem r hu)

end SymmetryDVR

end QuadFormsKB.OMeara
