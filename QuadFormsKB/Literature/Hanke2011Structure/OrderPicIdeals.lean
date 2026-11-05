/-
# The Picard group of an order: the invertible ideals $aR + \mathfrak m$ (Neukirch I (12.9)–(12.11))

**Setting** as in `OrderPicSetup.lean`: $\mathcal O = \mathcal O_E$, $R\subseteq\mathcal O$ a subalgebra over $\mathcal O_F$,
$\mathfrak m\ne0$ an ideal of $\mathcal O$ with $\mathfrak m\subseteq R$; fractional ideals live in $E$.

**Defines** `idealA a` $= aR + \mathfrak m$ for $a\in\mathcal O$ (an $R$-fractional ideal of $E$).

**Proves** (unconditional)
* `mem_idealA`: $x\in aR+\mathfrak m$ iff $x = ra + m$ with $r\in R$, $m\in\mathfrak m$;
* `idealA_mul`: $(aR+\mathfrak m)(bR+\mathfrak m) = abR+\mathfrak m$ when $b$ is a unit modulo $\mathfrak m$;
* `idealA_congr`, `idealA_one`: $aR+\mathfrak m$ depends only on $a$ modulo $\mathfrak m$, and $1R+\mathfrak m = R$;
* `extendedHom_idealA`: $(aR+\mathfrak m)\mathcal O = \mathcal O$ when $a$ is a unit modulo $\mathfrak m$;
* `le_of_extendedHom_eq_one`: an $R$-fractional ideal $I$ with $I\mathcal O = \mathcal O$ satisfies $\mathfrak m\subseteq I\subseteq\mathcal O$;
* `idealA_eq_of_unit`: if moreover $u\in I$, $v\in I^{-1}$ and $uv\in R$ is a unit modulo $\mathfrak m$, then $I = uR+\mathfrak m$.

Source: Neukirch, *Algebraic Number Theory*, Ch. I, §12, proof of (12.9)–(12.11), pp. 78–79.
-/
import QuadFormsKB.Literature.Hanke2011Structure.OrderPicSetup

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.OrderCN

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {R : Subalgebra (𝓞 F) (𝓞 E)} {𝔪 : Ideal (𝓞 E)}

local notation "ι" => algebraMap (𝓞 E) E

theorem fadd_mem {I : FractionalIdeal R⁰ E} {x y : E} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I :=
  Submodule.add_mem I.1 hx hy

theorem fzero_mem (I : FractionalIdeal R⁰ E) : (0 : E) ∈ I := Submodule.zero_mem I.1

theorem fmul_mem (I : FractionalIdeal R⁰ E) (r : R) {x : E} (hx : x ∈ I) : algebraMap R E r * x ∈ I := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem I.1 r hx

variable [IsFractionRing R E]

variable (R 𝔪) in
/-- **The ideal $aR + \mathfrak m$** for $a\in\mathcal O_E$, as an $R$-fractional ideal of $E$. -/
def idealA (a : 𝓞 E) : FractionalIdeal R⁰ E :=
  FractionalIdeal.spanSingleton R⁰ (ι a) + ((idealIn R 𝔪 : Ideal R) : FractionalIdeal R⁰ E)

theorem mem_idealIn {m : R} : m ∈ idealIn R 𝔪 ↔ (m : 𝓞 E) ∈ 𝔪 := Iff.rfl

theorem mem_idealA (hR : ∀ x ∈ 𝔪, x ∈ R) (a : 𝓞 E) (x : E) :
    x ∈ idealA R 𝔪 a ↔ ∃ r : R, ∃ m ∈ 𝔪, ι ((r : 𝓞 E) * a + m) = x := by
  unfold idealA
  rw [FractionalIdeal.mem_add]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton R⁰).mp hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hj
    refine ⟨z, (j' : 𝓞 E), hj', ?_⟩
    rw [Algebra.smul_def, algebraMap_R_E, algebraMap_R_E, map_add, map_mul]
  · rintro ⟨r, m, hm, rfl⟩
    refine ⟨algebraMap R E r * ι a, (FractionalIdeal.mem_spanSingleton R⁰).mpr ⟨r, Algebra.smul_def r (ι a)⟩,
      algebraMap R E ⟨m, hR m hm⟩, (FractionalIdeal.mem_coeIdeal R⁰).mpr ⟨⟨m, hR m hm⟩, hm, rfl⟩, ?_⟩
    rw [algebraMap_R_E, algebraMap_R_E, map_add, map_mul]

theorem mem_idealA_self (hR : ∀ x ∈ 𝔪, x ∈ R) (a : 𝓞 E) : ι a ∈ idealA R 𝔪 a :=
  (mem_idealA hR a _).mpr ⟨1, 0, 𝔪.zero_mem, by simp⟩

theorem mem_idealA_of_mem (hR : ∀ x ∈ 𝔪, x ∈ R) (a : 𝓞 E) {m : 𝓞 E} (hm : m ∈ 𝔪) : ι m ∈ idealA R 𝔪 a :=
  (mem_idealA hR a _).mpr ⟨0, m, hm, by simp⟩

/-- **$(aR+\mathfrak m)(bR+\mathfrak m) = abR+\mathfrak m$** when $bc\equiv1 \bmod \mathfrak m$ for some $c\in\mathcal O$. -/
theorem idealA_mul (hR : ∀ x ∈ 𝔪, x ∈ R) (a b : 𝓞 E) {c : 𝓞 E} (hc : b * c - 1 ∈ 𝔪) :
    idealA R 𝔪 a * idealA R 𝔪 b = idealA R 𝔪 (a * b) := by
  apply le_antisymm
  · refine FractionalIdeal.mul_le.mpr fun i hi j hj => ?_
    obtain ⟨r, m, hm, rfl⟩ := (mem_idealA hR a i).mp hi
    obtain ⟨s, m', hm', rfl⟩ := (mem_idealA hR b j).mp hj
    refine (mem_idealA hR (a * b) _).mpr ⟨r * s, (r : 𝓞 E) * a * m' + m * s * b + m * m',
      𝔪.add_mem (𝔪.add_mem (𝔪.mul_mem_left _ hm') (𝔪.mul_mem_right _ (𝔪.mul_mem_right _ hm)))
        (𝔪.mul_mem_right _ hm), ?_⟩
    rw [← map_mul]
    congr 1
    push_cast
    ring
  · intro x hx
    obtain ⟨r, m, hm, rfl⟩ := (mem_idealA hR (a * b) x).mp hx
    have e : (r : 𝓞 E) * (a * b) + m = ((r : 𝓞 E) * a) * b + (c * m) * b + (1 - b * c) * m := by ring
    rw [e, map_add, map_add, map_mul, map_mul, map_mul]
    refine fadd_mem (fadd_mem ?_ ?_) ?_
    · exact FractionalIdeal.mul_mem_mul ((mem_idealA hR a _).mpr ⟨r, 0, 𝔪.zero_mem, by simp⟩)
        (mem_idealA_self hR b)
    · exact FractionalIdeal.mul_mem_mul (mem_idealA_of_mem hR a (𝔪.mul_mem_left _ hm)) (mem_idealA_self hR b)
    · have h1 : 1 - b * c ∈ 𝔪 := by rw [← neg_sub]; exact 𝔪.neg_mem hc
      exact FractionalIdeal.mul_mem_mul (mem_idealA_of_mem hR a h1) (mem_idealA_of_mem hR b hm)

/-- $aR+\mathfrak m$ depends only on $a$ modulo $\mathfrak m$. -/
theorem idealA_congr (hR : ∀ x ∈ 𝔪, x ∈ R) {a a' : 𝓞 E} (h : a - a' ∈ 𝔪) :
    idealA R 𝔪 a = idealA R 𝔪 a' := by
  have key : ∀ {a a' : 𝓞 E}, a - a' ∈ 𝔪 → idealA R 𝔪 a ≤ idealA R 𝔪 a' := by
    intro a a' h x hx
    obtain ⟨r, m, hm, rfl⟩ := (mem_idealA hR a x).mp hx
    refine (mem_idealA hR a' _).mpr ⟨r, (r : 𝓞 E) * (a - a') + m, 𝔪.add_mem (𝔪.mul_mem_left _ h) hm, ?_⟩
    congr 1; ring
  refine le_antisymm (key h) (key ?_)
  rw [← neg_sub]; exact 𝔪.neg_mem h

/-- $1R + \mathfrak m = R$. -/
theorem idealA_one (hR : ∀ x ∈ 𝔪, x ∈ R) : idealA R 𝔪 1 = 1 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, m, hm, rfl⟩ := (mem_idealA hR 1 x).mp hx
    exact (FractionalIdeal.mem_one_iff R⁰).mpr ⟨r + ⟨m, hR m hm⟩, by rw [algebraMap_R_E]; simp⟩
  · intro x hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hx
    exact (mem_idealA hR 1 _).mpr ⟨r, 0, 𝔪.zero_mem, by rw [algebraMap_R_E]; simp⟩

/-- $aR+\mathfrak m\subseteq\mathcal O$. -/
theorem idealA_le_O (hR : ∀ x ∈ 𝔪, x ∈ R) (a : 𝓞 E) {x : E} (hx : x ∈ idealA R 𝔪 a) : ∃ o : 𝓞 E, ι o = x := by
  obtain ⟨r, m, -, rfl⟩ := (mem_idealA hR a x).mp hx
  exact ⟨_, rfl⟩

/-! ### Extension to $\mathcal O$ -/

theorem extendedHom_eq_one_iff (I : FractionalIdeal R⁰ E) :
    FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) I = 1 ↔
      Submodule.span (𝓞 E) (I : Set E) = 1 := by
  rw [← FractionalIdeal.coeToSubmodule_inj, coe_extendedHom, FractionalIdeal.coe_one]

theorem mem_one_O {x : E} : x ∈ (1 : Submodule (𝓞 E) E) ↔ ∃ o : 𝓞 E, ι o = x := by
  rw [Submodule.mem_one]

/-- **$(aR+\mathfrak m)\mathcal O = \mathcal O$** when $ac\equiv1\bmod\mathfrak m$. -/
theorem extendedHom_idealA (hR : ∀ x ∈ 𝔪, x ∈ R) (a : 𝓞 E) {c : 𝓞 E}
    (hc : a * c - 1 ∈ 𝔪) :
    FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) (idealA R 𝔪 a) = 1 := by
  rw [extendedHom_eq_one_iff]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact mem_one_O.mpr (idealA_le_O hR a hx)
  · intro x hx
    obtain ⟨o, rfl⟩ := mem_one_O.mp hx
    have e : ι o = o • (c • ι a + ι (1 - a * c)) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_add, ← map_mul]; congr 1; ring
    rw [e]
    refine Submodule.smul_mem _ _ (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (mem_idealA_self hR a)))
      (Submodule.subset_span (mem_idealA_of_mem hR a ?_)))
    rw [← neg_sub]; exact 𝔪.neg_mem hc

/-- **An $R$-fractional ideal $I$ with $I\mathcal O = \mathcal O$ lies between $\mathfrak m$ and $\mathcal O$.** -/
theorem le_of_extendedHom_eq_one (hR : ∀ x ∈ 𝔪, x ∈ R) {I : FractionalIdeal R⁰ E}
    (hI : FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) I = 1) :
    (∀ x ∈ I, ∃ o : 𝓞 E, ι o = x) ∧ ∀ m ∈ 𝔪, ι m ∈ I := by
  rw [extendedHom_eq_one_iff] at hI
  refine ⟨fun x hx => mem_one_O.mp (hI ▸ Submodule.subset_span hx), fun m hm => ?_⟩
  -- the `𝒪`-submodule of the `y` with `𝔪 y ⊆ I`
  let S : Submodule (𝓞 E) E :=
    { carrier := {y | ∀ m ∈ 𝔪, ι m * y ∈ I}
      add_mem' := fun {y z} hy hz m hm => by rw [mul_add]; exact fadd_mem (hy m hm) (hz m hm)
      zero_mem' := fun m _ => by rw [mul_zero]; exact fzero_mem _
      smul_mem' := fun o y hy m hm => by
        rw [Algebra.smul_def, ← mul_assoc, ← map_mul]; exact hy _ (𝔪.mul_mem_right _ hm) }
  have hle : Submodule.span (𝓞 E) (I : Set E) ≤ S := by
    rw [Submodule.span_le]
    intro y hy m hm
    exact fmul_mem I ⟨m, hR m hm⟩ hy
  have h1 : (1 : E) ∈ S := hle (hI ▸ mem_one_O.mpr ⟨1, map_one _⟩)
  simpa using h1 m hm

/-- **An invertible $I$ with $I\mathcal O = \mathcal O$ is $uR+\mathfrak m$**, given $u\in I$, $v\in I^{-1}$ with $uv = w\in R$
a unit modulo $\mathfrak m$ (i.e. $ww'\equiv1$ for some $w'\in R$). -/
theorem idealA_eq_of_unit (hR : ∀ x ∈ 𝔪, x ∈ R) {I : FractionalIdeal R⁰ E}
    {I' : FractionalIdeal R⁰ E} (hII' : I * I' = 1)
    (hI : FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) I = 1) {u : 𝓞 E} {v : E} (hu : ι u ∈ I)
    (hv : v ∈ I') {w w' : R} (hw : ι u * v = algebraMap R E w) (hww' : ((w * w' : R) : 𝓞 E) - 1 ∈ 𝔪) :
    I = idealA R 𝔪 u := by
  obtain ⟨hIO, hmI⟩ := le_of_extendedHom_eq_one hR hI
  apply le_antisymm
  · intro x hx
    obtain ⟨o, rfl⟩ := hIO x hx
    have hxv : ι o * v ∈ (1 : FractionalIdeal R⁰ E) := hII' ▸ FractionalIdeal.mul_mem_mul hx hv
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hxv
    refine (mem_idealA hR u _).mpr ⟨r * w', o * (1 - ((w * w' : R) : 𝓞 E)), 𝔪.mul_mem_left _ ?_, ?_⟩
    · rw [← neg_sub]; exact 𝔪.neg_mem hww'
    · -- `o = (r w') u + o (1 - w w')`, using `o v = r` and `u v = w`
      have hrE : algebraMap R E r = ι o * v := hr
      have key : ι ((r : 𝓞 E) * (w' : 𝓞 E)) * ι u = ι o * ((ι u * v) * ι (w' : 𝓞 E)) := by
        rw [map_mul, ← algebraMap_R_E, hrE]; ring
      rw [hw, algebraMap_R_E] at key
      simp only [Subalgebra.coe_mul, map_add, map_sub, map_one, map_mul] at key ⊢
      linear_combination key
  · intro x hx
    obtain ⟨r, m, hm, rfl⟩ := (mem_idealA hR u x).mp hx
    rw [map_add, map_mul, ← algebraMap_R_E]
    exact fadd_mem (fmul_mem I r hu) (hmI m hm)

end

end QuadFormsKB.Hanke2011Structure.OrderCN
