/-
# Cassels, Chapter 14, §6: the $2$-component for $D = 4rs$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 351–353.

Part 1 (group theory): a finite abelian group in which at most two elements square to $1$ has a cyclic
$2$-component, whose order is read off from the orders of elements.
-/
import QuadFormsKB.Literature.Cassels.Ch14.FourRS530
import QuadFormsKB.Literature.Cassels.Ch14.AmbiguousGroup

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

/-! ### Abstract group theory -/

section Abs

/-- Helper: a finite commutative group $Q$ in which every element has $2$-power order and at most two elements
square to $1$ (hypothesis `H`: any two elements $a, b$ with $a^2 = b^2 = 1$ satisfy $a = 1$, $b = 1$ or $a = b$) is
cyclic. Proof: the number of solutions of $a^n = 1$ is at most $n$ (induction on $n$ with the squaring map for even
$n$, and trivially for odd $n$), and `isCyclic_of_card_pow_eq_one_le`. Arguments: `hp` ($2$-power order of every
element), `H` (the hypothesis above). -/
theorem cyc_of_two_group {Q : Type*} [CommGroup Q] [Finite Q] (hp : ∀ a : Q, ∃ k : ℕ, a ^ 2 ^ k = 1)
    (H : ∀ a b : Q, a ^ 2 = 1 → b ^ 2 = 1 → a = 1 ∨ b = 1 ∨ a = b) : IsCyclic Q := by
  classical
  have := Fintype.ofFinite Q
  apply isCyclic_of_card_pow_eq_one_le
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · subst hm
    have hm0 : 0 < m := by omega
    set S : Finset Q := Finset.univ.filter (fun a : Q => a ^ (m + m) = 1) with hS
    have hfib : ∀ b ∈ S.image (fun a => a ^ 2), (S.filter (fun a => a ^ 2 = b)).card ≤ 2 := by
      intro b _
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.1 hlt
      simp only [Finset.mem_filter] at hx hy hz
      have hu : (y * x⁻¹) ^ 2 = 1 := by rw [mul_pow, inv_pow, hy.2, hx.2, mul_inv_cancel]
      have hv : (z * x⁻¹) ^ 2 = 1 := by rw [mul_pow, inv_pow, hz.2, hx.2, mul_inv_cancel]
      rcases H _ _ hu hv with h | h | h
      · exact hxy (mul_inv_eq_one.1 h).symm
      · exact hxz (mul_inv_eq_one.1 h).symm
      · exact hyz (mul_right_cancel h)
    have h1 := Finset.card_le_mul_card_image S 2 hfib
    have himg : S.image (fun a => a ^ 2) ⊆ Finset.univ.filter (fun b : Q => b ^ m = 1) := by
      intro b hb
      simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      obtain ⟨a, ha, rfl⟩ := hb
      rw [← pow_mul, show 2 * m = m + m by ring]
      exact ha
    have h2 := ih m (by omega) hm0
    have h3 := Finset.card_le_card himg
    omega
  · have hone : ∀ a : Q, a ^ n = 1 → a = 1 := by
      intro a ha
      obtain ⟨k, hk⟩ := hp a
      have h := pow_gcd_eq_one.2 ⟨hk, ha⟩
      have hc : Nat.gcd (2 ^ k) n = 1 :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
      rwa [hc, pow_one] at h
    have hsub : (Finset.univ.filter (fun a : Q => a ^ n = 1)) ⊆ {1} := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp [hone a ha]
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega

/-- Helper: if at most two elements of a finite commutative group $G$ square to $1$ (`H`), then the $2$-component
of $G$ (`CommGroup.primaryComponent G 2`) is cyclic. -/
theorem primary_cyclic {G : Type*} [CommGroup G] [Finite G]
    (H : ∀ a b : G, a ^ 2 = 1 → b ^ 2 = 1 → a = 1 ∨ b = 1 ∨ a = b) :
    IsCyclic (CommGroup.primaryComponent G 2) := by
  refine cyc_of_two_group (fun a => ?_) (fun a b ha hb => ?_)
  · obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.1 a.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · have ha' : (a : G) ^ 2 = 1 := by simpa using congrArg Subtype.val ha
    have hb' : (b : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hb
    rcases H _ _ ha' hb' with h | h | h
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Or.inl (Subtype.ext (by simpa using h)))
    · exact Or.inr (Or.inr (Subtype.ext h))

/-- Helper: an element $B$ of order $2^j$ in a finite commutative group $G$ lies in the $2$-component, so
$2^j \le |P|$ for $P$ the $2$-component. Arguments: the element `B` and `hB : orderOf B = 2 ^ j`. -/
theorem card_primary_ge {G : Type*} [CommGroup G] [Finite G] {j : ℕ} (B : G) (hB : orderOf B = 2 ^ j) :
    2 ^ j ≤ Nat.card (CommGroup.primaryComponent G 2) := by
  have hmem : B ∈ CommGroup.primaryComponent G 2 := CommGroup.mem_primaryComponent_iff_orderOf.2 ⟨j, hB⟩
  have h1 : orderOf (⟨B, hmem⟩ : CommGroup.primaryComponent G 2) = 2 ^ j := by
    rw [← hB]; exact Subgroup.orderOf_mk _ _
  have := orderOf_dvd_natCard (⟨B, hmem⟩ : CommGroup.primaryComponent G 2)
  rw [h1] at this
  exact Nat.le_of_dvd Nat.card_pos this

/-- Helper: if at most two elements of the finite commutative group $G$ square to $1$ (`H`), there is an element of
order $2^{j+1}$ (`hex`) and none of order $2^{j+2}$ (`hnot`), then the $2$-component has order exactly $2^{j+1}$. -/
theorem card_primary_eq {G : Type*} [CommGroup G] [Finite G]
    (H : ∀ a b : G, a ^ 2 = 1 → b ^ 2 = 1 → a = 1 ∨ b = 1 ∨ a = b) {j : ℕ}
    (hex : ∃ B : G, orderOf B = 2 ^ (j + 1)) (hnot : ¬ ∃ B : G, orderOf B = 2 ^ (j + 2)) :
    Nat.card (CommGroup.primaryComponent G 2) = 2 ^ (j + 1) := by
  have := primary_cyclic H
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CommGroup.primaryComponent.isPGroup (G := G) (p := 2))
  obtain ⟨B, hB⟩ := hex
  have hge := card_primary_ge B hB
  rw [hk] at hge ⊢
  have hjk : j + 1 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hge
  by_contra hne
  have hk2 : j + 2 ≤ k := by
    by_contra h
    exact hne (by rw [show k = j + 1 by omega])
  apply hnot
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := CommGroup.primaryComponent G 2)
  rw [hk] at hg
  have hdvd : 2 ^ (k - (j + 2)) ∣ orderOf g := by
    rw [hg]; exact pow_dvd_pow 2 (by omega)
  have hord := orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hdvd
  rw [hg, Nat.pow_div (by omega) (by norm_num), show k - (k - (j + 2)) = j + 2 by omega] at hord
  refine ⟨((g ^ 2 ^ (k - (j + 2)) : CommGroup.primaryComponent G 2) : G), ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hord

/-- Helper: **a character of index $2$ cuts out the squares.** Let $G$ be a finite commutative group, $\chi : G \to
\{\pm1\}$ a homomorphism taking the value $-1$ at some element `C` (`hC`), and suppose every $A$ with $A^2 = 1$ is
$1$ or `T` (`hT`). Then every `A` with $\chi(A) = 1$ (`hA`) is a square. Proof: the squares $\phi(G)$ lie in
$\ker\chi$, which has index $2$; and $[G : \phi(G)] = |\ker \phi| \le 2$, so the relative index of $\phi(G)$ in
$\ker\chi$ is $1$. -/
theorem exists_sq_of_chi_eq_one {G : Type*} [CommGroup G] [Finite G] (χ : G →* ℤˣ) (T : G)
    (hT : ∀ A : G, A ^ 2 = 1 → A = 1 ∨ A = T) (C : G) (hC : χ C = -1) (A : G) (hA : χ A = 1) :
    ∃ B : G, B ^ 2 = A := by
  classical
  set φ : G →* G := powMonoidHom 2 with hφ
  set K : Subgroup G := χ.ker with hK
  have hrk : φ.range ≤ K := by
    rintro _ ⟨B, rfl⟩
    rw [hK, MonoidHom.mem_ker, hφ, powMonoidHom_apply, map_pow, Int.units_sq]
  have hKidx : K.index = 2 := by
    rw [hK, Subgroup.index_ker]
    have : χ.range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      intro u
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one χ⟩
      · exact ⟨C, hC⟩
    rw [this, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hker : Nat.card φ.ker ≤ 2 := by
    have hsub : (φ.ker : Set G) ⊆ {1, T} := by
      intro B hB
      have hB2 : B ^ 2 = 1 := by simpa [hφ, powMonoidHom_apply] using hB
      rcases hT B hB2 with h | h <;> simp [h]
    calc Nat.card φ.ker = (φ.ker : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, T} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  have h1 := Subgroup.card_mul_index φ.range
  have h2 := Subgroup.card_ker_mul_card_range φ
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have hidx : φ.range.index = Nat.card φ.ker := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, mul_comm, h2]
  have h3 := Subgroup.relIndex_mul_index hrk
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hrel : φ.range.relIndex K = 1 := by
    rw [hKidx, hidx] at h3
    omega
  have hle : K ≤ φ.range := Subgroup.relIndex_eq_one.1 hrel
  have hAK : A ∈ K := by rw [hK, MonoidHom.mem_ker]; exact hA
  obtain ⟨B, hB⟩ := hle hAK
  exact ⟨B, by simpa [hφ, powMonoidHom_apply] using hB⟩

end Abs

/-! ### Genus characters of $f(-1), f(r), f(s)$ and the group of classes of order dividing $2$ -/

section NT

variable {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hrs : r ≠ s) {D : ℤ} [NonzeroDisc D] (hD : D = 4 * r * s)

/-- Helper: a prime $p \equiv 1 \pmod 4$ is odd. -/
theorem ne_two_of_mod4 {p : ℕ} (hp : p % 4 = 1) : p ≠ 2 := by omega

/-- Helper: the prime $r$ divides $D = 4rs$ (`hD`). -/
theorem dvd_D_r (hD : D = 4 * r * s) : (r : ℤ) ∣ D := ⟨4 * s, by rw [hD]; ring⟩

/-- Helper: the prime $s$ divides $D = 4rs$ (`hD`). -/
theorem dvd_D_s (hD : D = 4 * r * s) : (s : ℤ) ∣ D := ⟨4 * r, by rw [hD]; ring⟩

/-- Helper: distinct primes $p \ne q$ satisfy $p \nmid q$ (as integers). -/
theorem not_dvd_prime {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p ≠ q) : ¬ (p : ℤ) ∣ (q : ℤ) := fun h' =>
  h ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp (Int.natCast_dvd_natCast.mp h'))

/-- Helper: $\left(\frac{-a}{p}\right) = \left(\frac{a}{p}\right)$ for a prime $p \equiv 1 \pmod 4$ (`hp`) and an
integer `a`. -/
theorem legendreSym_neg_of_one_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) (a : ℤ) :
    legendreSym p (-a) = legendreSym p a := by
  rw [show -a = (-1) * a by ring, legendreSym.mul, legendreSym.at_neg_one (ne_two_of_mod4 hp),
    ZMod.χ₄_nat_one_mod_four hp, one_mul]

/-- Helper: the genus character evaluated through a value. If the form `f` takes the value `v` at $(x, y)$ and
$p \nmid v$, then $\chi_p(\mathfrak C_f) = (v/p)$ (`charHom_mk`). Arguments: the prime `p` (odd, `hp2`, dividing
$D$, `hpD`), the form `f`, the point `x y`, the value `v` with `hv` and `hnd`. -/
theorem charHom_val (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpD : (p : ℤ) ∣ D) (f : PrimForm D) (x y v : ℤ)
    (hv : f.1.eval x y = v) (hnd : ¬ (p : ℤ) ∣ v) :
    ((charHom p D hp2 hpD (mk f) : ℤˣ) : ℤ) = legendreSym p v := by
  rw [charHom_mk p D hp2 hpD f x y (by rw [hv]; exact hnd), hv]

/-- Helper: a unit of $\mathbb Z$ whose value is $1$ is $1$. -/
theorem units_eq_one_of {u : ℤˣ} {z : ℤ} (h : (u : ℤ) = z) (hz : z = 1) : u = 1 :=
  Units.ext (by rw [h, hz]; rfl)

/-- Helper: a unit of $\mathbb Z$ whose value is $-1$ is $-1$. -/
theorem units_eq_neg_one_of {u : ℤˣ} {z : ℤ} (h : (u : ℤ) = z) (hz : z = -1) : u = -1 :=
  Units.ext (by rw [h, hz]; simp)

/-- Helper: $\chi_r(f(-1)) = 1$. -/
theorem chiR_M (hr : r % 4 = 1) :
    charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) (mk (formM hrs hD)) = 1 := by
  apply Units.ext
  have hnd : ¬ (r : ℤ) ∣ -1 := by
    intro h
    have h1 := Int.eq_one_of_dvd_one (by positivity) ((dvd_neg).1 h)
    have h2 := (Fact.out : r.Prime).one_lt
    omega
  rw [charHom_val r (ne_two_of_mod4 hr) (dvd_D_r hD) (formM hrs hD) 1 0 (-1) (by simp [BinQF.eval_eq, formM]) hnd,
    legendreSym.at_neg_one (ne_two_of_mod4 hr), ZMod.χ₄_nat_one_mod_four hr]
  simp

/-- Helper: $\chi_s(f(-1)) = 1$. -/
theorem chiS_M (hs : s % 4 = 1) :
    charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) (mk (formM hrs hD)) = 1 := by
  apply Units.ext
  have hnd : ¬ (s : ℤ) ∣ -1 := by
    intro h
    have h1 := Int.eq_one_of_dvd_one (by positivity) ((dvd_neg).1 h)
    have h2 := (Fact.out : s.Prime).one_lt
    omega
  rw [charHom_val s (ne_two_of_mod4 hs) (dvd_D_s hD) (formM hrs hD) 1 0 (-1) (by simp [BinQF.eval_eq, formM]) hnd,
    legendreSym.at_neg_one (ne_two_of_mod4 hs), ZMod.χ₄_nat_one_mod_four hs]
  simp

/-- Helper: $\chi_r(f(r)) = (s/r)$ (value $-s$ at $(0, 1)$). -/
theorem chiR_R (hr : r % 4 = 1) (hs : s % 4 = 1) :
    ((charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) (mk (formR hrs hD)) : ℤˣ) : ℤ) = legendreSym s r := by
  rw [charHom_val r (ne_two_of_mod4 hr) (dvd_D_r hD) (formR hrs hD) 0 1 (-(s : ℤ)) (by simp [BinQF.eval_eq, formR])
    (fun h => not_dvd_prime hrs ((dvd_neg).1 h)), legendreSym_neg_of_one_mod_four hr]
  exact (legendreSym.quadratic_reciprocity_one_mod_four hr (ne_two_of_mod4 hs)).symm

/-- Helper: $\chi_r(f(s)) = (s/r)$ (value $s$ at $(1, 0)$, then quadratic reciprocity). -/
theorem chiR_S (hr : r % 4 = 1) (hs : s % 4 = 1) :
    ((charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) (mk (formS hrs hD)) : ℤˣ) : ℤ) = legendreSym s r := by
  rw [charHom_val r (ne_two_of_mod4 hr) (dvd_D_r hD) (formS hrs hD) 1 0 (s : ℤ) (by simp [BinQF.eval_eq, formS])
    (not_dvd_prime hrs)]
  exact (legendreSym.quadratic_reciprocity_one_mod_four hr (ne_two_of_mod4 hs)).symm

/-- Helper: $\chi_s(f(r)) = (s/r)$ (value $r$ at $(1, 0)$, then quadratic reciprocity). -/
theorem chiS_R (hs : s % 4 = 1) :
    ((charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) (mk (formR hrs hD)) : ℤˣ) : ℤ) = legendreSym s r := by
  rw [charHom_val s (ne_two_of_mod4 hs) (dvd_D_s hD) (formR hrs hD) 1 0 (r : ℤ) (by simp [BinQF.eval_eq, formR])
    (not_dvd_prime hrs.symm)]

/-- Helper: $\chi_s(f(s)) = (s/r)$ (value $-r$ at $(0, 1)$). -/
theorem chiS_S (hs : s % 4 = 1) :
    ((charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) (mk (formS hrs hD)) : ℤˣ) : ℤ) = legendreSym s r := by
  rw [charHom_val s (ne_two_of_mod4 hs) (dvd_D_s hD) (formS hrs hD) 0 1 (-(r : ℤ)) (by simp [BinQF.eval_eq, formS])
    (fun h => not_dvd_prime hrs.symm ((dvd_neg).1 h)), legendreSym_neg_of_one_mod_four hs]

/-- Helper: $r \ne 0$ as an integer. -/
theorem cast_ne_zero_r : (r : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : r.Prime).ne_zero

/-- Helper: $s \ne 0$ as an integer. -/
theorem cast_ne_zero_s : (s : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : s.Prime).ne_zero

include hD in
/-- Helper: if $ac = -rs$ and $a \ne 0$ then $\operatorname{amb}F(D, a) = [a, 0, c]$ (the form `ambF` of
`AmbiguousFG`), for $D = 4rs$. Arguments: `a`, `c`, `ha : a ≠ 0`, `h : a * c = -(r * s)`. -/
theorem ambF_eq_of_mul {a c : ℤ} (ha : a ≠ 0) (h : a * c = -((r : ℤ) * s)) : ambF D a = BinQF.mk a 0 c := by
  have h1 : -D / (4 * a) = c := by
    rw [show -D = (4 * a) * c by rw [hD]; linear_combination (-4) * h]
    exact Int.mul_ediv_cancel_left _ (mul_ne_zero (by norm_num) ha)
  rw [ambF, h1]

/-- **Composition of the ambiguous classes** (Cassels, Ch. 14, §6, p. 351 and Lemma 6.1, (6.10)): in the class group of
discriminant $D = 4rs$, $f(-1) \cdot f(r) = f(s)$, i.e. $[-1, 0, rs]\,[r, 0, -s] \sim [s, 0, -r]$. -/
theorem mk_formM_mul_formR : mk (formM hrs hD) * mk (formR hrs hD) = mk (formS hrs hD) := by
  have hM : (formM hrs hD).1 = ambF D (-1) := by
    rw [ambF_eq_of_mul hD (a := -1) (c := r * s) (by norm_num) (by ring)]; rfl
  have hR : (formR hrs hD).1 = ambF D r := by
    rw [ambF_eq_of_mul hD (a := r) (c := -s) cast_ne_zero_r (by ring)]; rfl
  obtain ⟨f₃, h3, hm⟩ := mk_mul_mk_ambF (formM hrs hD) (formR hrs hD) hM hR
  rw [hm]
  have hg : (-1 * (r : ℤ) / ((Int.gcd (-1) (r : ℤ) : ℕ) : ℤ) ^ 2) = -r := by simp [Int.gcd]
  rw [hg, ambF_eq_of_mul hD (a := -r) (c := s) (neg_ne_zero.2 cast_ne_zero_r) (by ring)] at h3
  exact mk_eq_of_b_zero f₃ (formS hrs hD) (by simp [h3]) (by simp [formS])
    (Or.inr ⟨by simp [h3, formS], by simp [h3, formS]⟩)

include hrs hD in
/-- **At most one class of order $2$** (Cassels, Ch. 14, §6, p. 351: "the group $\mathcal A$ is of order $2$", in the
form we need): there is a class $T$ such that every class $A$ with $A^2 = 1$ is $1$ or $T$. Proof: such classes are
among $1, f(-1), f(r), f(s)$ (`amb_classes`), one of $f(-1), f(r), f(s)$ is $1$ (`one_of_three`), and
$f(-1) f(r) = f(s)$. -/
theorem exists_T (hr : r % 4 = 1) (hs : s % 4 = 1) :
    ∃ T : FormClass D, ∀ A : FormClass D, A ^ 2 = 1 → A = 1 ∨ A = T := by
  have hMR := mk_formM_mul_formR hrs hD
  have hM2 : mk (formM hrs hD) ^ 2 = 1 := mk_sq_of_isAmbiguousForm _ (Or.inl (by simp [formM]))
  rcases one_of_three hrs hD hr hs with h | h | h
  · refine ⟨mk (formR hrs hD), fun A hA => ?_⟩
    rcases amb_classes hrs hD hr hs A hA with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl h
    · exact Or.inr rfl
    · exact Or.inr (by rw [← hMR, h, one_mul])
  · refine ⟨mk (formM hrs hD), fun A hA => ?_⟩
    rcases amb_classes hrs hD hr hs A hA with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl h
    · exact Or.inr (by rw [← hMR, h, mul_one])
  · refine ⟨mk (formM hrs hD), fun A hA => ?_⟩
    rcases amb_classes hrs hD hr hs A hA with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · refine Or.inr (mul_left_cancel (a := mk (formM hrs hD)) ?_)
      rw [← sq, hM2, hMR, h]
    · exact Or.inl h

end NT

/-! ### Square roots with prescribed value, and a class of the non-principal genus -/

section Roots

/-- Helper: **a square root of a class, with a prescribed value.** If a primitive form `f` of discriminant $D$
represents $w^2$ at the coprime pair $(x, y)$ with $w$ prime to $2D$, then there is a class $\mathfrak A$ with
$\mathfrak A^2 = \mathfrak C_f$ which contains a form `g` with first coefficient $w$ (the class of
$[w, b, wc]$ for $f \sim [w^2, b, c]$; Cassels, Ch. 14, §6, p. 351: "$\mathfrak C_1$ of $[w, b, c]$"). -/
theorem exists_root_with_value {D : ℤ} [NonzeroDisc D] (f : PrimForm D) {x y w : ℤ} (hxy : IsCoprime x y)
    (hw : IsCoprime w (2 * D)) (hev : f.1.eval x y = w ^ 2) :
    ∃ (A : FormClass D) (g : PrimForm D), A ^ 2 = mk f ∧ mk g = A ∧ g.1.a = w := by
  obtain ⟨g0, e, hga⟩ := exists_sLEquiv_a_of_eval (f := f.1) hxy
  rw [hev] at hga
  have hdisc : g0.disc = D := (SLEquiv.disc_eq e).symm.trans f.2.2
  have hwD : IsCoprime w D := hw.of_isCoprime_of_dvd_right ⟨2, by ring⟩
  have hD' : g0.b ^ 2 - 4 * w ^ 2 * g0.c = D := by rw [← hga]; exact hdisc
  have hcw : IsCoprime w g0.b := by
    have h1 : IsCoprime w (g0.b ^ 2) := by
      have : g0.b ^ 2 = D + w * (4 * w * g0.c) := by linear_combination hD'
      rw [this]; exact hwD.add_mul_left_right _
    exact (IsCoprime.pow_right_iff two_pos).1 h1
  let h : PrimForm D := ⟨BinQF.mk w g0.b (w * g0.c),
    fun d h1 h2 _ => hcw.isUnit_of_dvd' (by simpa using h1) (by simpa using h2),
    by simp only [BinQF.disc, a_mk, b_mk, c_mk]; linear_combination hD'⟩
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  have hc : Concordant h.1 h.1 := by
    refine ⟨?_, rfl, rfl, ?_⟩
    · simp [h, hw0]
    · rw [h.2.2]
      exact ⟨g0.c, by simp only [h, a_mk, b_mk, c_mk]; linear_combination hD'⟩
  have hcomp : (PrimForm.comp h h hc).1 = g0 := by
    apply eq_of_a_b_disc
    · rw [primComp_a]; simp [h, hw0]
    · rw [primComp_a]; simp only [h, a_mk]; rw [hga]; ring
    · rw [primComp_b]; rfl
    · exact (PrimForm.comp h h hc).2.2.trans hdisc.symm
  refine ⟨mk h, h, ?_, rfl, by simp [h]⟩
  rw [sq, mk_mul_mk h h hc]
  exact mk_eq_mk.2 (by rw [hcomp]; exact e.symm)

variable {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hrs : r ≠ s) {D : ℤ} [NonzeroDisc D] (hD : D = 4 * r * s)

/-- **A square root of $f(r)$ with the genus character $[s/r]_4$** (Cassels, Ch. 14, §6, pp. 351–352): for distinct
primes $r \equiv s \equiv 1 \pmod 4$ with $(s/r) = 1$, the class $\mathfrak C_r = [f(r)]$ is a square
$\mathfrak A^2$ with $\chi_r(\mathfrak A) = [s/r]_4$ (`exists_rep_legendreSym_eq_condBiquadSym_uncond`: $f(r)$
represents $w^2$ primitively with $(w/r) = [s/r]_4$, and $\mathfrak A$ contains a form with first coefficient $w$). -/
theorem exists_root_R (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1) :
    ∃ A : FormClass D, A ^ 2 = mk (formR hrs hD) ∧
      ((charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) A : ℤˣ) : ℤ) = condBiquadSym r s := by
  obtain ⟨x, y, w, hxy, hw, hrep, hleg⟩ := exists_rep_legendreSym_eq_condBiquadSym_uncond hr hs hrs hη
  have hev : (formR hrs hD).1.eval x y = w ^ 2 := by
    rw [BinQF.eval_eq]; simp only [formR, amb0_a, amb0_b, amb0_c]; linear_combination hrep
  have hw' : IsCoprime w (2 * D) := by
    have h2 : IsCoprime w 2 := hw.of_isCoprime_of_dvd_right ⟨r * s, by ring⟩
    have h4 : IsCoprime w 4 := by simpa using h2.pow_right (n := 2)
    rw [hD, show (2 : ℤ) * (4 * r * s) = 4 * (2 * r * s) by ring]
    exact h4.mul_right hw
  obtain ⟨A, g, hA2, hg, hga⟩ := exists_root_with_value (formR hrs hD) hxy hw' hev
  refine ⟨A, hA2, ?_⟩
  have hndvd : ¬ (r : ℤ) ∣ w := by
    intro h
    have hc : IsCoprime w (r : ℤ) := hw.of_isCoprime_of_dvd_right ⟨2 * s, by ring⟩
    have hu := hc.isUnit_of_dvd' h dvd_rfl
    have h1 := Int.isUnit_iff.mp hu
    have h2 := (Fact.out : r.Prime).one_lt
    omega
  rw [← hg, charHom_val r (ne_two_of_mod4 hr) (dvd_D_r hD) g 1 0 w (by rw [BinQF.eval_eq]; simp [hga]) hndvd]
  exact hleg

/-- **A square root of $f(s)$ with the genus character $[r/s]_4$** (the case of `exists_root_R` with $r$ and $s$
exchanged): for $(s/r) = 1$, $f(s)$ is a square $\mathfrak A^2$ with $\chi_s(\mathfrak A) = [r/s]_4$. -/
theorem exists_root_S (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1) :
    ∃ A : FormClass D, A ^ 2 = mk (formS hrs hD) ∧
      ((charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) A : ℤˣ) : ℤ) = condBiquadSym s r := by
  have hD' : D = 4 * s * r := by rw [hD]; ring
  have hη' : legendreSym r s = 1 :=
    (legendreSym.quadratic_reciprocity_one_mod_four hr (ne_two_of_mod4 hs)).symm.trans hη
  obtain ⟨A, hA, hχ⟩ := exists_root_R (r := s) (s := r) hrs.symm hD' hs hr hη'
  exact ⟨A, hA, hχ⟩

end Roots

section Dirichlet

variable {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hrs : r ≠ s) {D : ℤ} [NonzeroDisc D] (hD : D = 4 * r * s)

include hrs in
/-- **A class in the non-principal genus** (Gauss; Cassels, Ch. 14, §5, p. 343 and §6, p. 351: "there are two
genera"): for distinct primes $r \equiv s \equiv 1 \pmod 4$ there is a class $\mathfrak C$ of discriminant
$D = 4rs$ with $\chi_r(\mathfrak C) = \chi_s(\mathfrak C) = -1$. Proof: take a prime $q$ (Dirichlet's theorem,
Mathlib's `Nat.forall_exists_prime_gt_and_eq_mod`) which is a quadratic non-residue modulo both $r$ and $s$ (Chinese
remainder theorem) and exceeds $4rs$; then $(rs/q) = (q/r)(q/s) = 1$ by quadratic reciprocity, so
$b^2 \equiv rs \pmod q$ is soluble and $[q, 2b, (b^2 - rs)/q]$ is a primitive form of discriminant $4rs$ with the
value $q$. -/
theorem exists_class_neg (hr : r % 4 = 1) (hs : s % 4 = 1) :
    ∃ C : FormClass D, charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) C = -1 ∧
      charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) C = -1 := by
  have hrp : r.Prime := Fact.out
  have hsp : s.Prime := Fact.out
  have hr2 : ringChar (ZMod r) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact ne_two_of_mod4 hr
  have hs2 : ringChar (ZMod s) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact ne_two_of_mod4 hs
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hr2
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare hs2
  have hcop : Nat.Coprime r s := (Nat.coprime_primes hrp hsp).2 hrs
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop a.val b.val
  have hkA : (k : ZMod r) = a := by
    rw [(ZMod.natCast_eq_natCast_iff k a.val r).2 hk1, ZMod.natCast_zmod_val]
  have hkB : (k : ZMod s) = b := by
    rw [(ZMod.natCast_eq_natCast_iff k b.val s).2 hk2, ZMod.natCast_zmod_val]
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, by simp⟩)
  have hkr : Nat.Coprime k r := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hrp).2 fun h => ha0 ?_)
    rw [← hkA]; exact (ZMod.natCast_eq_zero_iff k r).2 h
  have hks : Nat.Coprime k s := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hsp).2 fun h => hb0 ?_)
    rw [← hkB]; exact (ZMod.natCast_eq_zero_iff k s).2 h
  obtain ⟨q, hqbig, hq, hqk⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime k (r * s)).mpr (Nat.Coprime.mul_right hkr hks)) (4 * r * s)
  have hqk' : q ≡ k [MOD r * s] := (ZMod.natCast_eq_natCast_iff q k (r * s)).mp hqk
  have hrs1 : 1 ≤ r * s := Nat.mul_pos hrp.pos hsp.pos
  have h4 : 4 * r * s = 4 * (r * s) := by ring
  have hq2 : q ≠ 2 := by omega
  have : Fact q.Prime := ⟨hq⟩
  have hqA : (q : ZMod r) = a := by
    rw [← hkA]; exact (ZMod.natCast_eq_natCast_iff q k r).2 (Nat.ModEq.of_dvd (dvd_mul_right r s) hqk')
  have hqB : (q : ZMod s) = b := by
    rw [← hkB]; exact (ZMod.natCast_eq_natCast_iff q k s).2 (Nat.ModEq.of_dvd (dvd_mul_left s r) hqk')
  have hqr : legendreSym r (q : ℤ) = -1 := (legendreSym.eq_neg_one_iff' r (a := q)).2 (by rw [hqA]; exact ha)
  have hqs : legendreSym s (q : ℤ) = -1 := (legendreSym.eq_neg_one_iff' s (a := q)).2 (by rw [hqB]; exact hb)
  have hqr' : legendreSym q (r : ℤ) = -1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four hr hq2]; exact hqr
  have hqs' : legendreSym q (s : ℤ) = -1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four hs hq2]; exact hqs
  have hq_nd : ¬ (q : ℤ) ∣ (r : ℤ) * s := by
    intro h
    have h' : q ∣ r * s := by exact_mod_cast h
    have := Nat.le_of_dvd hrs1 h'
    omega
  have hrsq : legendreSym q ((r : ℤ) * s) = 1 := by
    rw [legendreSym.mul, hqr', hqs']; norm_num
  have hne0 : (((r : ℤ) * s : ℤ) : ZMod q) ≠ 0 := fun h =>
    hq_nd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  obtain ⟨y, hy⟩ := (legendreSym.eq_one_iff q hne0).1 hrsq
  set b₀ : ℤ := (y.val : ℤ) with hb₀def
  have hb₀ : (q : ℤ) ∣ b₀ ^ 2 - (r : ℤ) * s := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    push_cast at hy
    simp [b₀, hy, sq]
  obtain ⟨c, hc⟩ := hb₀
  have hcop2 : IsCoprime (q : ℤ) (2 * b₀) := by
    have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    rw [Prime.coprime_iff_not_dvd hqprime]
    intro h
    rcases hqprime.dvd_or_dvd h with h2 | h2
    · have : q ∣ 2 := by exact_mod_cast h2
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · apply hq_nd
      have : (q : ℤ) ∣ b₀ ^ 2 := dvd_pow h2 two_ne_zero
      have h3 : (r : ℤ) * s = b₀ ^ 2 - q * c := by linear_combination -hc
      rw [h3]
      exact dvd_sub this (dvd_mul_right _ _)
  have hqc : (q : ℤ) * c = b₀ ^ 2 - r * s := hc.symm
  let f : PrimForm D := ⟨BinQF.mk q (2 * b₀) c,
    fun d h1 h2 _ => hcop2.isUnit_of_dvd' (by simpa using h1) (by simpa using h2),
    by
      simp only [BinQF.disc, a_mk, b_mk, c_mk]
      rw [hD]
      linear_combination (-4 : ℤ) * hqc⟩
  have hnr : ¬ (r : ℤ) ∣ (q : ℤ) := by
    intro h
    have h0 := (legendreSym.eq_zero_iff r (q : ℤ)).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h)
    rw [hqr] at h0; norm_num at h0
  have hns : ¬ (s : ℤ) ∣ (q : ℤ) := by
    intro h
    have h0 := (legendreSym.eq_zero_iff s (q : ℤ)).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h)
    rw [hqs] at h0; norm_num at h0
  have hev : f.1.eval 1 0 = q := by simp [f, BinQF.eval_eq]
  refine ⟨mk f, units_eq_neg_one_of ?_ hqr, units_eq_neg_one_of ?_ hqs⟩
  · exact charHom_val r (ne_two_of_mod4 hr) (dvd_D_r hD) f 1 0 q hev hnr
  · exact charHom_val s (ne_two_of_mod4 hs) (dvd_D_s hD) f 1 0 q hev hns

end Dirichlet

/-! ### The orders of the $2$-component -/

section Main

/-- Helper: $1 \ne -1$ in $\mathbb Z^\times$. -/
theorem units_one_ne_neg_one : (1 : ℤˣ) ≠ -1 := by
  intro h
  have := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at this

/-- Helper: if some class $X \ne 1$ with $X^2 = 1$ is a fourth power $\mathfrak B^4$, then $\mathfrak B$ has order
$8$, so the $2$-component has order at least $8$. -/
theorem card_ge_eight_of_fourth {G : Type*} [CommGroup G] [Finite G] (X B : G) (hX2 : X ^ 2 = 1) (hX1 : X ≠ 1)
    (hB : B ^ 4 = X) : 8 ≤ Nat.card (CommGroup.primaryComponent G 2) := by
  have hord : orderOf B = 2 ^ 3 := by
    apply orderOf_eq_prime_pow (n := 2)
    · rw [show 2 ^ 2 = 4 by norm_num, hB]; exact hX1
    · rw [show 2 ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, hB, hX2]
  simpa using card_primary_ge B hord

variable {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hrs : r ≠ s) {D : ℤ} [NonzeroDisc D] (hD : D = 4 * r * s)

include hrs hD

/-- Helper: any two classes with square $1$ are $1$, $1$, or equal (from `exists_T`), the hypothesis `H` of
`primary_cyclic`. -/
theorem amb_pair (hr : r % 4 = 1) (hs : s % 4 = 1) :
    ∀ a b : FormClass D, a ^ 2 = 1 → b ^ 2 = 1 → a = 1 ∨ b = 1 ∨ a = b := by
  obtain ⟨T, hT⟩ := exists_T hrs hD hr hs
  intro a b ha hb
  rcases hT a ha with rfl | rfl <;> rcases hT b hb with rfl | rfl <;> simp

include hD in
/-- Helper: if $(s/r) = 1$, both genus characters $\chi_r$ and $\chi_s$ are trivial on the classes $A$ with
$A^2 = 1$ (these are among $1, f(-1), f(r), f(s)$, `amb_classes`, and each of $f(-1), f(r), f(s)$ has
character $1$ by `chiR_M`, `chiR_R`, `chiR_S`, `chiS_M`, `chiS_R`, `chiS_S`). -/
theorem chi_amb_one (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1) (A : FormClass D)
    (hA : A ^ 2 = 1) :
    charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) A = 1 ∧ charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) A = 1 := by
  rcases amb_classes hrs hD hr hs A hA with rfl | rfl | rfl | rfl
  · exact ⟨map_one _, map_one _⟩
  · exact ⟨chiR_M hrs hD hr, chiS_M hrs hD hs⟩
  · exact ⟨units_eq_one_of (chiR_R hrs hD hr hs) hη, units_eq_one_of (chiS_R hrs hD hs) hη⟩
  · exact ⟨units_eq_one_of (chiR_S hrs hD hr hs) hη, units_eq_one_of (chiS_S hrs hD hs) hη⟩

include hrs hD in
/-- **The $2$-component is cyclic** (Cassels, Ch. 14, §6, p. 351: "$\mathcal G$ contains only one element of
(precise) order $2$: hence the $2$-component of $\mathcal G$ is cyclic"): for distinct primes
$r \equiv s \equiv 1 \pmod 4$ and $D = 4rs$ (`hD`). -/
theorem fourRS_cyclic (hr : r % 4 = 1) (hs : s % 4 = 1) :
    IsCyclic (CommGroup.primaryComponent (FormClass D) 2) :=
  primary_cyclic (amb_pair hrs hD hr hs)

/-- **$\eta = -1$: the $2$-component has order $2$** (Cassels, Ch. 14, §6, p. 351). Proof: $f(r)$ and $f(s)$ have
character $\chi_r = (s/r) = -1$, so $f(-1) \sim 1$ (`one_of_three`), $f(r) \sim f(s)$ is the unique class of order $2$,
and it is not a square (squares have $\chi_r = 1$), so there is no element of order $4$. -/
theorem fourRS_card_two (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = -1) :
    Nat.card (CommGroup.primaryComponent (FormClass D) 2) = 2 := by
  have H := amb_pair hrs hD hr hs
  set χ := charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) with hχ
  have hRm : χ (mk (formR hrs hD)) = -1 := units_eq_neg_one_of (chiR_R hrs hD hr hs) hη
  have hSm : χ (mk (formS hrs hD)) = -1 := units_eq_neg_one_of (chiR_S hrs hD hr hs) hη
  have hR1 : mk (formR hrs hD) ≠ 1 := fun h => by
    rw [h, map_one] at hRm; exact units_one_ne_neg_one hRm
  have hR2 : mk (formR hrs hD) ^ 2 = 1 := mk_sq_of_isAmbiguousForm _ (Or.inl (by simp [formR]))
  have hM : mk (formM hrs hD) = 1 := by
    rcases one_of_three hrs hD hr hs with h | h | h
    · exact h
    · exact absurd h hR1
    · rw [h, map_one] at hSm; exact absurd hSm units_one_ne_neg_one
  have key := card_primary_eq (G := FormClass D) H (j := 0)
    ⟨mk (formR hrs hD), by simpa using orderOf_eq_prime hR2 hR1⟩ ?_
  · simpa using key
  · rintro ⟨B, hB⟩
    have hB4 : B ^ 4 = 1 := by
      have := pow_orderOf_eq_one B
      rw [hB] at this; simpa using this
    have hB2 : B ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hB]; norm_num)
    have hC : (B ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hB4
    rcases amb_classes hrs hD hr hs (B ^ 2) hC with h | h | h | h
    · exact hB2 h
    · exact hB2 (h.trans hM)
    · have := congrArg χ h
      rw [map_pow, Int.units_sq, hRm] at this
      exact units_one_ne_neg_one this
    · have := congrArg χ h
      rw [map_pow, Int.units_sq, hSm] at this
      exact units_one_ne_neg_one this

/-- **Case (i)/(ii) with $\varepsilon_r = -1$: the $2$-component has order $4$** (Cassels, Ch. 14, §6, p. 352).
Proof: $f(r) = \mathfrak A^2$ with $\chi_r(\mathfrak A) = [s/r]_4 = -1$ (`exists_root_R`), so $\mathfrak A$ has order $4$;
an element $\mathfrak B$ of order $8$ would have $\mathfrak B^4 = f(r)$ (the only class of order $2$), whence
$\mathfrak A\mathfrak B^{-2}$ has square $1$ and so $\chi_r = 1$, giving $\chi_r(\mathfrak A) = 1$, a contradiction. -/
theorem fourRS_card_four_R (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1)
    (hε : condBiquadSym r s = -1) :
    Nat.card (CommGroup.primaryComponent (FormClass D) 2) = 4 := by
  have H := amb_pair hrs hD hr hs
  set χ := charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD) with hχ
  obtain ⟨A, hA2, hAχ⟩ := exists_root_R hrs hD hr hs hη
  have hAm : χ A = -1 := units_eq_neg_one_of hAχ hε
  have hamb : ∀ Z : FormClass D, Z ^ 2 = 1 → χ Z = 1 := fun Z hZ => (chi_amb_one hrs hD hr hs hη Z hZ).1
  have hR2 : mk (formR hrs hD) ^ 2 = 1 := mk_sq_of_isAmbiguousForm _ (Or.inl (by simp [formR]))
  have hR1 : mk (formR hrs hD) ≠ 1 := fun h => by
    have := hamb A (hA2.trans h)
    rw [hAm] at this
    exact units_one_ne_neg_one this.symm
  have hAord : orderOf A = 2 ^ (1 + 1) := by
    apply orderOf_eq_prime_pow (n := 1)
    · rw [pow_one, hA2]; exact hR1
    · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hA2, hR2]
  have key := card_primary_eq (G := FormClass D) H (j := 1) ⟨A, hAord⟩ ?_
  · simpa using key
  · rintro ⟨B, hB⟩
    have hB8 : B ^ 8 = 1 := by
      have := pow_orderOf_eq_one B
      rw [hB] at this; simpa using this
    have hB4 : B ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hB]; norm_num)
    have hZ2 : (B ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact hB8
    have hZR : B ^ 4 = mk (formR hrs hD) := by
      rcases H _ _ hZ2 hR2 with h | h | h
      · exact absurd h hB4
      · exact absurd h hR1
      · exact h
    have e : (A * (B ^ 2)⁻¹) ^ 2 = A ^ 2 * (B ^ 4)⁻¹ := by rw [mul_pow, inv_pow, ← pow_mul]
    have hE : (A * (B ^ 2)⁻¹) ^ 2 = 1 := by
      rw [e, hA2, ← hZR]; exact mul_inv_cancel _
    have h1 := hamb _ hE
    have h2 : χ (B ^ 2) = 1 := by rw [map_pow, Int.units_sq]
    have h3 : A = (A * (B ^ 2)⁻¹) * B ^ 2 := (inv_mul_cancel_right A (B ^ 2)).symm
    rw [h3, map_mul, h1, h2, mul_one] at hAm
    exact units_one_ne_neg_one hAm

/-- **Case (i)/(ii) with $\varepsilon_s = -1$: the $2$-component has order $4$** (`fourRS_card_four_R` with $r$ and
$s$ exchanged). -/
theorem fourRS_card_four_S (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1)
    (hε : condBiquadSym s r = -1) :
    Nat.card (CommGroup.primaryComponent (FormClass D) 2) = 4 := by
  have hD' : D = 4 * s * r := by rw [hD]; ring
  have hη' : legendreSym r s = 1 :=
    (legendreSym.quadratic_reciprocity_one_mod_four hr (ne_two_of_mod4 hs)).symm.trans hη
  exact fourRS_card_four_R (r := s) (s := r) hrs.symm hD' hs hr hη' hε

/-- **Case (iii): the $2$-component has order at least $8$** (Cassels, Ch. 14, §6, p. 353). Proof: by the existence of
a class $\mathfrak C$ with $\chi_r(\mathfrak C) = \chi_s(\mathfrak C) = -1$ (`exists_class_neg`, Dirichlet) the kernels
of $\chi_r$ and $\chi_s$ are the squares (`exists_sq_of_chi_eq_one`); hence $f(r) = \mathfrak A_r^2$ with
$\chi_r(\mathfrak A_r) = \varepsilon_r = 1$ is a fourth power, and likewise $f(s)$. Not both $f(r)$, $f(s)$ are $1$
(else all classes of order $2$ are trivial, squaring is bijective, and $\mathfrak C$ would be a square), so one of them is
a fourth power of an element of order $8$. -/
theorem fourRS_card_ge_eight (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1)
    (h1 : condBiquadSym r s = 1) (h2 : condBiquadSym s r = 1) :
    8 ≤ Nat.card (CommGroup.primaryComponent (FormClass D) 2) := by
  obtain ⟨T, hT⟩ := exists_T hrs hD hr hs
  obtain ⟨C, hCr, hCs⟩ := exists_class_neg hrs hD hr hs
  obtain ⟨AR, hAR2, hARχ⟩ := exists_root_R hrs hD hr hs hη
  obtain ⟨AS, hAS2, hASχ⟩ := exists_root_S hrs hD hr hs hη
  obtain ⟨BR, hBR⟩ := exists_sq_of_chi_eq_one (charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD)) T hT C hCr AR
    (units_eq_one_of hARχ h1)
  obtain ⟨BS, hBS⟩ := exists_sq_of_chi_eq_one (charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD)) T hT C hCs AS
    (units_eq_one_of hASχ h2)
  have hR4 : BR ^ 4 = mk (formR hrs hD) := by
    calc BR ^ 4 = (BR ^ 2) ^ 2 := by rw [← pow_mul]
      _ = mk (formR hrs hD) := by rw [hBR, hAR2]
  have hS4 : BS ^ 4 = mk (formS hrs hD) := by
    calc BS ^ 4 = (BS ^ 2) ^ 2 := by rw [← pow_mul]
      _ = mk (formS hrs hD) := by rw [hBS, hAS2]
  have hR2 : mk (formR hrs hD) ^ 2 = 1 := mk_sq_of_isAmbiguousForm _ (Or.inl (by simp [formR]))
  have hS2 : mk (formS hrs hD) ^ 2 = 1 := mk_sq_of_isAmbiguousForm _ (Or.inl (by simp [formS]))
  by_cases hR1 : mk (formR hrs hD) = 1
  · by_cases hS1 : mk (formS hrs hD) = 1
    · exfalso
      have hM : mk (formM hrs hD) = 1 := by
        have := mk_formM_mul_formR hrs hD
        rw [hR1, mul_one, hS1] at this; exact this
      have hinj : Function.Injective (fun x : FormClass D => x ^ 2) := by
        intro x y hxy
        have hxy' : (x * y⁻¹) ^ 2 = 1 := by
          simp only at hxy
          rw [mul_pow, inv_pow, hxy, mul_inv_cancel]
        have : x * y⁻¹ = 1 := by
          rcases amb_classes hrs hD hr hs _ hxy' with h | h | h | h
          · exact h
          · rw [h, hM]
          · rw [h, hR1]
          · rw [h, hS1]
        exact mul_inv_eq_one.1 this
      obtain ⟨Y, hY⟩ := (Finite.injective_iff_surjective.1 hinj) C
      have := congrArg (charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD)) (show Y ^ 2 = C from hY)
      rw [map_pow, Int.units_sq, hCr] at this
      exact units_one_ne_neg_one this
    · exact card_ge_eight_of_fourth _ BS hS2 hS1 hS4
  · exact card_ge_eight_of_fourth _ BR hR2 hR1 hR4

/-- **Case (ii): $x^2 - rsy^2 = -1$ is insoluble** (Cassels, Ch. 14, §6, pp. 352–353, case (ii)): for $(s/r) = 1$,
$[s/r]_4 = 1$, $[r/s]_4 = -1$. Proof: if soluble then $f(-1) \sim 1$ and $f(r) \sim f(s)$. But $f(r) = \mathfrak A_r^2$
with $\chi_r(\mathfrak A_r) = 1$, so $\mathfrak A_r$ is a square (`exists_class_neg`, `exists_sq_of_chi_eq_one`), whence
$\chi_s(\mathfrak A_r) = 1$; and $f(s) = \mathfrak A_s^2$ with $\chi_s(\mathfrak A_s) = -1$; as $\mathfrak A_r^2 = \mathfrak A_s^2$,
$\mathfrak A_s\mathfrak A_r^{-1}$ has square $1$, so $\chi_s(\mathfrak A_s) = \chi_s(\mathfrak A_r) = 1$. Contradiction. -/
theorem fourRS_not_negPell (hr : r % 4 = 1) (hs : s % 4 = 1) (hη : legendreSym s r = 1)
    (h1 : condBiquadSym r s = 1) (h2 : condBiquadSym s r = -1) :
    ¬ ∃ x y : ℤ, x ^ 2 - (r * s : ℤ) * y ^ 2 = -1 := by
  rintro ⟨x, y, hxy⟩
  obtain ⟨T, hT⟩ := exists_T hrs hD hr hs
  obtain ⟨C, hCr, hCs⟩ := exists_class_neg hrs hD hr hs
  obtain ⟨AR, hAR2, hARχ⟩ := exists_root_R hrs hD hr hs hη
  obtain ⟨AS, hAS2, hASχ⟩ := exists_root_S hrs hD hr hs hη
  have hM : mk (formM hrs hD) = 1 := (formM_one_iff hrs hD).2 ⟨x, y, hxy⟩
  have hRS : mk (formR hrs hD) = mk (formS hrs hD) := by
    have := mk_formM_mul_formR hrs hD
    rw [hM, one_mul] at this; exact this
  obtain ⟨B, hB⟩ := exists_sq_of_chi_eq_one (charHom r D (ne_two_of_mod4 hr) (dvd_D_r hD)) T hT C hCr AR
    (units_eq_one_of hARχ h1)
  set χs := charHom s D (ne_two_of_mod4 hs) (dvd_D_s hD) with hχs
  have hAR : χs AR = 1 := by rw [← hB, map_pow, Int.units_sq]
  have hAS : χs AS = -1 := units_eq_neg_one_of hASχ h2
  have hE : (AS * AR⁻¹) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, hAS2, hAR2, hRS, mul_inv_cancel]
  have hE1 := (chi_amb_one hrs hD hr hs hη _ hE).2
  have h3 : AS = (AS * AR⁻¹) * AR := (inv_mul_cancel_right AS AR).symm
  rw [h3, map_mul, hE1, hAR, mul_one] at hAS
  exact units_one_ne_neg_one hAS

end Main

/-! ### The named statements -/

/-- **Case (ii): the negative Pell equation is insoluble, proved** (Cassels, Ch. 14, §6, pp. 352–353, case (ii)): the
named statement `FourRSCaseTwoNegPell` holds unconditionally. See `fourRS_not_negPell` for the proof. Unconditional. -/
@[kb "cassels1978" "Ch. 14, §6, pp. 352–353, case (ii) (x² − rsy² = −1 is not soluble; proved)"]
theorem fourRSCaseTwoNegPell_holds : FourRSCaseTwoNegPell := by
  refine ⟨fun r s _ _ hr hs hrs hη h1 h2 => ?_⟩
  have : NonzeroDisc (4 * (r : ℤ) * s) := nonzeroDisc_fourRS rfl
  exact fourRS_not_negPell hrs (rfl : (4 * (r : ℤ) * s) = 4 * r * s) hr hs hη h1 h2

/-- **The $2$-component of the class group for $D = 4rs$, proved** (Cassels, Ch. 14, §6, pp. 351–353): the named
statement `FourRSTwoComponent` holds unconditionally. The $2$-component is cyclic (`fourRS_cyclic`); of order $2$ if
$\eta = -1$ (`fourRS_card_two`); of order $4$ in cases (i), (ii) (`fourRS_card_four_R`, `fourRS_card_four_S`); and of
order at least $8$ in case (iii) (`fourRS_card_ge_eight`, which uses Dirichlet's theorem on primes in progressions,
proved in Mathlib, for the existence of the second genus). Unconditional. -/
@[kb "cassels1978" "Ch. 14, §6, pp. 351–353 (the 2-component of the class group for D = 4rs; proved)"]
theorem fourRSTwoComponent_holds : FourRSTwoComponent where
  cyclic r s _ _ _ hr hs hrs := fourRS_cyclic hrs (rfl : (4 * (r : ℤ) * s) = 4 * r * s) hr hs
  order_two r s _ _ _ hr hs hrs hη := fourRS_card_two hrs (rfl : (4 * (r : ℤ) * s) = 4 * r * s) hr hs hη
  order_four r s _ _ _ hr hs hrs hη hε := by
    rcases hε with hε | hε
    · exact fourRS_card_four_R hrs (rfl : (4 * (r : ℤ) * s) = 4 * r * s) hr hs hη hε
    · exact fourRS_card_four_S hrs (rfl : (4 * (r : ℤ) * s) = 4 * r * s) hr hs hη hε
  order_ge_eight r s _ _ _ hr hs hrs hη h1 h2 :=
    fourRS_card_ge_eight hrs (rfl : (4 * (r : ℤ) * s) = 4 * r * s) hr hs hη h1 h2



end QuadFormsKB.Composition
