/-
# Shimura 2004, Theorem 3.6 (ii), last clause: the center of $A^+(V)$ meets $G^+(V)$ in $F^\times \cup F^\times z$


**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I: Theorem 3.6 (ii)
(printed p. 22), using Theorem 2.8 (i) (printed p. 19). Page numbers are printed pages.

**Setting and dictionary.** As in `QuadFormsKB/Literature/Shimura2004/Wave2/Center.lean`: $F$ a field of
characteristic $\ne 2$, `Q : QuadraticForm F V` nondegenerate (`hQ`), $A(V)$ = `CliffordAlgebra Q`, $A^+(V)$ =
`evenOdd Q 0`, $G^+(V)$ = `Cassels.M0 Q` (a subgroup of the units of $A(V)$), and $z = h_1\cdots h_n$ =
`orthProd Q (List.ofFn h)` for an orthogonal basis `h : Fin n → V` (`horth`: pairwise orthogonal, `hspan`: spanning,
`hanis`: $\varphi[h_i] \ne 0$). *Indexing:* Shimura's $h_1, \dots, h_n$ are `h 0`, ..., `h (n-1)` here. The
dimension $n$ is even (`hn : Even n`). The center $\mathfrak{c}^+$ of $A^+(V)$ is described by Theorem 2.8 (i)
(`theorem_2_8_i_center`): an element of $A^+(V)$ is central in $A^+(V)$ iff it is $c + dz$ with $c, d \in F$.
The statement "$\mathfrak{c}^+ \cap G^+(V)$" is formalized for a unit `a : (CliffordAlgebra Q)ˣ` that lies in $A^+(V)$
and commutes with every element of $A^+(V)$ (hypotheses `ha`, `hcomm`); that $a$ then is a unit of $\mathfrak{c}^+$
follows because the inverse of such an $a$ is again even and central in $A^+(V)$ (used in the case $n = 2$).

**Proves** (all unconditional; standard axioms only)
* $n > 2$ (`theorem_3_6_ii_center_inter_G_plus`): such a unit lies in $G^+(V)$ if and only if it is
  $c$ or $cz$ for some $c \in F^\times$, i.e. $\mathfrak{c}^+ \cap G^+(V) = F^\times \cup F^\times z$.
  Key step (`orthProd_vec_ne`): for $n \ge 3$ the element $h_0 z$ is not a vector.
* $n = 2$ (`theorem_3_6_ii_center_inter_G_plus_two`): every such unit lies in $G^+(V)$, i.e.
  $\mathfrak{c}^+ \cap G^+(V) = (\mathfrak{c}^+)^\times$.
-/
import QuadFormsKB.Literature.Shimura2004.Wave2.Center
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-! ### Algebraic identities in $F + Fz$ -/

section Identities

/-- $(x + yz)(x - yz) = x^2 - y^2 s$ when $z^2 = s$. -/
theorem sq_aux1 {z : A} {s : F} (hz : z * z = algebraMap F A s) (x y : F) :
    (algebraMap F A x + y • z) * (algebraMap F A x - y • z) = algebraMap F A (x * x - y * y * s) := by
  simp only [Algebra.algebraMap_eq_smul_one] at hz ⊢
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hz]
  module

/-- $(x - yz)^2 = (x^2 + y^2 s) - 2xy\,z$ when $z^2 = s$. -/
theorem sq_aux2 {z : A} {s : F} (hz : z * z = algebraMap F A s) (x y : F) :
    (algebraMap F A x - y • z) * (algebraMap F A x - y • z) =
      algebraMap F A (x * x + y * y * s) - (2 * x * y) • z := by
  simp only [Algebra.algebraMap_eq_smul_one] at hz ⊢
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hz]
  module

/-- $(x - yz)(x' + y'z) = (xx' - yy's) + (xy' - yx')z$ when $z^2 = s$. -/
theorem sq_aux3 {z : A} {s : F} (hz : z * z = algebraMap F A s) (x y x' y' : F) :
    (algebraMap F A x - y • z) * (algebraMap F A x' + y' • z) =
      algebraMap F A (x * x' - y * y' * s) + (x * y' - y * x') • z := by
  simp only [Algebra.algebraMap_eq_smul_one] at hz ⊢
  simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hz]
  module

end Identities

/-- A vector $u$ whose image commutes with $\iota(v)$ satisfies $\varphi(v,u)\,v = 2\varphi[v]\,u$
(where `polar Q v u` is $2\varphi(v,u)$). -/
theorem vec_eq_smul_of_commute {u v : V} (hc : ι Q u * ι Q v = ι Q v * ι Q u) :
    QuadraticMap.polar Q v u • v = (2 * Q v) • u := by
  apply cliffordι_injective Q
  have e1 : ι Q v * ι Q u * ι Q v = ι Q (QuadraticMap.polar Q v u • v - Q v • u) := ι_mul_ι_mul_ι v u
  have e2 : ι Q v * ι Q u * ι Q v = Q v • ι Q u := by
    rw [← hc, mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have e3 := e1.symm.trans e2
  rw [map_sub, map_smul, map_smul] at e3
  rw [map_smul, map_smul, mul_smul, two_smul]
  exact sub_eq_iff_eq_add.1 e3

section Center

variable {n : ℕ} (h : Fin n → V)

/-- For $n$ even and positive, $z$ anticommutes with every vector. -/
theorem orthProd_mul_ι_even (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hn : Even n) (hpos : 0 < n) (y : V) :
    orthProd Q (List.ofFn h) * ι Q y = -(ι Q y * orthProd Q (List.ofFn h)) := by
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k - 1, by omega⟩
  rw [vec_mul_orthProd h horth hspan y, hodd.neg_one_pow, neg_smul, one_smul, neg_neg]

/-- **Key step.** For $n \ge 3$ even, $h_0 z$ is not in the image of $V$ in $A(V)$. -/
theorem orthProd_vec_ne (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hanis : ∀ i, Q (h i) ≠ 0) (hn : Even n) (hn2 : 2 < n)
    (u : V) : ι Q u ≠ ι Q (h ⟨0, by omega⟩) * orthProd Q (List.ofFn h) := by
  intro heq
  obtain ⟨s, hs0, hs⟩ := orthProd_sq_ne_zero h horth hanis
  have hanti := orthProd_mul_ι_even h horth hspan hn (by omega)
  set z := orthProd Q (List.ofFn h) with hzdef
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  have hcomm : ∀ j : Fin n, j ≠ i0 → ι Q u * ι Q (h j) = ι Q (h j) * ι Q u := by
    intro j hj
    have o : Q.IsOrtho (h j) (h i0) := isOrtho_of_polar_eq_zero (horth _ _ hj)
    rw [heq]
    calc ι Q (h i0) * z * ι Q (h j) = ι Q (h i0) * (z * ι Q (h j)) := mul_assoc _ _ _
      _ = ι Q (h i0) * (-(ι Q (h j) * z)) := by rw [hanti]
      _ = -(ι Q (h i0) * ι Q (h j)) * z := by rw [mul_neg, neg_mul, mul_assoc]
      _ = (ι Q (h j) * ι Q (h i0)) * z := by rw [ι_mul_ι_comm_of_isOrtho o]
      _ = ι Q (h j) * (ι Q (h i0) * z) := mul_assoc _ _ _
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i1, i0, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [i2, i0, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have k1 := vec_eq_smul_of_commute (hcomm i1 h10)
  have k2 := vec_eq_smul_of_commute (hcomm i2 h20)
  have two : (2 : F) ≠ 0 := Invertible.ne_zero (2 : F)
  -- pair `k1` with `h i2`
  have p2 : QuadraticMap.polar Q (h i2) u = 0 := by
    have := congrArg (QuadraticMap.polar Q (h i2)) k1
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, horth _ _ h12.symm] at this
    simp only [smul_eq_mul, mul_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (mul_ne_zero two (hanis i1))
  have hu0 : u = 0 := by
    rw [p2, zero_smul] at k2
    exact (smul_eq_zero.1 k2.symm).resolve_left (mul_ne_zero two (hanis i2))
  rw [hu0, map_zero] at heq
  have hsq : ι Q (h i0) * z * (ι Q (h i0) * z) = algebraMap F A (-(Q (h i0) * s)) := by
    calc ι Q (h i0) * z * (ι Q (h i0) * z) = ι Q (h i0) * (z * ι Q (h i0)) * z := by simp only [mul_assoc]
      _ = -(ι Q (h i0) * ι Q (h i0) * (z * z)) := by rw [hanti]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = _ := by rw [ι_sq_scalar, hs, ← map_mul, map_neg]
  rw [← heq, mul_zero] at hsq
  have := (algebraMap F A).injective (hsq.symm.trans (map_zero _).symm)
  exact mul_ne_zero (hanis i0) hs0 (neg_eq_zero.1 this)

/-- **Theorem 3.6 (ii)**, last clause (Shimura 2004, p. 22), case $n > 2$ even. A unit $a$ of $A(V)$ that lies in
$A^+(V)$ and commutes with all of $A^+(V)$ (so $a \in \mathfrak{c}^+$ and $a$ is a unit) lies in $G^+(V)$ if and only
if $a = c$ or $a = cz$ for some $c \in F^\times$, where $z = h_1 \cdots h_n$ (here $h_0 \cdots h_{n-1}$). That is,
$\mathfrak{c}^+ \cap G^+(V) = F^\times \cup F^\times z$. -/
@[kb "shimura2004" "Thm. 3.6 (ii), p. 22 (𝔠⁺ ∩ G⁺(V) = F^× ∪ F^×z for n > 2 even)"]
theorem theorem_3_6_ii_center_inter_G_plus (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hanis : ∀ i, Q (h i) ≠ 0) (hn : Even n) (hn2 : 2 < n)
    (a : (CliffordAlgebra Q)ˣ) (ha : (a : A) ∈ evenOdd Q 0)
    (hcomm : ∀ g ∈ evenOdd Q 0, (a : A) * g = g * (a : A)) :
    a ∈ M0 Q ↔ ∃ c : F, c ≠ 0 ∧
      ((a : A) = algebraMap F A c ∨ (a : A) = c • orthProd Q (List.ofFn h)) := by
  obtain ⟨s, hs0, hs⟩ := orthProd_sq_ne_zero h horth hanis
  have hanti := orthProd_mul_ι_even h horth hspan hn (by omega)
  have hz0 : orthProd Q (List.ofFn h) ∈ evenOdd Q 0 := by
    have := orthProd_mem_evenOdd (Q := Q) (List.ofFn h)
    rwa [List.length_ofFn, (ZMod.natCast_eq_zero_iff_even).2 hn] at this
  constructor
  · intro hM
    obtain ⟨x, y, hxy⟩ := (theorem_2_8_i_center h hQ horth hspan hanis hn (by omega) a ha).1 hcomm
    set z := orthProd Q (List.ofFn h) with hzdef
    set i0 : Fin n := ⟨0, by omega⟩ with hi0
    have hax : ∀ v : V, (a : A) * ι Q v = ι Q v * (algebraMap F A x - y • z) := by
      intro v
      rw [hxy, add_mul, smul_mul_assoc, hanti, mul_sub, smul_neg, mul_smul_comm, ← Algebra.commutes]
      simp [sub_eq_add_neg]
    have ha0 : (a : A) ≠ 0 := a.ne_zero
    by_cases hxy0 : x * y = 0
    · rcases mul_eq_zero.1 hxy0 with hx | hy
      · refine ⟨y, ?_, Or.inr ?_⟩
        · rintro rfl
          apply ha0
          rw [hxy, hx]; simp
        · rw [hxy, hx]; simp
      · refine ⟨x, ?_, Or.inl ?_⟩
        · rintro rfl
          apply ha0
          rw [hxy, hy]; simp
        · rw [hxy, hy]; simp
    · exfalso
      obtain ⟨w, hw⟩ := hM.2 (h i0)
      have hba : ι Q w * (a : A) = ι Q (h i0) * (algebraMap F A x - y • z) := by
        rw [hw, mul_assoc, Units.inv_mul, mul_one, hax]
      have haa : (a : A) * (algebraMap F A x - y • z) = algebraMap F A (x * x - y * y * s) := by
        rw [hxy]; exact sq_aux1 hs x y
      have e1 : ι Q w * (a : A) * (algebraMap F A x - y • z) =
          ι Q (h i0) * (algebraMap F A x - y • z) * (algebraMap F A x - y • z) := by rw [hba]
      rw [mul_assoc, haa, ← Algebra.commutes, ← Algebra.smul_def, mul_assoc (ι Q (h i0)), sq_aux2 hs, mul_sub,
        ← Algebra.commutes, ← Algebra.smul_def, mul_smul_comm] at e1
      have e2 : (2 * x * y) • (ι Q (h i0) * z) =
          (x * x + y * y * s) • ι Q (h i0) - (x * x - y * y * s) • ι Q w := by
        rw [e1]; abel
      have hne : 2 * x * y ≠ 0 := mul_ne_zero (Invertible.ne_zero (2 : F)) hxy0 |> fun t => by
        simpa [mul_assoc] using t
      refine orthProd_vec_ne h horth hspan hanis hn hn2
        ((2 * x * y)⁻¹ • ((x * x + y * y * s) • h i0 - (x * x - y * y * s) • w)) ?_
      rw [map_smul, map_sub, map_smul, map_smul, ← e2, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · rintro ⟨c, hc0, hc⟩
    have hl : ∀ y ∈ List.ofFn h, Q y ≠ 0 := by
      intro y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact hanis i
    have hev : Even (List.ofFn h).length := by simpa using hn
    rcases hc with hc | hc
    · have : a = Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc0) := Units.ext (by simpa using hc)
      rw [this]
      exact scalar_mem_M0 _
    · have hzM : ((vecProd (List.ofFn h) hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) ∈ M0 Q :=
        ⟨vecProd_mem_even hl hev, (vecProd (List.ofFn h) hl).2⟩
      have : a = Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc0) *
          ((vecProd (List.ofFn h) hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) := by
        apply Units.ext
        rw [Units.val_mul, coe_vecProd_eq_prod, hc, Algebra.smul_def]
        rfl
      rw [this]
      exact (M0 Q).mul_mem (scalar_mem_M0 _) hzM

/-- For $n = 2$, $\iota(v)\,z$ is a vector for every $v \in V$ (the vectors $h_0, h_1$ span $V$). -/
theorem ι_mul_orthProd_mem_range_two (h : Fin 2 → V)
    (hspan : Submodule.span F (Set.range h) = ⊤) (v : V) :
    ∃ w : V, ι Q w = ι Q v * orthProd Q (List.ofFn h) := by
  have hz2 : orthProd Q (List.ofFn h) = ι Q (h 0) * ι Q (h 1) := by
    simp [orthProd, List.ofFn_succ]
  have hv : v ∈ Submodule.span F (Set.range h) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [hz2]
    fin_cases i
    · refine ⟨Q (h 0) • h 1, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, map_smul]
      rw [← mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    · refine ⟨QuadraticMap.polar Q (h 1) (h 0) • h 1 - Q (h 1) • h 0, ?_⟩
      simp only [Fin.mk_one, Fin.isValue]
      rw [← mul_assoc, ι_mul_ι_mul_ι]
  | zero => exact ⟨0, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨w', hw'⟩ := hw
    exact ⟨y' + w', by rw [map_add, hy', hw', map_add, add_mul]⟩
  | smul c y _ hy =>
    obtain ⟨y', hy'⟩ := hy
    exact ⟨c • y', by rw [map_smul, hy', map_smul, smul_mul_assoc]⟩

/-- **Theorem 3.6 (ii)**, last clause (Shimura 2004, p. 22), case $n = 2$. Every unit $a$ of $A(V)$ that lies in
$A^+(V)$ and commutes with all of $A^+(V)$ lies in $G^+(V)$; since the inverse of such an $a$ is again even and
central in $A^+(V)$, this says $\mathfrak{c}^+ \cap G^+(V) = (\mathfrak{c}^+)^\times$. -/
@[kb "shimura2004" "Thm. 3.6 (ii), p. 22 (𝔠⁺ ∩ G⁺(V) = (𝔠⁺)^× for n = 2)"]
theorem theorem_3_6_ii_center_inter_G_plus_two (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h : Fin 2 → V) (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hanis : ∀ i, Q (h i) ≠ 0)
    (a : (CliffordAlgebra Q)ˣ) (ha : (a : A) ∈ evenOdd Q 0)
    (hcomm : ∀ g ∈ evenOdd Q 0, (a : A) * g = g * (a : A)) :
    a ∈ M0 Q := by
  have hn : Even 2 := even_two
  obtain ⟨s, hs0, hs⟩ := orthProd_sq_ne_zero h horth hanis
  have hanti := orthProd_mul_ι_even h horth hspan hn (by omega)
  have hai : ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 0 := mem_evenOdd_of_mul_eq_one Q ha a.mul_inv
  have hcomm' : ∀ g ∈ evenOdd Q 0, ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * g = g * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) := by
    intro g hg
    calc ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * g = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * g * ((a : A) * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * (g * (a : A)) * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) := by
          simp only [mul_assoc]
      _ = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ((a : A) * g) * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) := by
          rw [hcomm g hg]
      _ = g * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨x, y, hxy⟩ := (theorem_2_8_i_center h hQ horth hspan hanis hn (by omega) a ha).1 hcomm
  obtain ⟨x', y', hxy'⟩ :=
    (theorem_2_8_i_center h hQ horth hspan hanis hn (by omega) _ hai).1 hcomm'
  refine ⟨ha, fun v => ?_⟩
  set z := orthProd Q (List.ofFn h) with hzdef
  obtain ⟨w0, hw0⟩ := ι_mul_orthProd_mem_range_two (Q := Q) h hspan v
  have hax : (a : A) * ι Q v = ι Q v * (algebraMap F A x - y • z) := by
    rw [hxy, add_mul, smul_mul_assoc, hanti, mul_sub, smul_neg, mul_smul_comm, ← Algebra.commutes]
    simp [sub_eq_add_neg]
  refine ⟨(x * x' - y * y' * s) • v + (x * y' - y * x') • w0, ?_⟩
  rw [hax, mul_assoc (ι Q v), hxy', sq_aux3 hs, mul_add, ← Algebra.commutes, ← Algebra.smul_def, mul_smul_comm, map_add,
    map_smul, map_smul, hw0]

end Center

end QuadFormsKB.Shimura2004
