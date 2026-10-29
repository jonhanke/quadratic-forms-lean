import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Literature.OMeara.Sec43E

/-!
# O'Meara §43B–§43C: consequences of the Cartan–Dieudonné theorem (43:3b, 43:12b)

**Setting** (as in `Sec43CD.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular quadratic space,
$n = \dim V$, $O(V)$ = `orth Q`, $O^+(V)$ = `orthPlus Q` (rotations, $\det = 1$), $\tau_u$ = `symmetry Q u hu`, and
`cd_prod Q l` the product $\tau_{u_1}\cdots\tau_{u_r}$ for a list $l$ of anisotropic vectors.

**Proves** (O'Meara 1973 printing, Chapter IV, pp. 104–105, 110):
* `exists_cd_prod_cons_eq` (**43:3b**): if $\sigma$ is a product of $n$ symmetries, then it is a product of $n$
  symmetries whose first symmetry is any given symmetry $\tau_u$;
* `orthPlus_comm_of_finrank_le_two` (**43:12b**, first sentence; §43C, p. 104): $O^+(V)$ is commutative when
  $n \le 2$.

**Proof notes.** Both use the sharp Cartan–Dieudonné theorem 43:3 (`cd_list`) and the parity of the number of
symmetries (`cd_det_prod`). For 43:12b with $n = 2$ we follow §43C: $\tau\sigma$ is a reflexion, hence a symmetry, so
$\tau\sigma\tau = \sigma^{-1}$ for every symmetry $\tau$ and rotation $\sigma$, and a rotation is a product of two
symmetries. The second sentence of 43:12b ($O^+$ not commutative for $n \ge 3$) needs $\Omega_n \ne 1$ and is not
formalized here.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43C

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

theorem iv_cd_prod_append (l m : List {u : V // Q u ≠ 0}) : cd_prod Q (l ++ m) = cd_prod Q l * cd_prod Q m := by
  simp [cd_prod, List.map_append, List.prod_append]

theorem iv_symmetry_mul_self {u : V} (hu : Q u ≠ 0) : symmetry Q u hu * symmetry Q u hu = 1 := by
  ext x; exact symmetry_symmetry Q hu x

theorem cd_prod_replicate_two_mul (a : {u : V // Q u ≠ 0}) (k : ℕ) :
    cd_prod Q (List.replicate (2 * k) a) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, List.replicate_add, iv_cd_prod_append, ih, one_mul]
    show symmetry Q a.1 a.2 * (symmetry Q a.1 a.2 * 1) = 1
    rw [mul_one, iv_symmetry_mul_self]

/-- **O'Meara 43:3b** (p. 104). Let $V$ be regular of dimension $n$ and suppose $\sigma = \tau_{u_1}\cdots\tau_{u_n}$ is
a product of $n$ symmetries. Then for any anisotropic $a$, $\sigma$ is a product $\tau_a\tau_{v_2}\cdots\tau_{v_n}$ of
$n$ symmetries whose first symmetry is $\tau_a$. (The book adds "or last"; that form follows in the same way and is
not stated.) -/
@[kb "omeara1963" "§43B, 43:3b, p. 104 (first symmetry arbitrary)"]
theorem exists_cd_prod_cons_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {l : List {u : V // Q u ≠ 0}}
    (hlen : l.length = finrank F V) (a : {u : V // Q u ≠ 0}) :
    ∃ l' : List {u : V // Q u ≠ 0}, cd_prod Q l = cd_prod Q (a :: l') ∧ (a :: l').length = finrank F V := by
  have hρ : symmetry Q a.1 a.2 * cd_prod Q l ∈ orth Q := by
    refine (orth Q).mul_mem (symmetry_mem_orth Q a.2) ?_
    rw [cd_prod]
    refine List.prod_induction _ (fun a b ha hb => (orth Q).mul_mem ha hb) (orth Q).one_mem ?_
    intro x hx
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact symmetry_mem_orth Q u.2
  obtain ⟨m, hm, hρm⟩ := cd_list Q hQ hρ
  have hdet : ((-1 : Fˣ)) ^ m.length = (-1) ^ (finrank F V + 1) := by
    rw [← cd_det_prod, ← hρm, ← cd_prod_cons, cd_det_prod, List.length_cons, hlen]
  have hev : Even (m.length + (finrank F V + 1)) := by
    apply (neg_one_pow_eq_one_iff_even (cd_neg_one_ne (F := F))).1
    rw [pow_add, hdet, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  obtain ⟨k, hk⟩ := hev
  have hn : 1 ≤ finrank F V := by
    by_contra h0
    push Not at h0
    have : Subsingleton V := Module.finrank_zero_iff (R := F).1 (by omega)
    exact a.2 (by rw [Subsingleton.elim a.1 0, map_zero])
  obtain ⟨j, hj⟩ : ∃ j, finrank F V - 1 - m.length = 2 * j := ⟨k - m.length - 1, by omega⟩
  refine ⟨m ++ List.replicate (2 * j) a, ?_, ?_⟩
  · rw [cd_prod_cons, iv_cd_prod_append, cd_prod_replicate_two_mul, mul_one, ← hρm, ← mul_assoc,
      iv_symmetry_mul_self, one_mul]
  · simp only [List.length_cons, List.length_append, List.length_replicate]
    omega

/-- In a regular binary space, a symmetry times a rotation is a symmetry (§43C, p. 104), hence
$\tau\sigma\tau = \sigma^{-1}$. -/
theorem symmetry_conj_rotation (hQ : (QuadraticMap.associated Q).Nondegenerate) (h2 : finrank F V = 2)
    {u : V} (hu : Q u ≠ 0) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPlus Q) :
    symmetry Q u hu * σ * symmetry Q u hu = σ⁻¹ := by
  have hρ : symmetry Q u hu * σ ∈ orth Q := (orth Q).mul_mem (symmetry_mem_orth Q hu) hσ.1
  obtain ⟨m, hm, hρm⟩ := cd_list Q hQ hρ
  have hdetσ : LinearEquiv.det σ = 1 := MonoidHom.mem_ker.mp hσ.2
  have hdet : ((-1 : Fˣ)) ^ m.length = -1 := by
    rw [← cd_det_prod, ← hρm, map_mul, hdetσ, mul_one]
    have := cd_det_prod Q [⟨u, hu⟩]
    simpa [cd_prod] using this
  have hlen : m.length = 1 := by
    rcases Nat.lt_or_ge m.length 1 with h | h
    · have : m.length = 0 := by omega
      rw [this, pow_zero] at hdet
      exact absurd hdet.symm (cd_neg_one_ne (F := F))
    · rcases Nat.lt_or_ge m.length 2 with h' | h'
      · omega
      · have : m.length = 2 := by omega
        rw [this, neg_one_sq] at hdet
        exact absurd hdet (cd_neg_one_ne (F := F)).symm
  obtain ⟨w, rfl⟩ | ⟨w, l, hl⟩ : m = [] ∨ ∃ w l, m = w :: l := by
    cases m with
    | nil => left; rfl
    | cons w l => right; exact ⟨w, l, rfl⟩
  · simp at hlen
  · subst hl
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hl0
    have hsq : (symmetry Q u hu * σ) * (symmetry Q u hu * σ) = 1 := by
      rw [hρm]; show symmetry Q w.1 w.2 * 1 * (symmetry Q w.1 w.2 * 1) = 1
      rw [mul_one, iv_symmetry_mul_self]
    calc symmetry Q u hu * σ * symmetry Q u hu
        = symmetry Q u hu * σ * symmetry Q u hu * (σ * σ⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = ((symmetry Q u hu * σ) * (symmetry Q u hu * σ)) * σ⁻¹ := by group
      _ = σ⁻¹ := by rw [hsq, one_mul]

/-- **O'Meara 43:12b** (p. 110; proof in §43C, p. 104), first sentence: if $V$ is regular with $\dim V \le 2$ then
the rotation group $O^+(V)$ is commutative. -/
@[kb "omeara1963" "§43E, 43:12b, p. 110 (O⁺ commutative for n ≤ 2)"]
theorem orthPlus_comm_of_finrank_le_two (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h2 : finrank F V ≤ 2) {σ ρ : V ≃ₗ[F] V} (hσ : σ ∈ orthPlus Q) (hρ : ρ ∈ orthPlus Q) : σ * ρ = ρ * σ := by
  rcases Nat.lt_or_ge (finrank F V) 2 with h | h
  · rcases Nat.lt_or_ge (finrank F V) 1 with h' | h'
    · have : Subsingleton V := Module.finrank_zero_iff (R := F).1 (by omega)
      ext x; exact Subsingleton.elim _ _
    · exact commutative_of_finrank_eq_one Q (by omega) σ hσ.1 ρ hρ.1
  have h2' : finrank F V = 2 := by omega
  obtain ⟨m, hm, hρm⟩ := cd_list Q hQ hρ.1
  have hdet : LinearEquiv.det ρ = 1 := MonoidHom.mem_ker.mp hρ.2
  rw [hρm, cd_det_prod] at hdet
  have hev := (neg_one_pow_eq_one_iff_even (cd_neg_one_ne (F := F))).1 hdet
  obtain ⟨k, hk⟩ := hev
  rcases Nat.lt_or_ge m.length 1 with h0 | h0
  · have : m = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [hρm]; simp
  · obtain ⟨a, b, rfl⟩ : ∃ a b, m = [a, b] := by
      match m, hm, h0, hk with
      | [a, b], _, _, _ => exact ⟨a, b, rfl⟩
      | [], _, h0, _ => simp at h0
      | [_], _, _, hk => simp at hk; omega
      | _ :: _ :: _ :: _, hm, _, _ => simp at hm; omega
    have hρ' : ρ = symmetry Q a.1 a.2 * symmetry Q b.1 b.2 := by
      rw [hρm]; show _ * (_ * 1) = _; rw [mul_one]
    have hb := symmetry_conj_rotation Q hQ h2' b.2 hσ
    have hσinv : σ⁻¹ ∈ orthPlus Q := (orthPlus Q).inv_mem hσ
    have ha := symmetry_conj_rotation Q hQ h2' a.2 hσinv
    rw [inv_inv] at ha
    -- ρσρ⁻¹ = τ_a τ_b σ τ_b τ_a = τ_a σ⁻¹ τ_a = σ
    have hbb := iv_symmetry_mul_self Q b.2
    have haa := iv_symmetry_mul_self Q a.2
    rw [hρ']
    calc σ * (symmetry Q a.1 a.2 * symmetry Q b.1 b.2)
        = (symmetry Q a.1 a.2 * σ⁻¹ * symmetry Q a.1 a.2) * (symmetry Q a.1 a.2 * symmetry Q b.1 b.2) := by
          rw [ha]
      _ = symmetry Q a.1 a.2 * σ⁻¹ * (symmetry Q a.1 a.2 * symmetry Q a.1 a.2) * symmetry Q b.1 b.2 := by
          group
      _ = symmetry Q a.1 a.2 * (symmetry Q b.1 b.2 * σ * symmetry Q b.1 b.2) * symmetry Q b.1 b.2 := by
          rw [haa, mul_one, hb]
      _ = symmetry Q a.1 a.2 * symmetry Q b.1 b.2 * σ * (symmetry Q b.1 b.2 * symmetry Q b.1 b.2) := by
          group
      _ = symmetry Q a.1 a.2 * symmetry Q b.1 b.2 * σ := by rw [hbb, mul_one]

end Sec43C

end QuadFormsKB.OMeara
