/-
# Weak approximation for products of symmetries and on a quadric

**Layer:** $V = F^n$ with `Q : QuadForm F n` over a number field $F$, completions $V_\mathfrak p$ at finite primes.

**Proves**
* `exists_symmProd_approx`: products $\tau_{x_1}\cdots\tau_{x_m}$ of local symmetries at finitely many primes (lists of a
  common length) are simultaneously approximated by a product of global symmetries (weak approximation for $O(V)$ in
  the form needed; O'Meara 1973, 101:7 [unverified]);
* `exists_quadric_approx`: **weak approximation on the quadric $Q(z) = a$** given one global point $u$: local points
  $z_\mathfrak p$ ($\mathfrak p \in T$) are approximated by a global $w$ with $Q(w) = a$. Each $z_\mathfrak p$ is
  $\tau_{z-u}\tau_y u$ or $\tau_{z+u}\tau_u u$ with $y \perp u$ (step 2 of O'Meara 104:3, p. 312, where O'Meara uses Witt's
  theorem and weak approximation for rotations instead).
-/
import QuadFormsKB.Lattices.SACorrection

open NumberField IsDedekindDomain Matrix Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

theorem symmProd_cons {K : Type*} [Field K] [Algebra F K] [CharZero K] (a : Fin n → K) (l : List (Fin n → K)) :
    symmProd Q K (a :: l) = symm Q K a * symmProd Q K l := by
  simp [symmProd]

/-- **Weak approximation for products of symmetries** at finitely many primes. -/
theorem exists_symmProd_approx (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ (m : ℕ) (l : ∀ v : HeightOneSpectrum (𝓞 F), List (Fin n → v.adicCompletion F)),
      (∀ v ∈ T, (l v).length = m ∧ ∀ x ∈ l v, Q.evalIn _ x ≠ 0) →
      ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)),
        (∀ v ∈ T, U v ∈ 𝓝 (omat (symmProd Q _ (l v)))) →
        ∃ ys : List (Fin n → F), ys.length = m ∧
          ∀ v ∈ T, omat (symmProd Q _ (ys.map (locVec v))) ∈ U v := by
  classical
  intro m
  induction m with
  | zero =>
    intro l hl U hU
    refine ⟨[], rfl, fun v hv => ?_⟩
    have := hU v hv
    rw [List.length_eq_zero_iff.mp (hl v hv).1] at this
    simpa using mem_of_mem_nhds this
  | succ m ih =>
    intro l hl U hU
    have hcons : ∀ v ∈ T, l v = (l v).headD 0 :: (l v).tail := by
      intro v hv
      obtain ⟨a, l', hal⟩ := List.exists_cons_of_length_eq_add_one (hl v hv).1
      rw [hal]; rfl
    -- split the neighbourhoods
    have hsplit : ∀ v ∈ T, ∃ A ∈ 𝓝 (omat (symm Q (v.adicCompletion F) ((l v).headD 0))),
        ∃ B ∈ 𝓝 (omat (symmProd Q _ (l v).tail)), ∀ M ∈ A, ∀ N ∈ B, M * N ∈ U v := by
      intro v hv
      have hU' : U v ∈ 𝓝 (omat (symm Q (v.adicCompletion F) ((l v).headD 0)) *
          omat (symmProd Q _ (l v).tail)) := by
        have := hU v hv
        rwa [hcons v hv, symmProd_cons, omat_mul] at this
      have h := (continuous_matmul_joint v).continuousAt (x := (omat (symm Q (v.adicCompletion F) ((l v).headD 0)),
        omat (symmProd Q _ (l v).tail))) |>.preimage_mem_nhds hU'
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp h
      refine ⟨A, hA, B, hB, fun M hM N hN => ?_⟩
      have := hAB (Set.mk_mem_prod hM hN)
      simpa only [Set.mem_preimage] using this
    choose! A hA B hB hAB using hsplit
    obtain ⟨ys, hlen, hys⟩ := ih (fun v => (l v).tail) (fun v hv =>
      ⟨by rw [List.length_tail, (hl v hv).1]; rfl, fun x hx => (hl v hv).2 x (List.mem_of_mem_tail hx)⟩) B hB
    obtain ⟨y, hyT, -⟩ := exists_vec_approx T (fun v => (l v).headD 0)
      (fun v => {y | omat (symm Q (v.adicCompletion F) y) ∈ A v}) fun v hv =>
        (continuousAt_symm v Q ((hl v hv).2 _ (by rw [hcons v hv]; exact List.mem_cons_self))).preimage_mem_nhds
          (hA v hv)
    refine ⟨y :: ys, by rw [List.length_cons, hlen], fun v hv => ?_⟩
    rw [List.map_cons, symmProd_cons, omat_mul]
    exact hAB v hv _ (hyT v hv) _ (hys v hv)

/-- **An anisotropic vector orthogonal to a given anisotropic vector** ($Q$ nondegenerate, $n \ge 2$). -/
theorem exists_perp_aniso (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {u : Fin n → F} (hu : Q.evalIn F u ≠ 0) :
    ∃ y, qbil Q F u y = 0 ∧ Q.evalIn F y ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- every vector orthogonal to `u` is isotropic, hence `u^⊥` is totally isotropic
  have hiso : ∀ y z, qbil Q F u y = 0 → qbil Q F u z = 0 → qbil Q F y z = 0 := by
    intro y z hy hz
    have h1 := hcon y hy
    have h2 := hcon z hz
    have h3 := hcon (y + z) (by rw [qbil_add_right, hy, hz, add_zero])
    have := evalIn_add_smul Q F y z 1
    rw [one_smul, h1, h2, h3, one_mul, one_pow, one_mul, zero_add, add_zero] at this
    exact this.symm
  -- a nonzero vector orthogonal to `u`
  let e : Fin n → Fin n → F := fun i => Pi.single i 1
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨y, hy0, hyu⟩ : ∃ y : Fin n → F, y ≠ 0 ∧ qbil Q F u y = 0 := by
    by_cases h : qbil Q F u (e i0) = 0
    · exact ⟨e i0, by simp [e], h⟩
    · refine ⟨qbil Q F u (e i1) • e i0 - qbil Q F u (e i0) • e i1, fun h0 => h ?_, ?_⟩
      · have := congrFun h0 i1
        simpa [e, h01, Ne.symm h01] using this
      · rw [show qbil Q F u (qbil Q F u (e i1) • e i0 - qbil Q F u (e i0) • e i1) =
            qbil Q F u (qbil Q F u (e i1) • e i0 + (-qbil Q F u (e i0)) • e i1) by rw [neg_smul, sub_eq_add_neg],
          qbil_add_right, qbil_smul_right, qbil_smul_right]
        ring
  apply hy0
  refine eq_zero_of_qbil_eq_zero hQ fun x => ?_
  -- decompose `x = c u + x'` with `x' ⊥ u`
  set c := qbil Q F u x / qbil Q F u u
  have huu : qbil Q F u u ≠ 0 := by rw [qbil_self]; exact mul_ne_zero two_ne_zero hu
  have hx' : qbil Q F u (x - c • u) = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, qbil_add_right, qbil_smul_right]
    simp only [c]; field_simp; ring
  have : x = c • u + (x - c • u) := by abel
  rw [this, qbil_add_right, qbil_smul_right, qbil_comm, hyu, mul_zero, zero_add]
  exact hiso y _ hyu hx'

/-- **Weak approximation on the quadric $Q(z) = a$** from one global point $u$ ($n \ge 2$, $Q$ nondegenerate). -/
theorem exists_quadric_approx (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {u : Fin n → F} (hu : Q.evalIn F u ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (z : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hz : ∀ v ∈ T, Q.evalIn _ (z v) = algebraMap F _ (Q.evalIn F u))
    (Z : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) (hZ : ∀ v ∈ T, Z v ∈ 𝓝 (z v)) :
    ∃ w : Fin n → F, Q.evalIn F w = Q.evalIn F u ∧ ∀ v ∈ T, locVec v w ∈ Z v := by
  classical
  obtain ⟨y, hyu, hy⟩ := exists_perp_aniso Q hQ hn hu
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : Fin n → F,
      Q.evalIn (v.adicCompletion F) (locVec v x) = algebraMap F _ (Q.evalIn F x) := fun v x => evalIn_locVec Q v x
  -- local words
  have hword : ∀ v ∈ T, ∃ l : List (Fin n → v.adicCompletion F), l.length = 2 ∧
      (∀ x ∈ l, Q.evalIn _ x ≠ 0) ∧ omat (symmProd Q _ l) *ᵥ locVec v u = z v := by
    intro v hv
    have huK : Q.evalIn (v.adicCompletion F) (locVec v u) ≠ 0 := by rw [hloc]; exact (map_ne_zero _).mpr hu
    have hzu : Q.evalIn (v.adicCompletion F) (z v) = Q.evalIn (v.adicCompletion F) (locVec v u) := by rw [hz v hv, hloc]
    by_cases h : Q.evalIn (v.adicCompletion F) (z v - locVec v u) ≠ 0
    · refine ⟨[z v - locVec v u, locVec v y], rfl, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact h
        · rw [hloc]; exact (map_ne_zero _).mpr hy
      · simp only [symmProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, omat_mul,
          ← mulVec_mulVec]
        have hyK : Q.evalIn (v.adicCompletion F) (locVec v y) ≠ 0 := by rw [hloc]; exact (map_ne_zero _).mpr hy
        have hperp : qbil Q (v.adicCompletion F) (locVec v y) (locVec v u) = 0 := by
          have : qbil Q (v.adicCompletion F) (locVec v y) (locVec v u) = algebraMap F (v.adicCompletion F) (qbil Q F y u) := by
            simp only [qbil, locVec_eq, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
            simp [Algebra.algebraMap_self]
          rw [this, qbil_comm, hyu, map_zero]
        rw [symm_mulVec_bil Q (v.adicCompletion F) hyK, hperp, zero_div, zero_smul, sub_zero]
        exact symm_sub_apply Q (v.adicCompletion F) hzu h
    · have h4 := evalIn_sub_add_evalIn_add Q (v.adicCompletion F) hzu
      have h' : Q.evalIn (v.adicCompletion F) (z v + locVec v u) ≠ 0 := by
        intro h0
        rw [not_not.mp h, h0, add_zero, hzu] at h4
        have : (4 : v.adicCompletion F) ≠ 0 := by norm_num
        exact huK ((mul_eq_zero.mp h4.symm).resolve_left this)
      refine ⟨[z v + locVec v u, locVec v u], rfl, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact h'
        · exact huK
      · simp only [symmProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, omat_mul,
          ← mulVec_mulVec]
        rw [symm_mulVec_bil Q (v.adicCompletion F) huK (locVec v u), qbil_self,
          mul_div_assoc, div_self huK, mul_one,
          show locVec v u - (2 : v.adicCompletion F) • locVec v u = -locVec v u by rw [two_smul]; abel, mulVec_neg,
          symm_add_apply Q (v.adicCompletion F) hzu h', neg_neg]
  choose! l hl2 hla hlu using hword
  have hcont : ∀ v : HeightOneSpectrum (𝓞 F),
      Continuous fun M : Matrix (Fin n) (Fin n) (v.adicCompletion F) => M *ᵥ locVec v u := fun v =>
    continuous_id.matrix_mulVec continuous_const
  obtain ⟨ys, -, hys⟩ := exists_symmProd_approx Q T 2 l (fun v hv => ⟨hl2 v hv, hla v hv⟩)
    (fun v => {M | M *ᵥ locVec v u ∈ Z v})
    (fun v hv => (hcont v).continuousAt.preimage_mem_nhds (by rw [hlu v hv]; exact hZ v hv))
  set g := symmProd Q F ys
  refine ⟨((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ u, evalIn_mulVec_of_mem Q g.2 u, fun v hv => ?_⟩
  have := hys v hv
  rw [← orthMap_symmProd] at this
  have e : locVec v (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ u) =
      omat (orthMap Q (v.adicCompletion F) g) *ᵥ locVec v u := by
    funext i
    simp only [locVec_eq, mulVec, dotProduct, map_sum, map_mul]
    rfl
  rw [e]; exact this

end QuadFormsKB.Lattices
