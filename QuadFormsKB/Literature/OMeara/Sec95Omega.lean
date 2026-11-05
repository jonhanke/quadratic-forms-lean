/-
# O'Meara §95: general lemmas on $\Omega_n$ used in the proof of 95:1

**Setting.** A field $F$ with $2 \ne 0$ (`Invertible (2 : F)`), a finite-dimensional quadratic space $(V, Q)$ over
$F$, regular meaning `(QuadraticMap.associated Q).Nondegenerate`, O'Meara's bilinear form $B$ = `bil Q`, the
symmetries $\tau_u$ (`symmetry`), their products $\tau_{u_1}\cdots\tau_{u_r}$ (`symProd`), $\Omega(V)$ (`omega`, the
commutator subgroup of $O(V)$) and $O'(V)$ (`orthPrime`), as in `Sec55.lean`.

**Proves** the two facts that the proof of Proposition 95:1 (O'Meara 1973 printing, pp. 281–282) uses over and
over:
* `S95.symProd_mul_inv_mem_omega_of_sq`: the coset $\tau_{(\alpha_1)}\cdots\tau_{(\alpha_r)}\Omega$ depends only on the
  square classes of the $\alpha_i$ (step 1 of the proof: "$\tau_{(\alpha)}\Omega_4$ is well-defined in virtue of
  Proposition 55:3", together with $\tau_{tx} = \tau_x$); `S95.symmetry_mul_symmetry_mem_omega`: $\tau_x\tau_y \in
  \Omega$ when $Q(x)Q(y) \in F^{\times 2}$ (step 3: $\tau_{(\alpha_i)}\tau_{(\alpha_i)}\Omega_4 = \Omega_4$);
* `S95.mem_omega_of_lift`: if $\sigma = \tau_{u_1}\cdots\tau_{u_r} \in O'(V)$ and a regular subspace $U$ with
  $\Omega(U) = O'(U)$ represents $Q(u_1), \dots, Q(u_r)$, then $\sigma \in \Omega(V)$ (step 2: "each of the
  symmetries appearing in this equation is with respect to a line in $U$. But $O'_3(U) = \Omega_3(U)$").
-/
import QuadFormsKB.Literature.OMeara.Sec55

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54

namespace S95

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Rescaling the vectors of a factorization by non-zero scalars does not change the product of symmetries. -/
theorem symProd_smul_eq : ∀ (w : List V) (t : List F) (hw : ∀ u ∈ w, Q u ≠ 0) (_ht : ∀ s ∈ t, s ≠ 0)
    (_hlen : t.length = w.length) (hw' : ∀ u ∈ List.zipWith (· • ·) t w, Q u ≠ 0),
    symProd Q (List.zipWith (· • ·) t w) hw' = symProd Q w hw
  | [], _, _, _, _, _ => by simp [symProd]
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | b :: w, s :: t, hw, ht, hlen, hw' => by
    simp only [List.zipWith_cons_cons] at hw' ⊢
    rw [symProd_cons Q hw', symProd_cons Q hw]
    have hs : s ≠ 0 := ht s List.mem_cons_self
    rw [Sp55.symmetry_smul_vec Q hs (hw b List.mem_cons_self)]
    congr 1
    exact symProd_smul_eq w t (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      (fun u hu => ht u (List.mem_cons_of_mem _ hu)) (by simpa using hlen) _

/-- **The coset $\tau_{(\alpha_1)}\cdots\tau_{(\alpha_r)}\Omega$ depends only on the square classes of the
$\alpha_i$** (O'Meara 1973, proof of 95:1, step 1, p. 281, from 55:3): if $Q(u_i) = s_i^2 Q(w_i)$ with $s_i \ne 0$,
then $\tau_{u_1}\cdots\tau_{u_r}(\tau_{w_1}\cdots\tau_{w_r})^{-1} \in \Omega(V)$. -/
@[kb "omeara1963" "§95, proof of 95:1, step 1, p. 281 (τ_(α) Ω is well defined)"]
theorem symProd_mul_inv_mem_omega_of_sq (hQ : (QuadraticMap.associated Q).Nondegenerate) {u w : List V}
    (hu : ∀ x ∈ u, Q x ≠ 0) (hw : ∀ x ∈ w, Q x ≠ 0)
    (h : List.Forall₂ (fun a b => ∃ s : F, s ≠ 0 ∧ Q a = s ^ 2 * Q b) u w) :
    symProd Q u hu * (symProd Q w hw)⁻¹ ∈ omega Q := by
  classical
  -- choose the scalars
  have key : ∀ (u w : List V), List.Forall₂ (fun a b => ∃ s : F, s ≠ 0 ∧ Q a = s ^ 2 * Q b) u w →
      ∃ t : List F, (∀ s ∈ t, s ≠ 0) ∧ t.length = w.length ∧
        (List.zipWith (· • ·) t w).map Q = u.map Q := by
    intro u w h
    induction h with
    | nil => exact ⟨[], by simp, rfl, rfl⟩
    | @cons a b u w hab _ ih =>
      obtain ⟨s, hs, hQs⟩ := hab
      obtain ⟨t, ht, hlen, hmap⟩ := ih
      refine ⟨s :: t, ?_, by simp [hlen], ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · exact ht x hx
      · simp only [List.zipWith_cons_cons, List.map_cons, hmap, Q_smul, hQs]
  obtain ⟨t, ht, hlen, hmap⟩ := key u w h
  have hw' : ∀ x ∈ List.zipWith (· • ·) t w, Q x ≠ 0 := by
    intro x hx
    have : Q x ∈ u.map Q := by rw [← hmap]; exact List.mem_map_of_mem hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp this
    rw [← hyx]; exact hu y hy
  have h1 := symProd_mul_inv_mem_omega Q hQ hu hw' (by rw [hmap])
  rwa [symProd_smul_eq Q w t hw ht hlen hw'] at h1

/-- $\tau_x\tau_y \in \Omega(V)$ when $Q(x)Q(y)$ is a square, i.e. $Q(x) = s^2Q(y)$ (O'Meara 1973, proof of 95:1,
step 3, p. 281: $\tau_{(\alpha_i)}\tau_{(\alpha_i)}\Omega_4 = \Omega_4$). -/
theorem symmetry_mul_symmetry_mem_omega (hQ : (QuadraticMap.associated Q).Nondegenerate) {x y : V} (hx : Q x ≠ 0)
    (hy : Q y ≠ 0) {s : F} (hs : s ≠ 0) (hxy : Q x = s ^ 2 * Q y) :
    symmetry Q x hx * symmetry Q y hy ∈ omega Q := by
  have hl : ∀ u ∈ [x, y], Q u ≠ 0 := by simp [hx, hy]
  have hl' : ∀ u ∈ [y, y], Q u ≠ 0 := by simp [hy]
  have h := symProd_mul_inv_mem_omega_of_sq Q hQ hl hl'
    (List.Forall₂.cons ⟨s, hs, hxy⟩ (List.Forall₂.cons ⟨1, one_ne_zero, by ring⟩ List.Forall₂.nil))
  have e1 : symProd Q [x, y] hl = symmetry Q x hx * symmetry Q y hy := by
    simp [symProd]
  have e2 : symProd Q [y, y] hl' = 1 := by
    simp only [symProd, List.pmap, List.prod_cons, List.prod_nil, mul_one]
    ext z
    exact symmetry_symmetry Q hy z
  rwa [e1, e2, inv_one, mul_one] at h

/-- **Lifting a factorization into a subspace** (O'Meara 1973, proof of 95:1, step 2, p. 281, and 55:6): let
$\sigma = \tau_{u_1}\cdots\tau_{u_r} \in O'(V)$ and let $U$ be a regular subspace with $\Omega(U) = O'(U)$ which
represents $Q(u_1), \dots, Q(u_r)$. Then $\sigma \in \Omega(V)$. -/
@[kb "omeara1963" "§95, proof of 95:1, step 2, p. 281 (the symmetries are with respect to lines in U, O'(U) = Ω(U))"]
theorem mem_omega_of_lift (hQ : (QuadraticMap.associated Q).Nondegenerate) {U : Submodule F V}
    (hU : (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate)
    (hΩ : omega (Q.comp U.subtype) = orthPrime (Q.comp U.subtype)) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPrime Q)
    (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) (h : σ = symProd Q l hl)
    (hrep : ∀ u ∈ l, ∃ w : U, Q (w : V) = Q u) : σ ∈ omega Q := by
  have hcomp := Sp55.isCompl_perp Q hU
  have horth := Sp55.horth_perp Q (U := U)
  have lift : ∀ l : List V, (∀ u ∈ l, ∃ w : U, Q (w : V) = Q u) →
      ∃ l' : List U, l'.map (fun u : U => Q (u : V)) = l.map Q := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons x l ih =>
      intro hr
      obtain ⟨w, hw⟩ := hr x List.mem_cons_self
      obtain ⟨l', h'⟩ := ih fun u hu => hr u (List.mem_cons_of_mem x hu)
      exact ⟨w :: l', by simp [hw, h']⟩
  obtain ⟨l', hl'map⟩ := lift l hrep
  have hl'ne : ∀ u ∈ l', (Q.comp U.subtype) u ≠ 0 := by
    intro u hu
    have : Q (u : V) ∈ l.map Q := by rw [← hl'map]; exact List.mem_map_of_mem hu
    obtain ⟨v, hv, hvu⟩ := List.mem_map.mp this
    show Q (u : V) ≠ 0
    rw [← hvu]; exact hl v hv
  have hperm : (l.map Q).Perm ((l'.map fun u : U => (u : V)).map Q) := by
    rw [List.map_map]
    exact (show l.map Q = l'.map (Q ∘ fun u : U => (u : V)) from hl'map.symm) ▸ List.Perm.refl _
  have h1 := symProd_mul_inv_mem_omega Q hQ hl (Sp55.ne_zero_map_coe Q U l' hl'ne) hperm
  have hτ' : symProd (Q.comp U.subtype) l' hl'ne ∈ omega (Q.comp U.subtype) := by
    rw [hΩ]
    have hev := Sp55.even_length_of_mem_orthPlus Q hσ.1 l hl h
    have hlen : l'.length = l.length := by simpa using congrArg List.length hl'map
    have hs : HasSpinorNorm Q σ (l.map Q).prod :=
      (Sp55.hasSpinorNorm_iff Q).mpr ⟨l, hl, h, 1, one_ne_zero, by simp⟩
    obtain ⟨s, hs0, hps⟩ := HasSpinorNorm.eq_mul_sq Q hQ hs hσ.2
    refine ⟨⟨Sp55.symProd_mem_orth _ _ _, (MonoidHom.mem_ker).mpr ?_⟩, ?_⟩
    · rw [Sp55.det_symProd _ _ hl'ne, hlen]; exact hev.neg_one_pow
    · refine (Sp55.hasSpinorNorm_iff _).mpr ⟨l', hl'ne, rfl, s, hs0, ?_⟩
      have e : l'.map (Q.comp U.subtype) = l.map Q := hl'map
      rw [e, hps]
  have h2 : symProd Q (l'.map fun u : U => (u : V)) (Sp55.ne_zero_map_coe Q U l' hl'ne) ∈ omega Q := by
    have := Sp55.map_omega_le Q hcomp horth (Subgroup.mem_map_of_mem (Sp55.extId hcomp) hτ')
    rwa [Sp55.extId_symProd Q hcomp horth] at this
  rw [← h] at h1
  have := (omega Q).mul_mem h1 h2
  simpa using this

end S95

end QuadFormsKB.OMeara
