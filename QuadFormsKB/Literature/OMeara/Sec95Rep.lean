/-
# O'Meara 95:2: elements of $\Omega_n$ and ternary subspaces

**Setting** (as in `Sec95.lean`): $F$ a number field, $\mathfrak p$ (`v`) a finite place, $K = F_\mathfrak p$
(`v.adicCompletion F`), $(V, Q)$ a regular quadratic space over $K$ of dimension $n$; $\tau_{(\alpha)}$ is a symmetry
$\tau_u$ with $Q(u) = \alpha$, and a product $\tau_{u_1}\cdots\tau_{u_r}$ is `symProd Q [u₁, …, u_r]`.

**Proves** **Proposition 95:2** (O'Meara 1973 printing, p. 283): if $n \ge 3$ and
$\sigma = \tau_{(\alpha_1)}\cdots\tau_{(\alpha_r)} \in \Omega_n$ with $r \le n$, then some regular ternary subspace
of $V$ represents $\alpha_1, \dots, \alpha_r$ (`exists_ternary_of_mem_omega`). (The machine-read text lost the bound
on $r$; the page image reads "with $r \le n$".)

The proof follows the book: if $V$ is isotropic, a regular ternary subspace containing a hyperbolic plane is
universal; otherwise $n \in \{3, 4\}$; for $n = 4$ over a dyadic field step 2 of the proof of 95:1 gives the
subspace, and over a non-dyadic field the $\alpha_i$ fall into at most two square classes (they cannot fill the four
classes, by 95:1a), so a ternary subspace through vectors of those two classes works.
-/
import QuadFormsKB.Literature.OMeara.Sec95

open QuadraticMap Module NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54

namespace S95

section Aux

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable (Q : QuadraticForm K W)

/-- An anisotropic form is regular (over any field). -/
lemma nondeg_of_aniso_gen (hQ : Q.Anisotropic) : (QuadraticMap.associated Q).Nondegenerate :=
  cd_nondeg_of_reg Q fun x hx => hQ x (by rw [← bil_self]; exact hx x)

/-- Pairings of a combination $ax + by + cz$ with a hyperbolic pair $x, y$ and a vector $z$ orthogonal to it. -/
lemma bil_comb3 {x y z : W} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hzx : bil Q z x = 0) (hzy : bil Q z y = 0) (a b c : K) :
    bil Q (a • x + b • y + c • z) x = b ∧ bil Q (a • x + b • y + c • z) y = a ∧
      bil Q (a • x + b • y + c • z) z = c * Q z := by
  have hxz : bil Q x z = 0 := by rw [bil_comm]; exact hzx
  have hyz : bil Q y z = 0 := by rw [bil_comm]; exact hzy
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [bil_add_left, bil_smul_left, bil_self, hx, hy, hxy, hyx, hxz, hyz, hzx, hzy] <;> ring

/-- A hyperbolic pair together with an orthogonal anisotropic vector spans a regular universal ternary space. -/
lemma exists_ternary_of_triple {x y z : W} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hzx : bil Q z x = 0) (hzy : bil Q z y = 0) (hz : Q z ≠ 0) :
    ∃ U : Submodule K W, finrank K U = 3 ∧ (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate ∧
      ∀ α : K, ∃ w : U, Q (w : W) = α := by
  have b0 : ∀ t : W, bil Q 0 t = 0 := fun t => by simp [bil]
  have hli : LinearIndependent K ![x, y, z] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
    obtain ⟨e1, e2, e3⟩ := bil_comb3 Q hx hy hxy hzx hzy (g 0) (g 1) (g 2)
    rw [hg, b0] at e1 e2 e3
    intro i
    fin_cases i
    · exact e2.symm
    · exact e1.symm
    · exact (mul_eq_zero.mp e3.symm).resolve_right hz
  have mx : x ∈ Submodule.span K (Set.range ![x, y, z]) := Submodule.subset_span ⟨0, by simp⟩
  have my : y ∈ Submodule.span K (Set.range ![x, y, z]) := Submodule.subset_span ⟨1, by simp⟩
  have mz : z ∈ Submodule.span K (Set.range ![x, y, z]) := Submodule.subset_span ⟨2, by simp⟩
  refine ⟨Submodule.span K (Set.range ![x, y, z]), by simp [finrank_span_eq_card hli], ?_, fun α => ?_⟩
  · apply cd_nondeg_of_reg
    intro u hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp u.2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc
    have hux : bil Q (u : W) x = 0 := by
      have := hu ⟨x, mx⟩; rwa [Sp55.bil_comp_subtype] at this
    have huy : bil Q (u : W) y = 0 := by
      have := hu ⟨y, my⟩; rwa [Sp55.bil_comp_subtype] at this
    have huz : bil Q (u : W) z = 0 := by
      have := hu ⟨z, mz⟩; rwa [Sp55.bil_comp_subtype] at this
    rw [← hc] at hux huy huz
    obtain ⟨e1, e2, e3⟩ := bil_comb3 Q hx hy hxy hzx hzy (c 0) (c 1) (c 2)
    rw [e1] at hux
    rw [e2] at huy
    rw [e3] at huz
    have hc2 : c 2 = 0 := (mul_eq_zero.mp huz).resolve_right hz
    apply Subtype.ext
    rw [← hc, hux, huy, hc2]
    simp
  · refine ⟨⟨(α / 2) • x + y, Submodule.add_mem _ (Submodule.smul_mem _ _ mx) my⟩, ?_⟩
    show Q ((α / 2) • x + y) = α
    rw [Q_add, Q_smul, bil_smul_left, hxy, hx, hy]
    have h2 : (2 : K) ≠ 0 := cd_two_ne
    field_simp
    ring

/-- An isotropic regular space of dimension at least $3$ has a regular universal ternary subspace. -/
lemma exists_ternary_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 3 ≤ finrank K W)
    {x : W} (hx0 : x ≠ 0) (hx : Q x = 0) :
    ∃ U : Submodule K W, finrank K U = 3 ∧ (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate ∧
      ∀ α : K, ∃ w : U, Q (w : W) = α := by
  classical
  obtain ⟨y, hy, hxy⟩ := exists_hyperbolic_pair Q hQ hx0 hx
  set H := Submodule.span K {x, y} with hH
  have hreg := Sp55.nondegenerate_span_pair Q hx hy hxy
  have hc := Sp55.isCompl_perp Q hreg
  set P := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm K W) H with hP
  have hPmem : ∀ z ∈ P, bil Q z x = 0 ∧ bil Q z y = 0 := fun z hz => by
    refine ⟨?_, ?_⟩ <;> rw [bil_comm] <;>
      exact Sp55.horth_perp Q _ (Submodule.subset_span (by simp)) z hz
  have hz : ∃ z : W, bil Q z x = 0 ∧ bil Q z y = 0 ∧ Q z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hPQ : ∀ z ∈ P, Q z = 0 := fun z hz => hcon z (hPmem z hz).1 (hPmem z hz).2
    have hPbot : P = ⊥ := by
      by_contra hne
      obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      apply hw0
      apply hQ.1 w
      intro t
      have ht : t ∈ H ⊔ P := hc.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨h, hh, p, hp, rfl⟩ := Submodule.mem_sup.mp ht
      show bil Q w (h + p) = 0
      rw [bil_add_right, bil_comm Q w h, Sp55.horth_perp Q h hh w hwP, zero_add]
      have h1 := Q_add Q w p
      rw [hPQ _ (P.add_mem hwP hp), hPQ w hwP, hPQ p hp] at h1
      have h2 : (2 : K) ≠ 0 := cd_two_ne
      have : 2 * bil Q w p = 0 := by rw [zero_add, add_zero] at h1; exact h1.symm
      exact (mul_eq_zero.mp this).resolve_left h2
    have hHtop : H = ⊤ := by
      have := hc.sup_eq_top
      rwa [hPbot, sup_bot_eq] at this
    have hle2 : finrank K H ≤ 2 := by
      have hle := finrank_span_finset_le_card (R := K) ({x, y} : Finset W)
      rw [Finset.coe_pair] at hle
      exact hle.trans Finset.card_le_two
    have htop := finrank_top K W
    rw [← hHtop] at htop
    omega
  obtain ⟨z, hzx, hzy, hzQ⟩ := hz
  exact exists_ternary_of_triple Q hx hy hxy hzx hzy hzQ

/-- A four-dimensional space has a non-zero vector orthogonal to any two given vectors. -/
lemma exists_ne_zero_orth_two (hn : finrank K W = 4) (p q : W) :
    ∃ z : W, z ≠ 0 ∧ bil Q z p = 0 ∧ bil Q z q = 0 := by
  let φ : W →ₗ[K] K × K := LinearMap.prod (QuadraticMap.associated Q p) (QuadraticMap.associated Q q)
  have h := LinearMap.finrank_range_add_finrank_ker φ
  have hr : finrank K (LinearMap.range φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  by_contra hcon
  push Not at hcon
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    by_contra hz0
    have h1 : bil Q p z = 0 := congrArg Prod.fst hz
    have h2 : bil Q q z = 0 := congrArg Prod.snd hz
    exact hcon z hz0 (by rw [bil_comm]; exact h1) (by rw [bil_comm]; exact h2)
  rw [hker, finrank_bot, hn] at h
  omega

/-- The orthogonal complement of an anisotropic vector in a quaternary space has dimension $3$. -/
lemma ker_ternary_finrank (hn : finrank K W = 4) {z : W} (hz : Q z ≠ 0) :
    finrank K (LinearMap.ker (QuadraticMap.associated Q z)) = 3 := by
  have hbx : QuadraticMap.associated Q z z = Q z := bil_self Q z
  have hrange : LinearMap.range (QuadraticMap.associated Q z) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / Q z) • z, ?_⟩
    rw [map_smul, hbx, smul_eq_mul]
    field_simp
  have := LinearMap.finrank_range_add_finrank_ker (QuadraticMap.associated Q z)
  rw [hrange, finrank_top, finrank_self, hn] at this
  omega

/-- Counting: at most two indices carry a nonzero even count when the total is at most $4$. -/
lemma exists_two_cover (n : Fin 4 → ℕ) (hev : ∀ i, n i % 2 = 0) (hsum : ∑ k, n k ≤ 4) :
    ∃ i j : Fin 4, ∀ k, n k ≠ 0 → k = i ∨ k = j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, -, -⟩ := hcon 0 0
  obtain ⟨b, hb, hba, -⟩ := hcon a a
  obtain ⟨c, hc, hca, hcb⟩ := hcon a b
  have hsub : ({a, b, c} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset (f := n) hsub
  rw [Finset.sum_insert (by simp [Ne.symm hba, Ne.symm hca]), Finset.sum_insert (by simp [Ne.symm hcb]),
    Finset.sum_singleton] at h
  have := hev a
  have := hev b
  have := hev c
  omega

end Aux

end S95

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Invertible (2 : v.adicCompletion F)]
variable (Q : QuadraticForm (v.adicCompletion F) V)

/-- **Proposition 95:2** (O'Meara 1973, p. 283): let $V$ be a regular $n$-ary quadratic space over a local field
with $n \ge 3$, and let $\sigma = \tau_{u_1}\cdots\tau_{u_r} \in \Omega_n$ with $r \le n$. Then there is a regular
ternary subspace $U$ of $V$ which represents $Q(u_1), \dots, Q(u_r)$. -/
@[kb "omeara1963" "§95, 95:2, p. 283"]
theorem exists_ternary_of_mem_omega (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 3 ≤ finrank (v.adicCompletion F) V) (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0)
    (hσ : symProd Q l hl ∈ omega Q) (hr : l.length ≤ finrank (v.adicCompletion F) V) :
    ∃ U : Submodule (v.adicCompletion F) V, finrank (v.adicCompletion F) U = 3 ∧
      (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate ∧ ∀ u ∈ l, ∃ w : U, Q (w : V) = Q u := by
  classical
  by_cases hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0
  · obtain ⟨x, hx0, hx⟩ := hiso
    obtain ⟨U, hU3, hUn, hUr⟩ := S95.exists_ternary_of_isotropic Q hQ hn hx0 hx
    exact ⟨U, hU3, hUn, fun u _ => hUr (Q u)⟩
  have hQa : Q.Anisotropic := fun x hx => by_contra fun h => hiso ⟨x, h, hx⟩
  have h5 : ¬ 5 ≤ finrank (v.adicCompletion F) V := fun h => hiso (S95.exists_isotropic_of_five_le v Q hQ h)
  have hcases : finrank (v.adicCompletion F) V = 3 ∨ finrank (v.adicCompletion F) V = 4 := by omega
  rcases hcases with h3 | h4
  · refine ⟨⊤, ?_, ?_, fun u _ => ⟨⟨u, Submodule.mem_top⟩, rfl⟩⟩
    · rw [finrank_top]; exact h3
    · exact S95.nondeg_of_aniso_gen _ (fun u hu => Subtype.ext (hQa _ hu))
  rcases (S95.valued_two_le_one v).lt_or_eq with h2 | h2
  · obtain ⟨U, hU3, hUn, hUr⟩ := S95.exists_ternary_rep v Q h2 hQa h4 (l.map Q)
      (fun α hα => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hα; exact hl u hu)
      (by rw [List.length_map]; omega)
    exact ⟨U, hU3, hUn, fun u hu => hUr (Q u) (List.mem_map.mpr ⟨u, hu, rfl⟩)⟩
  have h2R := S95.isUnit_two_of_valued v h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  obtain ⟨Δ, hΔ, hΔs, -⟩ := exists_nonsquare_unit (R := v.adicCompletionIntegers F) h2R
  obtain ⟨y, hy⟩ := S95.exists_vectors_cls (F := v.adicCompletion F) h2R hπ hQa h4 hΔ
  have hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0 := by
    have := fun i => (hy i).symm ▸ S95.cls_ne_zero (F := v.adicCompletion F) hπ hΔ i
    simp [this]
  have hσO : symProd Q l hl ∈ orthPrime Q := omega_le_orthPrime Q hQ hσ
  obtain ⟨n, hpar, hlen, hcl, h0, h1⟩ := S95.class_count_parity Q hQ
    (Δ := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) Δ)
    (π := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) π)
    (fun x hx => S95.exists_cls h2R hπ hΔ hΔs hx) (fun m k => S95.isSquare_pow_iff hπ hΔ hΔs m k)
    y hy hy0 hσO l hl rfl
  have hev3 : n 3 % 2 = 0 := by
    by_contra hne
    have h1' := h1 (by omega)
    have hρ : symProd Q [y 0, y 1, y 2, y 3] hy0 ∈ omega Q := by
      have := (omega Q).mul_mem ((omega Q).inv_mem h1') hσ
      simpa [mul_assoc] using this
    exact S95.symProd_not_mem_omega h2R hπ hQa h4 hΔ hΔs y hy hy0 hρ
  have hev : ∀ i, n i % 2 = 0 := fun i => by have := hpar i; omega
  have hsum : ∑ k, n k ≤ 4 := by rw [← hlen]; omega
  obtain ⟨i, j, hij⟩ := S95.exists_two_cover n hev hsum
  obtain ⟨z, hz0, hzp, hzq⟩ := S95.exists_ne_zero_orth_two Q h4 (y i) (y j)
  have hzQ : Q z ≠ 0 := fun h => hz0 (hQa z h)
  refine ⟨LinearMap.ker (QuadraticMap.associated Q z), S95.ker_ternary_finrank Q h4 hzQ,
    S95.nondeg_of_aniso_gen _ (fun u hu => Subtype.ext (hQa _ hu)), fun u hu => ?_⟩
  obtain ⟨k, hk, s, hs, hQu⟩ := hcl u hu
  have hyk : bil Q z (y k) = 0 := by
    rcases hij k hk with h | h
    · rw [h]; exact hzp
    · rw [h]; exact hzq
  have hyk' : QuadraticMap.associated Q z (y k) = 0 := hyk
  refine ⟨⟨s • y k, LinearMap.mem_ker.mpr (by rw [map_smul, hyk', smul_zero])⟩, ?_⟩
  show Q (s • y k) = Q u
  rw [Q_smul, hy k, hQu]
  try rfl

end QuadFormsKB.OMeara
