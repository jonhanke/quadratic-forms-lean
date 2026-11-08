/-
# O'Meara §101C: Proposition 101:12 (for $\Omega_n$) from Lemma 101:11

**Layer:** $F$ a number field, $V = F^n$ with a nondegenerate `Q : QuadForm F n`; the matrix groups $O(V)$ =
`orthGroup Q F`, $O^+(V)$ = `Tamagawa.soSub Q F`, $O'(V)$ = `spinorKernel Q F`, $\Omega_n(V)$ = the commutator subgroup
`commutator (orthGroup Q F)`, the same over the completions $F_\mathfrak p$ (`v.adicCompletion F`, finite spots) and
$F_w$ (`w.Completion`, infinite spots), localization `orthMap`; O'Meara's abstract groups `OMeara.omega`,
`OMeara.orthPrime` on $K^n$ with the form `qk Q K`, through `QIn.glEquiv`.

**Proves**
* `omeara101_12_of_101_11` (**Proposition 101:12 from Lemma 101:11**, p. 294): the named statement `OMeara101_12`
  follows from the named statement `OMeara101_11`, by O'Meara's proof. Let $\sigma \in O^+(V)$ with
  $\sigma_\mathfrak p \in \Omega_n(V_\mathfrak p)$ at every spot. Then $\sigma \in O'_n(V)$ (Global Square Theorem,
  `mem_spinorKernel_iff_forall`); for $n \le 3$ this is the end (`omeara101_12_of_le_three`). For $n \ge 4$ write
  $\sigma = \tau_{y_1}\cdots\tau_{y_r}$ with $r \le n$ (43:3). At a finite spot, 95:2
  (`OMeara.exists_ternary_of_mem_omega`) gives a regular ternary subspace of $V_\mathfrak p$ representing
  $Q(y_1), \dots, Q(y_r)$; at an infinite spot $V_w$ is isotropic (then a regular ternary subspace through a hyperbolic
  plane is universal) or all products $Q(x)Q(y)$ of non-zero values are squares (then any regular ternary subspace
  represents every $Q(y_i)$). Lemma 101:11 gives a regular ternary $W \subseteq V$ representing all $Q(y_i)$, and
  $O'(W) = \Omega(W)$ (55:5) lifts to $\sigma \in \Omega_n(V)$ (`OMeara.S95.mem_omega_of_lift`, as in step 2 of the
  proof of 95:1). Conditional only on `OMeara101_11`.
* `omeara101_11_of_le_three` (**Lemma 101:11 for $n \le 3$**, p. 293): the conclusion of `OMeara101_11` for a single
  regular $V$ with $n \le 3$. Unconditional. For $n < 3$ the hypothesis is void (no ternary subspace at an infinite
  spot); for $n = 3$ the local ternary subspaces are all of $V_\mathfrak p$, and the global statement is 66:3 for
  numbers (`represents_iff_everywhere_nf`).

*Deviation from the book:* at the infinite spots O'Meara only says the ternary subspace exists ("clearly"); here the
two cases are made explicit (`isotropicIn_or_isSquare_mul`). Over an anisotropic $V_w$ any ternary subspace is used
(not one through $y_1$): each non-zero $Q(y_i)$ is a square multiple of $Q(u)$ for any $u \ne 0$ in it.
-/
import QuadFormsKB.Literature.OMeara.Sec101Omega
import QuadFormsKB.Literature.OMeara.Sec95Rep

open NumberField IsDedekindDomain Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

section Bridge

variable (K : Type) [Field K] [Algebra F K] [CharZero K]

/-- O'Meara's bilinear form of `qk Q K` vanishes iff the library's Hessian pairing does (they differ by $2$). -/
theorem associated_qk_eq_zero_iff [Invertible (2 : K)] (x y : Fin n → K) :
    QuadraticMap.associated (qk Q K) x y = 0 ↔ x ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ y) = 0 := by
  change OMeara.bil (qk Q K) x y = 0 ↔ qbil Q K x y = 0
  rw [← OMeara.QIn.two_mul_bil Q K x y]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- **Regularity of a subspace, two ways:** O'Meara's regularity of $U \subseteq K^n$
(`(QuadraticMap.associated ((qk Q K).comp U.subtype)).Nondegenerate`) is the nondegeneracy condition of
`RegTernaryRepresents` (via the Hessian pairing $x \cdot H y$). -/
theorem nondegenerate_comp_subtype_iff [Invertible (2 : K)] (U : Submodule K (Fin n → K)) :
    (QuadraticMap.associated ((qk Q K).comp U.subtype)).Nondegenerate ↔
      ∀ x ∈ U, (∀ y ∈ U, x ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ y) = 0) → x = 0 := by
  have key : ∀ a b : U, QuadraticMap.associated ((qk Q K).comp U.subtype) a b = 0 ↔
      (a : Fin n → K) ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ (b : Fin n → K)) = 0 := by
    intro a b
    have h1 := OMeara.Sp55.bil_comp_subtype (qk Q K) U a b
    rw [← associated_qk_eq_zero_iff Q K]
    change OMeara.bil _ a b = 0 ↔ OMeara.bil _ _ _ = 0
    rw [h1]
  constructor
  · intro h x hx hxy
    have := h.1 ⟨x, hx⟩ fun b => (key _ b).mpr (hxy b b.2)
    exact congrArg Subtype.val this
  · intro h
    refine OMeara.cd_nondeg_of_reg _ fun a ha => ?_
    exact Subtype.ext (h a a.2 fun y hy => (key a ⟨y, hy⟩).mp (ha ⟨y, hy⟩))

/-- An O'Meara regular ternary subspace $U \subseteq K^n$ representing the elements of $X$ witnesses
`RegTernaryRepresents Q K X`. -/
theorem regTernaryRepresents_of [Invertible (2 : K)] (X : Finset F) (U : Submodule K (Fin n → K))
    (h3 : finrank K U = 3) (hU : (QuadraticMap.associated ((qk Q K).comp U.subtype)).Nondegenerate)
    (hrep : ∀ a ∈ X, ∃ w : U, qk Q K (w : Fin n → K) = algebraMap F K a) : RegTernaryRepresents Q K X :=
  ⟨U, h3, (nondegenerate_comp_subtype_iff Q K U).mp hU, fun a ha => by
    obtain ⟨w, hw⟩ := hrep a ha
    exact ⟨w, w.2, by rw [← qk_apply]; exact hw⟩⟩

/-- The image of a product of rational symmetries over any $K \supseteq F$ of characteristic $0$. -/
theorem orthMap_symmProd' (xs : List (Fin n → F)) :
    orthMap Q K (symmProd Q F xs) = symmProd Q K (xs.map fun x i => algebraMap F K (x i)) := by
  rw [symmProd, symmProd, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => orthMap_symm' Q K x

theorem evalIn_algebraMap (x : Fin n → F) :
    Q.evalIn K (fun i => algebraMap F K (x i)) = algebraMap F K (Q.evalIn F x) := by
  simpa using evalIn_map_tower Q K (K := F) x

end Bridge

/-! ### The local ternary subspaces -/

open Classical in
/-- **The finite spots** (O'Meara 1973, proof of 101:12, p. 294, by 95:2): if $\tau_{y_1}\cdots\tau_{y_r} \in
\Omega_n(V_\mathfrak p)$ with $r \le n$ and $n \ge 3$, then a regular ternary subspace of $V_\mathfrak p$ represents
$Q(y_1), \dots, Q(y_r)$. -/
theorem regTernary_finite (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    (l : List (Fin n → F)) (hl : ∀ x ∈ l, Q.evalIn F x ≠ 0) (hlen : l.length ≤ n)
    (hσ : symmProd Q (v.adicCompletion F) (l.map fun x i => algebraMap F (v.adicCompletion F) (x i)) ∈
      commutator (orthGroup Q (v.adicCompletion F))) :
    RegTernaryRepresents Q (v.adicCompletion F) (l.map (Q.evalIn F)).toFinset := by
  set K := v.adicCompletion F
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  set lK := l.map fun x i => algebraMap F K (x i) with hlK
  have hlK0 : ∀ y ∈ lK, Q.evalIn K y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [evalIn_algebraMap]
    exact (map_ne_zero _).mpr (hl x hx)
  rw [OMeara.QIn.mem_commutator_iff, OMeara.QIn.glEquiv_symmProd Q K lK hlK0] at hσ
  obtain ⟨U, hU3, hUn, hUr⟩ := OMeara.exists_ternary_of_mem_omega v (qk Q K) (nondegenerate_qk_of Q K hQ)
    (by rw [finrank_fin_fun]; exact hn) lK _ hσ (by rw [finrank_fin_fun, hlK, List.length_map]; exact hlen)
  refine regTernaryRepresents_of Q K _ U hU3 hUn fun a ha => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨w, hw⟩ := hUr _ (List.mem_map_of_mem (f := fun x i => algebraMap F K (x i)) hx)
  exact ⟨w, by rw [hw, qk_apply, evalIn_algebraMap]⟩

/-- **The infinite spots** (O'Meara 1973, proof of 101:12, p. 294): for $n \ge 3$, some regular ternary subspace of
$V_w$ represents every element of $X$, provided each is a value of $Q$ over $F_w$. If $V_w$ is isotropic, a regular
ternary subspace through a hyperbolic plane is universal; otherwise all products $Q(x)Q(y)$ of non-zero values are
squares (`isotropicIn_or_isSquare_mul`), and any ternary subspace (regular, as $V_w$ is anisotropic) works. -/
theorem regTernary_infinite (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (w : InfinitePlace F) (X : Finset F)
    (hX : ∀ a ∈ X, ∃ y : Fin n → w.Completion, Q.evalIn _ y = algebraMap F _ a) :
    RegTernaryRepresents Q w.Completion X := by
  set K := w.Completion
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hnd := nondegenerate_qk_of Q K hQ
  by_cases hiso : Q.IsotropicIn K
  · obtain ⟨x, hx0, hx⟩ := hiso
    obtain ⟨U, hU3, hUn, hUr⟩ := OMeara.S95.exists_ternary_of_isotropic (qk Q K) hnd
      (by rw [finrank_fin_fun]; exact hn) hx0 (by rw [qk_apply]; exact hx)
    exact regTernaryRepresents_of Q K X U hU3 hUn fun a _ => hUr _
  · have hsq := (isotropicIn_or_isSquare_mul Q w).resolve_left hiso
    have han : ∀ x : Fin n → K, Q.evalIn K x = 0 → x = 0 := fun x hx => by
      by_contra h0
      exact hiso ⟨x, h0, hx⟩
    let e : Fin 3 → (Fin n → K) := fun i => Pi.basisFun K (Fin n) (Fin.castLE hn i)
    have hli : LinearIndependent K e :=
      (Pi.basisFun K (Fin n)).linearIndependent.comp (Fin.castLE hn) (Fin.castLE_injective hn)
    let U := Submodule.span K (Set.range e)
    have hU3 : finrank K U = 3 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hUn : (QuadraticMap.associated ((qk Q K).comp U.subtype)).Nondegenerate :=
      OMeara.S95.nondeg_of_aniso_gen _ fun u hu => by
        have h := han (u : Fin n → K) (by rw [← qk_apply]; exact hu)
        exact Subtype.ext h
    have he0 : e 0 ∈ U := Submodule.subset_span ⟨0, rfl⟩
    have he0Q : Q.evalIn K (e 0) ≠ 0 := fun h => by
      have h' := congrFun (han _ h) (Fin.castLE hn 0)
      simp [e] at h'
    refine regTernaryRepresents_of Q K X U hU3 hUn fun a ha => ?_
    obtain ⟨y, hy⟩ := hX a ha
    by_cases hy0 : Q.evalIn K y = 0
    · exact ⟨0, by rw [Submodule.coe_zero, map_zero, ← hy, hy0]⟩
    obtain ⟨s, hs⟩ := hsq y (e 0) hy0 he0Q
    set q : K := Q.evalIn K (e 0) with hq
    set Y : K := Q.evalIn K y with hY
    have hs' : Y * q = s * s := hs
    refine ⟨⟨(s / q) • e 0, U.smul_mem _ he0⟩, ?_⟩
    change qk Q K ((s / q) • e 0) = _
    rw [QuadraticMap.map_smul, qk_apply, ← hq, smul_eq_mul, ← hy]
    calc s / q * (s / q) * q = s * s / q := by field_simp
      _ = Y := by rw [← hs', mul_div_assoc, div_self he0Q, mul_one]

/-! ### Proposition 101:12 from Lemma 101:11 -/

/-- **Proposition 101:12 from Lemma 101:11** (O'Meara 1973, §101C, p. 294): the named statement `OMeara101_12`
($\sigma \in \Omega_n(V)$ iff $\sigma_\mathfrak p \in \Omega_n(V_\mathfrak p)$ at every spot, for $\sigma \in O^+(V)$)
follows from the named statement `OMeara101_11`, by O'Meara's proof: $\sigma \in O'_n(V)$ by the Global Square
Theorem; for $n \ge 4$, $\sigma = \tau_{y_1}\cdots\tau_{y_r}$ with $r \le n$ (43:3), local regular ternary subspaces
representing the $Q(y_i)$ come from 95:2 (finite spots) and the archimedean theory (infinite spots), 101:11 gives a
global one $W$, and $O'(W) = \Omega(W)$ (55:5) gives $\sigma \in \Omega_n(V)$. -/
@[kb "omeara1963" "§101C, 101:12, p. 294 (from 101:11)"]
theorem omeara101_12_of_101_11 (h11 : OMeara101_11 F) : OMeara101_12 F := by
  classical
  refine ⟨fun n Q hQ σ hσ => ?_⟩
  rcases le_or_gt n 3 with hn | hn
  · exact omeara101_12_of_le_three Q hQ hn hσ
  refine ⟨fun h => ⟨fun v => orthMap_mem_commutator Q _ h, fun w => orthMap_mem_commutator Q _ h⟩, ?_⟩
  rintro ⟨hv, -⟩
  have hk : σ ∈ spinorKernel Q F :=
    (mem_spinorKernel_iff_forall Q hQ hσ).mpr fun v => commutator_le_spinorKernel Q _ hQ (hv v)
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hnd := nondegenerate_qk_of Q F hQ
  have hτ := OMeara.QIn.mem_orthPrime_of_mem_spinorKernel Q F hk
  obtain ⟨l, hl, hσl, hlen⟩ := OMeara.exists_symmetry_prod_eq_length_le (qk Q F) hnd hτ.1.1
  rw [OMeara.Cl54.attach_prod_eq_symProd] at hσl
  rw [finrank_fin_fun] at hlen
  have hl' : ∀ x ∈ l, Q.evalIn F x ≠ 0 := fun x hx => by rw [← qk_apply]; exact hl x hx
  have hσeq : σ = symmProd Q F l := by
    apply Subtype.ext
    apply (OMeara.QIn.glEquiv F).injective
    rw [hσl, OMeara.QIn.glEquiv_symmProd Q F l hl']
  have hX : RegTernaryRepresents Q F (l.map (Q.evalIn F)).toFinset := by
    refine h11.holds n Q hQ _ (fun v => ?_) (fun w => ?_)
    · refine regTernary_finite Q hQ hn.le v l hl' hlen ?_
      rw [← orthMap_symmProd', ← hσeq]
      exact hv v
    · refine regTernary_infinite Q hQ hn.le w _ fun a ha => ?_
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨fun i => algebraMap F _ (x i), evalIn_algebraMap Q _ x⟩
  obtain ⟨W, hW3, hWn, hWr⟩ := hX
  have hWn' := (nondegenerate_comp_subtype_iff Q F W).mpr hWn
  rw [OMeara.QIn.mem_commutator_iff]
  refine OMeara.S95.mem_omega_of_lift (qk Q F) hnd hWn'
    (OMeara.omega_eq_orthPrime_of_finrank_le_three _ hWn' hW3.le) hτ l hl hσl fun u hu => ?_
  obtain ⟨x, hxW, hx⟩ := hWr _ (List.mem_toFinset.mpr (List.mem_map_of_mem hu))
  exact ⟨⟨x, hxW⟩, by rw [qk_apply, qk_apply, hx, Algebra.algebraMap_self, RingHom.id_apply]⟩

/-! ### Lemma 101:11 for $n \le 3$ -/

/-- **Lemma 101:11 for $n \le 3$** (O'Meara 1973, §101C, p. 293): the conclusion of the named statement
`OMeara101_11` for a regular $V = F^n$ with $n \le 3$. If at every spot some regular ternary subspace of the
localization represents all of $X$, so does one of $V$. For $n < 3$ there is no ternary subspace at an infinite spot;
for $n = 3$ the subspace is $V$ itself, and each non-zero $a \in X$ is represented by $V$ since it is represented
everywhere locally (66:3, `represents_iff_everywhere_nf`). Unconditional. -/
@[kb "omeara1963" "§101C, 101:11, p. 293 (the case n ≤ 3)"]
theorem omeara101_11_of_le_three (hQ : Q.Nondegenerate) (hn : n ≤ 3) (X : Finset F)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), RegTernaryRepresents Q (v.adicCompletion F) X)
    (hw : ∀ w : InfinitePlace F, RegTernaryRepresents Q w.Completion X) :
    RegTernaryRepresents Q F X := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h3 : n = 3 := by
    obtain ⟨W, hW3, -⟩ := hw w
    have := Submodule.finrank_le W
    rw [finrank_fin_fun] at this
    omega
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hnd := nondegenerate_qk_of Q F hQ
  refine ⟨⊤, by rw [finrank_top, finrank_fin_fun, h3], fun x _ hx => ?_, fun a ha => ?_⟩
  · exact hnd.1 x fun y => (associated_qk_eq_zero_iff Q F x y).mpr (hx y Submodule.mem_top)
  by_cases ha0 : a = 0
  · refine ⟨0, Submodule.mem_top, ?_⟩
    rw [ha0, map_zero, ← qk_apply, map_zero]
  obtain ⟨x, hx⟩ := (represents_iff_everywhere_nf Q hQ a ha0).mpr fun (p : NFPlace F) => by
    cases p with
    | infinite w =>
      obtain ⟨_, -, -, hr⟩ := hw w
      obtain ⟨x, -, hx⟩ := hr a ha
      exact ⟨x, hx⟩
    | finite v =>
      obtain ⟨_, -, -, hr⟩ := hv v
      obtain ⟨x, -, hx⟩ := hr a ha
      exact ⟨x, hx⟩
  exact ⟨x, Submodule.mem_top, hx⟩

end QuadFormsKB.Lattices
