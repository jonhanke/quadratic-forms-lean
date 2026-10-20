/-
# Kneser's theorem for integral forms: the neighbour graph of a genus over $\mathbb Z$

**Layer:** integral forms `QuadForm ℤ n` with Hanke's genus (`Siegel.SameGenus`) and the $p$-neighbour graph on
$\mathrm{GL}_n(\mathbb Z)$-classes (`Siegel.Kneser.NbrStep`, `NbrReach`, `Siegel/KneserClosure.lean`), and lattices in
$(\mathbb Q^n, Q)$ over $\mathcal O_{\mathbb Q} \cong \mathbb Z$ (`Lattices/KneserLocal.lean`), linked by the transport
(`Tamagawa/RatBridge.lean`: Gram forms `gramZ`, `down`, `exists_latOf_of_sameGenus`).

**Proves**
- `isNbrForm_of_isNbrL` (one step): if $\gamma'\mathcal O^n$ is a $p$-neighbour (`IsNbrL`) of $\gamma\mathcal O^n$ in $(\mathbb Q^n, Q)$, then the
  Gram form of $\gamma'$ is a $p$-neighbour form (`IsNbrForm`) of the Gram form of $\gamma$;
- `nbrReach_of_chain`: a chain of $p$-neighbours of lattices starting at $\mathbb Z^n$ gives a path in the neighbour graph of forms;
- **`exists_nbrReach_intEquiv`** (Kneser's theorem over $\mathbb Z$): for $Q$ positive definite, $n \ge 3$, $p$ an odd prime with
  $p \nmid \det H$, and the genus of $\mathbb Z^n$ a single spinor genus, every form $Q'$ in the genus of $Q$ is
  $\mathrm{GL}_n(\mathbb Z)$-equivalent to a form reachable from $Q$ in the $p$-neighbour graph;
- **`exists_intEquiv_of_closed_kneser`**: the closure completeness criterion of the certified neighbour enumeration
  under exactly these hypotheses (no `KneserConnected` hypothesis). The isotropy of $Q$ at $p$ needed by strong approximation is
  automatic: $\mathbb Z_p^n$ is unimodular of rank $\ge 3$ at the odd prime $p$ (`isotropicIn_formF_of_unimodular`).

*Scope.* `KneserConnected p Q` itself (reachability on the nose, not up to equivalence) would additionally need one neighbour
step when $Q' \cong Q$; the closure criterion only needs reachability up to equivalence, which is what is proved. The hypothesis
"gen $=$ spn" (`hgs`) is a condition on $Q$ (O'Meara 102:9; `Lattices/SpinorGlobal.lean`), not an input.
-/
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Siegel.KneserClosure
import QuadFormsKB.Lattices.KneserLocal

open NumberField Matrix IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel.Kneser.Bridge

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.RatBridge QuadFormsKB.Lattices.Nbr QuadFormsKB.HilbertModular

variable {n : ℕ}

/-! ### $\mathcal O_{\mathbb Q} \cong \mathbb Z$ -/

theorem cast_eZ (c : 𝓞 ℚ) : ((eZ c : ℤ) : ℚ) = algebraMap (𝓞 ℚ) ℚ c := by
  conv_rhs => rw [← eZ.symm_apply_apply c, eZ_symm_apply]
  simp

theorem prime_natCast {p : ℕ} (hp : p.Prime) : Prime (p : 𝓞 ℚ) := by
  have h : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have e : eZ.symm (p : ℤ) = (p : 𝓞 ℚ) := by rw [eZ_symm_apply]; simp
  rw [← e]
  exact (MulEquiv.prime_iff eZ.symm.toMulEquiv).mpr h

theorem not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : 𝓞 ℚ) ∣ 2 := by
  intro h
  have h' := map_dvd (eZ : 𝓞 ℚ →+* ℤ) h
  simp only [map_natCast, map_ofNat] at h'
  have : p ∣ 2 := by exact_mod_cast h'
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact hp2 h1

theorem natCard_res_natCast (p : ℕ) [Fact p.Prime] : Nat.card (Res (p : 𝓞 ℚ)) = p := by
  have hI : Ideal.span {((p : ℤ))} = (Ideal.span {(p : 𝓞 ℚ)}).map (eZ : 𝓞 ℚ →+* ℤ) := by
    rw [Ideal.map_span, Set.image_singleton]; simp
  have e1 : Res (p : 𝓞 ℚ) ≃+* ℤ ⧸ Ideal.span {((p : ℤ))} := Ideal.quotientEquiv _ _ eZ hI
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem evalIn_down (G : QuadForm (𝓞 ℚ) n) (x : Fin n → ℚ) : (down G).evalIn ℚ x = G.evalIn ℚ x := by
  simp only [QuadForm.evalIn, down, QuadForm.map, Matrix.map_apply, eq_intCast, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [cast_eZ]

/-- $\mathcal O_{\mathbb Q}^n$ and $\mathbb Z^n$ are the same subgroup of $\mathbb Q^n$. -/
theorem toAddSubgroup_stdLat :
    (Nbr.stdLat (𝓞 ℚ) ℚ n).toAddSubgroup = (Kneser.stdLat n).toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Nbr.mem_stdLat, Kneser.mem_stdLat]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨fun i => eZ (y i), by ext i; simp [Kneser.cv, cast_eZ]⟩
  · rintro ⟨y, rfl⟩; exact ⟨fun i => eZ.symm (y i), by ext i; simp [Kneser.cv, ← cast_eZ]⟩

/-- $\delta\mathcal O_{\mathbb Q}^n = \delta\mathbb Z^n$. -/
theorem toAddSubgroup_latOf (δ : GL (Fin n) ℚ) : (latOf δ).toAddSubgroup = (imgLat δ.val).toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, latOf, mem_glImage, mem_imgLat]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, rfl⟩ := mem_intVec_iff_exists.mp hz
    exact ⟨fun i => eZ (y i), by congr 1; ext i; simp [Kneser.cv, cast_eZ]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨intCoe fun i => eZ.symm (c i), intCoe_mem _, ?_⟩
    congr 1; ext i; simp [Kneser.cv, ← cast_eZ]

/-! ### One neighbour step -/

/-- **A neighbour step of lattices gives a neighbour form.** -/
theorem isNbrForm_of_isNbrL {Q : QuadForm ℤ n} {p : ℕ} [Fact p.Prime] {γ γ' : GL (Fin n) ℚ}
    (hγ : IsIntegral (formF (up Q)) (latOf γ)) (hγ' : IsIntegral (formF (up Q)) (latOf γ'))
    (h : IsNbrL (formF (up Q)) (p : 𝓞 ℚ) (latOf γ) (latOf γ')) :
    IsNbrForm p (down (gramZ (formF (up Q)) γ hγ)) (down (gramZ (formF (up Q)) γ' hγ')) := by
  set N := latOf (γ⁻¹ * γ')
  have hN : glImage γ N = latOf γ' := by
    show glImage γ (glImage (γ⁻¹ * γ') intVec) = glImage γ' intVec
    rw [glImage_mul, ← glImage_mul, mul_inv_cancel, glImage_one]
  rw [← hN] at h
  obtain ⟨hnb, -⟩ := (isNbrL_latOf_iff γ hγ N).mp h
  set G := gramZ (formF (up Q)) γ hγ
  set g := (γ⁻¹ * γ').val
  have hNg := toAddSubgroup_latOf (γ⁻¹ * γ')
  refine ⟨g, (Matrix.isUnits_det_units (γ⁻¹ * γ')).ne_zero, ⟨?_, ?_, ?_⟩, fun x => ?_⟩
  · have := hnb.relIndex_std
    rwa [natCard_res_natCast, toAddSubgroup_stdLat, hNg] at this
  · have := hnb.relIndex_self
    rwa [natCard_res_natCast, toAddSubgroup_stdLat, hNg] at this
  · intro x hx
    have hxN : x ∈ N := by
      have : x ∈ (imgLat g).toAddSubgroup := hx
      rw [← hNg] at this; exact this
    obtain ⟨z, hz⟩ := hnb.integral x hxN
    refine ⟨eZ z, ?_⟩
    rw [evalIn_down, cast_eZ]; exact hz
  · rw [evalIn_down, evalIn_down,
      show (gramZ (formF (up Q)) γ' hγ').evalIn ℚ x = _ from qv_gramZ γ' hγ' x,
      show G.evalIn ℚ (g *ᵥ x) = _ from qv_gramZ γ hγ (g *ᵥ x),
      mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]

/-- A $\pi$-neighbour of a lattice is a lattice. -/
theorem isLattice_of_isNbrL {Q : QuadForm ℚ n} {π : 𝓞 ℚ} (hπ : π ≠ 0) {M M' : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hM : M.IsLattice ℚ) (h : IsNbrL Q π M M') : M'.IsLattice ℚ := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hM
  refine isLattice_of_global_bounds (d := π * d) (mul_ne_zero hπ hd) (fun z hz => ?_) (fun z hz => ?_)
  · rw [mul_smul, ← algebraMap_smul ℚ]
    exact h.smul_right _ (h1 z hz)
  · rw [mul_comm, mul_smul, ← algebraMap_smul ℚ π]
    exact h2 _ (h.smul_left _ hz)

/-- **A chain of neighbour lattices from $\gamma_0\mathcal O^n$ gives a path in the neighbour graph of forms.** -/
theorem nbrReach_of_chain {Q : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime] {γ₀ : GL (Fin n) ℚ}
    (hγ₀ : IsIntegral (formF (up Q)) (latOf γ₀)) {N : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hc : Relation.ReflTransGen (IsNbrL (formF (up Q)) (p : 𝓞 ℚ)) (latOf γ₀) N) :
    ∃ (γ : GL (Fin n) ℚ) (h : IsIntegral (formF (up Q)) (latOf γ)), N = latOf γ ∧
      NbrReach p (down (gramZ (formF (up Q)) γ₀ hγ₀)) (down (gramZ (formF (up Q)) γ h)) := by
  induction hc with
  | refl => exact ⟨γ₀, hγ₀, rfl, Relation.ReflTransGen.refl⟩
  | @tail N₁ N₂ _ hstep ih =>
    obtain ⟨γ₁, h₁, rfl, hr⟩ := ih
    have hL : N₂.IsLattice ℚ :=
      isLattice_of_isNbrL (prime_natCast hp.out).ne_zero (latOf_isLattice γ₁) hstep
    obtain ⟨γ₂, hγ₂⟩ := exists_latOf_of_isPrincipalIdealRing (⟨N₂, hL⟩ : Lat ℚ n)
    have hγ₂' : N₂ = latOf γ₂ := hγ₂
    subst hγ₂'
    have h₂ : IsIntegral (formF (up Q)) (latOf γ₂) := hstep.int_right
    exact ⟨γ₂, h₂, rfl, hr.tail ⟨_, isNbrForm_of_isNbrL h₁ h₂ hstep, IsometricGL.refl _⟩⟩

/-! ### Kneser's theorem over $\mathbb Z$ -/

/-- **Kneser's neighbour theorem for integral forms** (Kneser 1957, Satz 2 [unverified]). Let $Q$ be a positive definite
integral form in $n \ge 3$ variables, $p$ an odd prime with $p \nmid \det H$, and assume the genus of $\mathbb Z^n$ in $(\mathbb Q^n, Q)$ is a single spinor genus (`hgs`). Then every
form $Q'$ in the genus of $Q$ is $\mathrm{GL}_n(\mathbb Z)$-equivalent to a form reachable from $Q$ in the $p$-neighbour graph. -/
@[kb "kneser1957" "Satz 2 [unverified]"]
theorem exists_nbrReach_intEquiv (Q : QuadForm ℤ n) (hQ : IntQF.PosDef Q) (hn : 3 ≤ n) (p : ℕ) [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    (hgs : ∀ M : Lat ℚ n, Lattices.SameGenus (formF (up Q)) intVec M.1 →
      SameSpinorGenus (formF (up Q)) (HilbertModular.stdLat (F := ℚ)) M)
    {Q' : QuadForm ℤ n} (hg : Siegel.SameGenus Q Q') : ∃ Q'', NbrReach p Q Q'' ∧ IntEquiv Q'' Q' := by
  have hπ := prime_natCast hp.out
  obtain ⟨γ, hγ, hgen, rfl⟩ := exists_latOf_of_sameGenus Q hQ hg
  have hnd : (formF (up Q)).Nondegenerate :=
    IsTotallyPosDef.nondegenerate ((isTotallyPosDef_up_iff Q).mpr hQ)
  have hdv : (up Q).hessian.det ∉ (hosOf hπ).asIdeal := by
    rw [hosOf_asIdeal, Ideal.mem_span_singleton]
    intro hd
    apply hdet
    have h' := map_dvd (eZ : 𝓞 ℚ →+* ℤ) hd
    have e : (eZ : 𝓞 ℚ →+* ℤ) (up Q).hessian.det = Q.hessian.det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [up, Siegel.toOQ, QuadForm.hessian, QuadForm.map]
    rwa [e, map_natCast] at h'
  have h2v : (2 : 𝓞 ℚ) ∉ (hosOf hπ).asIdeal := by
    rw [hosOf_asIdeal, Ideal.mem_span_singleton]; exact not_dvd_two hp.out hp2
  have hiso := Lattices.isotropicIn_formF_of_unimodular (up Q) hn h2v hdv
  obtain ⟨M', hiso', hchain⟩ := kneser_reach_genus_uncond (formF (up Q)) hn hnd hπ (not_dvd_two hp.out hp2) hiso
    (L := HilbertModular.stdLat) (isIntegral_stdLat (up Q)) (KneserLocal.isUnimodularAt_intVec (up Q) hdv) hgs
    (M := ⟨latOf γ, latOf_isLattice γ⟩) hgen
  have hc : Relation.ReflTransGen (IsNbrL (formF (up Q)) (p : 𝓞 ℚ)) (latOf 1) M'.1 := by
    rw [latOf_one]; exact hchain
  obtain ⟨γ', hγ', hM', hr⟩ := nbrReach_of_chain (isIntegral_latOf_one (up Q)) hc
  rw [gramZ_one, down_up] at hr
  refine ⟨_, hr, ?_⟩
  rw [hM'] at hiso'
  exact (intEquiv_down_gramZ_iff Q γ' γ hγ' hγ).mpr hiso'.symm

/-- **The closure completeness criterion, unconditional** (Kneser 1957, §2 [unverified]; Scharlau–Hemkemeier 1998, §2): under
the hypotheses of `exists_nbrReach_intEquiv`, if a list $S$ of forms contains a form equivalent to $Q$ and is closed under
$p$-neighbour steps (as certified by `exists_intEquiv_of_cover`), then every form in the genus of $Q$ is equivalent to a member
of $S$. -/
@[kb "kneser1957" "§2 [unverified]"]
theorem exists_intEquiv_of_closed_kneser (Q : QuadForm ℤ n) (hQ : IntQF.PosDef Q) (hn : 3 ≤ n) (p : ℕ)
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    (hgs : ∀ M : Lat ℚ n, Lattices.SameGenus (formF (up Q)) intVec M.1 →
      SameSpinorGenus (formF (up Q)) (HilbertModular.stdLat (F := ℚ)) M)
    (S : List (QuadForm ℤ n)) (hS : ∃ s ∈ S, IntEquiv s Q)
    (hclosed : ∀ s ∈ S, ∀ Q', IsNbrForm p s Q' → ∃ s' ∈ S, IntEquiv s' Q')
    {Q' : QuadForm ℤ n} (hg : Siegel.SameGenus Q Q') : ∃ s ∈ S, IntEquiv s Q' := by
  obtain ⟨Q'', hr, he⟩ := exists_nbrReach_intEquiv Q hQ hn p hp2 hdet hgs hg
  obtain ⟨s, hs, hsQ⟩ := exists_intEquiv_of_reach S hclosed hS hr
  exact ⟨s, hs, IsometricGL.trans hsQ he⟩

end QuadFormsKB.Siegel.Kneser.Bridge
