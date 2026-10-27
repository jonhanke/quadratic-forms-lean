/-
# Cassels, Chapter 11, Theorem 6.2: chains avoiding a finite set of primes

**Layer:** as in `Ch11Sec6.lean` (integer forms, classical integrality, determinant = `hessian.det`, proper
$\mathbb Z$-equivalence by $U \in \mathrm{SL}_n(\mathbb Z)$, Cassels' substitution `casselsSubst`), with the genus
`Siegel.SameGenus`.

**Proves** Cassels' Theorem 6.2 (p. 225), first part (`exists_chain_of_sameGenus`): for classically integral forms
$f_1, f_2$ of the same genus and determinant $d \ne 0$ in $n \ge 2$ variables and a finite set $P$ of primes, the chain
of Theorem 6.1 exists with every prime $p$ of a step (ii) outside $P$. *Proof* (Cassels): by Lemma 4.2 (proper class)
the lattice of $f_2$ may be replaced by a properly equivalent one $\Gamma$ with $I(\Lambda, \Gamma)$ prime to $P$, and
the proof of Theorem 6.1 uses only primes dividing $I(\Lambda, \Gamma)$ (`exists_chain_coreD`). The converse part is
`sameGenus_of_chain`.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec6
import QuadFormsKB.Literature.Cassels.Ch11Sec4Proper
import QuadFormsKB.Lattices.Forms
import QuadFormsKB.Lattices.FreeBridge
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### The chain relation with all (ii)-primes dividing a given integer -/

section ChainD

open Tamagawa.SiegelSpace

/-- One step of Theorem 6.1, with the prime of (ii) required to divide `m`. -/
def ChainStepD (m : ℕ) (F G : QuadForm ℤ n) : Prop :=
  (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, G.eval x = F.eval (U *ᵥ x)) ∨
    ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ∀ x : Fin n → ℚ, (G.map (Int.castRingHom ℚ)).evalIn ℚ x =
      (F.map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x)

/-- The chain relation with all (ii)-primes dividing `m`. -/
def ChainRelD (f : QuadForm ℤ n) (m : ℕ) (F G : QuadForm ℤ n) : Prop :=
  GoodForm f F ∧ GoodForm f G ∧ ChainStepD m F G

theorem chainRelD_of_latOf_eq {f : QuadForm ℤ n} {m : ℕ} {γ δ : GL (Fin n) ℚ}
    (hγ : 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det) (hδ : 0 < (δ : Matrix (Fin n) (Fin n) ℚ).det)
    (h : latOf γ = latOf δ) {F G : QuadForm ℤ n} (hF : FormOf f γ F) (hG : FormOf f δ G)
    (hFg : GoodForm f F) (hGg : GoodForm f G) : ChainRelD f m F G := by
  obtain ⟨U, hU1, hU⟩ := exists_unimod_of_latOf_eq hδ hγ h.symm
  exact ⟨hFg, hGg, Or.inl ⟨U, hU1, eval_eq_of_latOf_eq f hG hF hU⟩⟩

/-- `reach_prime`, recording that the prime of the step (ii) divides `m`. -/
theorem reach_primeD (hn : 2 ≤ n) {f : QuadForm ℤ n} {m : ℕ} {L M : Lat ℚ n} (hL : LatGood f L)
    (hM : LatGood f M) {p : ℕ}
    (hp : p.Prime) (hpm : p ∣ m) (hI : casselsI M L = p) {γ δ : GL (Fin n) ℚ}
    (hγ : 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det) (hδ : 0 < (δ : Matrix (Fin n) (Fin n) ℚ).det)
    (hγL : latOf γ = L.1) (hδM : latOf δ = M.1) {F G : QuadForm ℤ n}
    (hF : FormOf f γ F) (hFg : GoodForm f F) (hG : FormOf f δ G) (hGg : GoodForm f G) :
    Relation.ReflTransGen (ChainRelD f m) F G := by
  have hlat : latIndex M = latIndex L := hM.2.trans hL.2.symm
  obtain ⟨b, hli, hMs, hLs⟩ := exists_basis_of_casselsI_prime hn hlat hp hI
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0 : 0 < n := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  set B : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => b j i with hB
  have hBcol : ∀ j, B *ᵥ Pi.single j (1 : ℚ) = b j := by
    intro j; ext i; simp [B, mulVec, dotProduct, Pi.single_apply]
  have hBu : IsUnit B.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    convert hli using 1
    funext j; ext i; rfl
  set t : Fin n → ℚ := fun j => if j.1 = n - 1 then (p : ℚ) else 1 with ht
  set S : Matrix (Fin n) (Fin n) ℚ := casselsSubstDiag n p with hS
  have hSdet : S.det = 1 := det_casselsDiag hn hp.ne_zero
  have htu : IsUnit (Matrix.diagonal t).det := by
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by simp only [ht]; split_ifs <;> simp [hp0]
  have h1u : IsUnit (B * Matrix.diagonal t).det := by rw [det_mul]; exact hBu.mul htu
  have h2u : IsUnit (B * Matrix.diagonal t * S).det := by
    rw [det_mul, hSdet]; simpa using h1u
  set γ₁ : GL (Fin n) ℚ := Matrix.nonsingInvUnit _ h1u with hγ₁
  set γ₂ : GL (Fin n) ℚ := Matrix.nonsingInvUnit _ h2u with hγ₂
  have hγ₁v : (γ₁ : Matrix (Fin n) (Fin n) ℚ) = B * Matrix.diagonal t := rfl
  have hγ₂v : (γ₂ : Matrix (Fin n) (Fin n) ℚ) = γ₁.val * S := rfl
  have hLγ₁ : latOf γ₁ = L.1 := by
    rw [latOf_eq_span, hLs, hγ₁v]
    congr 2
    ext j : 1
    rw [cols_mul_diagonal, hBcol]
    simp only [ht]
    split_ifs <;> simp
  have hMγ₂ : latOf γ₂ = M.1 := by
    rw [latOf_eq_span, hMs, hγ₂v, hγ₁v, Matrix.mul_assoc, hS, casselsSubstDiag, diagonal_mul_diagonal]
    congr 2
    ext j : 1
    rw [cols_mul_diagonal, hBcol]
    simp only [ht]
    by_cases h0' : j.1 = 0
    · simp [h0', hn1.symm]
    · by_cases hl : j.1 = n - 1
      · simp [h0', hl, hn1, hp0]
      · simp [h0', hl]
  have hs0 : (γ₁ : Matrix (Fin n) (Fin n) ℚ).det ≠ 0 := (γ₁.isUnit.map Matrix.detMonoidHom).ne_zero
  obtain ⟨E, hEv, hEstab, hEdet⟩ := exists_signMat hn0
    (if 0 < (γ₁ : Matrix (Fin n) (Fin n) ℚ).det then 1 else -1) (by split_ifs <;> simp)
  have hpos1 : 0 < ((γ₁ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
    rw [Units.val_mul, det_mul, hEdet]
    split_ifs with h
    · simpa using h
    · have := lt_of_le_of_ne (not_lt.mp h) hs0
      nlinarith
  have hES : E.val * S = S * E.val := by
    rw [hEv, hS, casselsSubstDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext j; ring
  have hv2 : ((γ₂ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) =
      ((γ₁ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) * S := by
    rw [Units.val_mul, Units.val_mul, hγ₂v, Matrix.mul_assoc, Matrix.mul_assoc, hES]
  have hpos2 : 0 < ((γ₂ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
    rw [hv2, det_mul, hSdet, mul_one]; exact hpos1
  have hL1 : latOf (γ₁ * E) = L.1 := by
    rw [← hLγ₁, latOf, latOf, glImage_mul, hEstab]
  have hM2 : latOf (γ₂ * E) = M.1 := by
    rw [← hMγ₂, latOf, latOf, glImage_mul, hEstab]
  obtain ⟨F', hF', hF'g⟩ := exists_good_formOf hL hL1
  obtain ⟨G', hG', hG'g⟩ := exists_good_formOf hM hM2
  have R1 : ChainRelD f m F F' := chainRelD_of_latOf_eq hγ hpos1 (by rw [hγL, hL1]) hF hF' hFg hF'g
  have R3 : ChainRelD f m G' G := chainRelD_of_latOf_eq hpos2 hδ (by rw [hδM, hM2]) hG' hG hG'g hGg
  have R2 : ChainRelD f m F' G' := by
    refine ⟨hF'g, hG'g, Or.inr ⟨p, hp, hpm, fun x => ?_⟩⟩
    rw [map_evalIn_rat, map_evalIn_rat, hG', hF', casselsSubst_eq, mulVec_mulVec, ← hv2]
  exact ((Relation.ReflTransGen.single R1).tail R2).tail R3

/-- **The core of Theorem 6.1 for an arbitrary lattice $\Gamma = g\mathbb Z^n$ ($\det g = 1$)**, recording that every
prime of a step (ii) divides $I(\mathbb Z^n, \Gamma)$. -/
theorem exists_chain_coreD (hn : 2 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (g : GL (Fin n) ℚ)
    (hg1 : (g : Matrix (Fin n) (Fin n) ℚ).det = 1) (hFg : FormOf f₁ g f₂)
    (M : Lat ℚ n) (hM : M.1 = latOf g) :
    Relation.ReflTransGen
      (ChainRelD f₁ (casselsI (⟨latOf 1, latOf_isLattice 1⟩ : Lat ℚ n) M)) f₁ f₂ := by
  have hn0 : 0 < n := by omega
  set Q := f₁.map (Int.castRingHom ℚ) with hQdef
  set m := casselsI (⟨latOf 1, latOf_isLattice 1⟩ : Lat ℚ n) M with hm
  have hF1 : FormOf f₁ 1 f₁ := fun x => by simp
  have hΛCI : LatCI Q (latOf 1) := latCI_latOf f₁ hF1 h₁
  have hΓCI : LatCI Q M.1 := by rw [hM]; exact latCI_latOf f₁ hFg h₂
  have hΛ1 : latIndex (⟨latOf 1, latOf_isLattice 1⟩ : Lat ℚ n) = 1 := by
    have := latIndex_latOf (1 : GL (Fin n) ℚ); simpa using this
  have hΓ1 : latIndex M = 1 := by
    have e : (⟨latOf g, latOf_isLattice g⟩ : Lat ℚ n) = M := Subtype.ext hM.symm
    have := latIndex_latOf g; rw [hg1, e] at this; simpa using this
  obtain ⟨J, Λs, h0, hlast, hlatΛ, hprime, hprod, hint⟩ := exists_casselsI_chain Q
    (L := ⟨latOf 1, latOf_isLattice 1⟩) (M := M) (hΛ1.trans hΓ1.symm)
    Set.univ (fun _ _ => Set.mem_univ _)
    (fun v _ => (latCI_iff_loc Q _).mp hΛCI v) (fun v _ => (latCI_iff_loc Q _).mp hΓCI v)
  have hgood : ∀ j, LatGood f₁ (Λs j) := fun j =>
    ⟨(latCI_iff_loc Q _).mpr (fun v => hint j v (Set.mem_univ _)), (hlatΛ j).trans hΛ1⟩
  have key : ∀ k (hk : k ≤ J) (γ : GL (Fin n) ℚ) (F : QuadForm ℤ n),
      0 < (γ : Matrix (Fin n) (Fin n) ℚ).det → latOf γ = (Λs ⟨k, by omega⟩).1 → FormOf f₁ γ F →
      GoodForm f₁ F → Relation.ReflTransGen (ChainRelD f₁ m) f₁ F := by
    intro k
    induction k with
    | zero =>
      intro _ γ F hγ hL hF hFg
      have e : (⟨0, by omega⟩ : Fin (J + 1)) = 0 := rfl
      rw [e, h0] at hL
      exact Relation.ReflTransGen.single
        (chainRelD_of_latOf_eq (γ := 1) (by simp) hγ hL.symm hF1 hF ⟨h₁, rfl⟩ hFg)
    | succ k ih =>
      intro hk γ F hγ hL hF hFg
      set v : Fin J := ⟨k, by omega⟩ with hv
      have hv2 : (⟨k + 1, by omega⟩ : Fin (J + 1)) = v.succ := rfl
      rw [hv2] at hL
      obtain ⟨γk, hγk, hLk⟩ := exists_latOf_pos_rat hn0 (Λs v.castSucc)
      obtain ⟨Fk, hFk, hFkg⟩ := exists_good_formOf (hgood v.castSucc) hLk.symm
      have r1 := ih (by omega) γk Fk hγk hLk.symm hFk hFkg
      have hI : casselsI (Λs v.succ) (Λs v.castSucc) = casselsI (Λs v.castSucc) (Λs v.succ) :=
        casselsI_comm (((hgood v.succ).2).trans (hgood v.castSucc).2.symm)
      have hpm : casselsI (Λs v.castSucc) (Λs v.succ) ∣ m := by
        rw [hm, ← hprod]
        exact Finset.dvd_prod_of_mem (fun j : Fin J => casselsI (Λs j.castSucc) (Λs j.succ))
          (Finset.mem_univ v)
      have r2 := reach_primeD hn (hgood v.castSucc) (hgood v.succ) (hprime v) hpm hI hγk hγ hLk.symm hL
        hFk hFkg hF hFg
      exact r1.trans r2
  exact key J le_rfl g f₂ (by rw [hg1]; exact one_pos)
    (hM.symm.trans (congrArg Subtype.val hlast.symm)) hFg ⟨h₂, hd.symm⟩

end ChainD

/-! ### Same genus implies rational equivalence -/

theorem nondegenerate_map_of_det_ne_zero (f : QuadForm ℤ n) (hd0 : f.hessian.det ≠ 0) :
    (f.map (Int.castRingHom ℚ)).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [Siegel.Kneser.hessian_map, Siegel.Kneser.det_map_eq]
  simpa using hd0

/-- Forms in one genus (with nonzero determinant) are rationally equivalent (Hasse–Minkowski,
`isometric_of_everywhere`; the local data at $p$ and $\infty$ come from `Siegel.SameGenus`). -/
theorem isometricGL_rat_of_sameGenus (f₁ f₂ : QuadForm ℤ n) (hd : f₁.hessian.det = f₂.hessian.det)
    (hd0 : f₁.hessian.det ≠ 0) (hg : Siegel.SameGenus f₁ f₂) :
    Siegel.IsometricGL (f₁.map (Int.castRingHom ℚ)) (f₂.map (Int.castRingHom ℚ)) := by
  rw [Siegel.isometricGL_iff_isometricIn]
  refine isometric_of_everywhere _ _ (nondegenerate_map_of_det_ne_zero f₁ hd0)
    (nondegenerate_map_of_det_ne_zero f₂ (hd ▸ hd0)) fun v => ?_
  cases v with
  | infinite => exact Tamagawa.RatBridge.isometricIn_rat_of_isometricGL hg.2
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    have h1 := Tamagawa.RatBridge.isometricGL_map_hom (PadicInt.Coe.ringHom (p := p.1)) (hg.1 p.1)
    rw [QuadForm.map_map, QuadForm.map_map,
      RingHom.ext_int ((PadicInt.Coe.ringHom (p := p.1)).comp (Int.castRingHom ℤ_[p.1]))
        (Int.castRingHom ℚ_[p.1])] at h1
    exact Tamagawa.RatBridge.isometricIn_rat_of_isometricGL h1

/-! ### The genus of the lattices $\mathbb Z^n$ and $g\mathbb Z^n$ -/

/-- The integrality of the lattice of a basis `γ` for which `F` is the integer form. -/
theorem isIntegral_latOf {f F : QuadForm ℤ n} {γ : GL (Fin n) ℚ} (hF : FormOf f γ F) :
    IsIntegral (f.map (Int.castRingHom ℚ)) (latOf γ) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨a, rfl⟩ := mem_intVec_iff_exists.mp hz
  have h1 : (f.map (Int.castRingHom ℚ)).evalIn ℚ (γ.val *ᵥ intCoe a) = F.evalIn ℚ (intCoe a) := by
    rw [map_evalIn_rat, ← hF]
  show (f.map (Int.castRingHom ℚ)).evalIn ℚ (γ.val *ᵥ intCoe a) ∈ _
  rw [h1, Tamagawa.RatBridge.evalIn_intCoe_rat]
  exact ⟨_, rfl⟩

/-- The Gram form of the basis `γ` of an integral lattice is the integer form `F`. -/
theorem gramZ_eq_map {f F : QuadForm ℤ n} {γ : GL (Fin n) ℚ} (hF : FormOf f γ F)
    (h : IsIntegral (f.map (Int.castRingHom ℚ)) (latOf γ)) :
    gramZ (f.map (Int.castRingHom ℚ)) γ h = F.map (algebraMap ℤ (𝓞 ℚ)) := by
  have hinj : Function.Injective (algebraMap (𝓞 ℚ) ℚ) := IsFractionRing.injective (𝓞 ℚ) ℚ
  have e1 : (F.map (algebraMap ℤ (𝓞 ℚ))).map (algebraMap (𝓞 ℚ) ℚ) = F.map (Int.castRingHom ℚ) := by
    rw [QuadForm.map_map]
    congr 1
  have e2 : (gramZ (f.map (Int.castRingHom ℚ)) γ h).map (algebraMap (𝓞 ℚ) ℚ) =
      F.map (Int.castRingHom ℚ) := by
    rw [gramZ_map]
    refine QuadForm.eq_of_eval_eq fun y => ?_
    rw [eval_gramFormF_col]
    have := hF y
    change (f.map (Int.castRingHom ℚ)).evalIn ℚ (γ.val *ᵥ y) = (F.map (Int.castRingHom ℚ)).evalIn ℚ y
    rw [map_evalIn_rat, map_evalIn_rat]
    exact this.symm
  exact LocalDensity.NF.map_injective hinj (e2.trans e1.symm)

/-- **$\mathbb Z^n$ and $g\mathbb Z^n$ are in the same genus** of $(\mathbb Q^n, f_1)$ when $f_1, f_2$ are in the same
genus and $f_2$ is the form of $f_1$ in the basis $g$. -/
theorem sameGenus_latOf_of_sameGenus {f₁ f₂ : QuadForm ℤ n} {g : GL (Fin n) ℚ} (hFg : FormOf f₁ g f₂)
    (hg : Siegel.SameGenus f₁ f₂) :
    SameGenus (f₁.map (Int.castRingHom ℚ)) (latOf 1) (latOf g) := by
  have hF1 : FormOf f₁ 1 f₁ := fun x => by simp
  have h1 := isIntegral_latOf hF1
  have h2 := isIntegral_latOf hFg
  rw [sameGenus_latOf_iff _ 1 g h1 h2, gramZ_eq_map hF1 h1, gramZ_eq_map hFg h2]
  exact (formSameGenus_rat_iff f₁ f₂).mpr hg

/-- **Cassels, Theorem 6.2** (Ch. 11, p. 225), first part: *let $f_1, f_2$ be two classically integral forms of the
same genus of determinant $d \ne 0$ in $n \ge 2$ variables and let $P$ be any finite set of primes. Then the conclusion
of Theorem 6.1 holds and we can suppose in (ii) that $p \notin P$.* -/
@[kb "cassels1978" "Ch. 11, Thm. 6.2, p. 225 (first part)"]
theorem exists_chain_of_sameGenus (hn : 2 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (hd0 : f₁.hessian.det ≠ 0)
    (hg : Siegel.SameGenus f₁ f₂) (P : Finset ℕ) :
    ∃ (V : ℕ) (g : Fin (V + 1) → QuadForm ℤ n), g 0 = f₁ ∧ g (Fin.last V) = f₂ ∧
      (∀ v, IsClassicallyIntegral (g v) ∧ (g v).hessian.det = f₁.hessian.det) ∧
      ∀ v : Fin V,
        (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, (g v.succ).eval x = (g v.castSucc).eval (U *ᵥ x)) ∨
        ∃ p : ℕ, p.Prime ∧ p ∉ P ∧ ∀ x : Fin n → ℚ, ((g v.succ).map (Int.castRingHom ℚ)).evalIn ℚ x =
          ((g v.castSucc).map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x) := by
  classical
  have hQ := isometricGL_rat_of_sameGenus f₁ f₂ hd hd0 hg
  obtain ⟨g, hg1, hFg⟩ := exists_pos_det_one f₁ f₂ (by omega) hd hd0 hQ
  set Q := f₁.map (Int.castRingHom ℚ) with hQdef
  have hQnd : Q.Nondegenerate := nondegenerate_map_of_det_ne_zero f₁ hd0
  have hgen := sameGenus_latOf_of_sameGenus hFg hg
  set L : Lat ℚ n := ⟨latOf 1, latOf_isLattice 1⟩ with hL
  set Δ : Lat ℚ n := ⟨latOf g, latOf_isLattice g⟩ with hΔ
  set P₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    (P.subtype Nat.Prime).image
      (fun p : {p : ℕ // p.Prime} => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (p : Nat.Primes)) with hP₀
  obtain ⟨M', ⟨σ, hσdet, hσ⟩, hM'⟩ := exists_isProperIsometric_casselsI Q hQnd L P₀ (M := Δ) hgen
  -- the new basis σ g
  have hσd : (σ : GL (Fin n) ℚ).val.det = 1 := Tamagawa.mem_soSub.mp hσdet
  have hlat : M'.1 = latOf ((σ : GL (Fin n) ℚ) * g) := by
    rw [← hσ]
    change glImage (σ : GL (Fin n) ℚ) (latOf g) = glImage ((σ : GL (Fin n) ℚ) * g) intVec
    rw [glImage_mul]
    rfl
  have hdet' : ((σ : GL (Fin n) ℚ) * g).val.det = 1 := by
    rw [Units.val_mul, det_mul, hσd, hg1, one_mul]
  have hF' : FormOf f₁ ((σ : GL (Fin n) ℚ) * g) f₂ := fun x => by
    rw [hFg x, Units.val_mul, ← mulVec_mulVec]
    have := evalIn_mulVec_of_mem Q σ.2 (g.val *ᵥ x)
    simp only [hQdef, map_evalIn_rat] at this
    exact this.symm
  have hrt := exists_chain_coreD hn f₁ f₂ h₁ h₂ hd _ hdet' hF' M' hlat
  obtain ⟨V, c, h0, hl, hP, hr⟩ := exists_fin_of_reflTransGen
    (ChainRelD f₁ (casselsI L M')) (GoodForm f₁) (fun a b h => h.2.1) hrt ⟨h₁, rfl⟩
  refine ⟨V, c, h0, hl, fun v => hP v, fun v => ?_⟩
  rcases (hr v).2.2 with hU | ⟨p, hp, hpm, hsub⟩
  · exact Or.inl hU
  · refine Or.inr ⟨p, hp, fun hpP => ?_, hsub⟩
    set v₀ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (⟨p, hp⟩ : Nat.Primes) with hv₀
    have hv₀P : v₀ ∈ P₀ := by
      rw [hP₀, Finset.mem_image]
      exact ⟨⟨p, hp⟩, Finset.mem_subtype.mpr hpP, rfl⟩
    have hgen : Rat.HeightOneSpectrum.natGenerator v₀ = p := by
      have := congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply (⟨p, hp⟩ : Nat.Primes))
      exact this
    exact hM' v₀ hv₀P (hgen ▸ hpm)

end QuadFormsKB.Lattices
