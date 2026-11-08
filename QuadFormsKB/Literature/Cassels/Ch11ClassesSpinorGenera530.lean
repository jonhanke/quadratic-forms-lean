/-
# Cassels, Chapter 11, Theorem 1.4 / §3: classes in an indefinite genus, $n$ odd, = proper spinor genera

J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Theorem 1.4 (p. 202, Eichler) and Theorem 3.1.

**Layer:** an integer-valued form $f$ = `f : QuadForm ℤ n` with $\det H_f \ne 0$, the rational space
$V = (\mathbb Q^n, f)$ (`f.map (Int.castRingHom ℚ)`), $\Lambda = \mathbb Z^n$ (`stdLat`).

**Proves** (`ncard_genusClasses_eq_properSpinorGenusNumber`): if $f$ is indefinite and $n \ge 3$ is **odd**, the number
of $\mathrm{GL}_n(\mathbb Z)$-classes in the (Siegel) genus of $f$ equals the number $g^+(\mathbb Z^n)$ of proper
spinor genera in the genus of $\mathbb Z^n$ in $V$. With Cassels' count (`properSpinorGenusNumber_eq_card_casselsG`)
this is $|G|$ (`ncard_genusClasses_eq_card_casselsG`), and in particular two classes when $|G| = 2$
(`ncard_genusClasses_eq_two_of_card`).

*Route.* Send a class $c$ to the proper spinor genus of the lattice $\gamma\mathbb Z^n$, where $\gamma$ has determinant
$1$ and $f(\gamma x) = g(x)$ for the chosen representative $g$ of $c$ (`classSpn`). *Injective*: equal proper spinor
genera give a proper isometry (Theorem 1.4, `isProperIsometric_of_sameProperSpinorGenus`), hence an integral
equivalence (`intEquiv_of_sameProperSpinorGenus`, as in Cassels' Lemma 1.1, Corollary 2). *Surjective*: every lattice of
the genus of $\mathbb Z^n$ is free, $\gamma\mathbb Z^n$ (`exists_form_of_lattice`), and its Gram form $g$ lies in the
genus of $f$; the lattice of the chosen $\gamma'$ for $g$ is isometric to it, and since $n$ is odd, $-1 \in O(V)$ has
determinant $-1$ and fixes every lattice, so the isometry may be taken proper (`isProperIsometric_of_isIsometric`).
-/
import QuadFormsKB.Literature.Cassels.Ch11SpinorGeneraCount530
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus
import QuadFormsKB.Literature.Cassels.Ch11Sec1Indef
import QuadFormsKB.Literature.ConwaySloane.Section9Group

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

/-- **For $n$ odd, an isometry of lattices may be taken proper**: if $L$, $M$ are isometric lattices in a nondegenerate
space $(F^n, Q)$ of odd dimension, they are properly isometric ($-1 \in O(V)$ has determinant $(-1)^n = -1$ and fixes
every lattice). Arguments: `Q` the form, `hQ` nondegenerate, `hodd` odd dimension, `h` the isometry of `L` and `M`. -/
theorem isProperIsometric_of_isIsometric {F : Type} [Field F] [NumberField F] (Q : QuadForm F n)
    (hQ : Q.Nondegenerate) (hodd : Odd n) {L M : Submodule (𝓞 F) (Fin n → F)} (h : IsIsometric Q L M) :
    IsProperIsometric Q L M := by
  obtain ⟨ρ, hρ, he⟩ := h
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ (⟨ρ, hρ⟩ : orthGroup Q F) with h1 | h1
  · exact ⟨⟨ρ, hρ⟩, Tamagawa.mem_soSub.mpr h1, he⟩
  · let ν : GL (Fin n) F := -1
    have hν : ν ∈ orthGroup Q F := by
      show (ν.val)ᵀ * Q.hessian.map (algebraMap F F) * ν.val = Q.hessian.map (algebraMap F F)
      simp [ν]
    have hνL : glImage ν L = L := by
      ext x
      rw [mem_glImage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : ν.val *ᵥ y = -y := by simp [ν, Matrix.neg_mulVec]
        rw [this]; exact L.neg_mem hy
      · intro hx
        exact ⟨-x, L.neg_mem hx, by simp [ν, Matrix.neg_mulVec]⟩
    refine ⟨⟨ρ * ν, (orthGroup Q F).mul_mem hρ hν⟩, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub]
      change (ρ * ν).val.det = 1
      rw [Units.val_mul, det_mul]
      have h1' : ρ.val.det = -1 := h1
      have : ν.val.det = -1 := by
        simp [ν, Matrix.det_neg, hodd.neg_one_pow]
      rw [h1', this]; ring
    · change glImage (ρ * ν) L = M
      rw [glImage_mul, hνL]; exact he

variable (f : QuadForm ℤ n)

/-- The bridge `FormOf` for the Gram form of a free integral lattice in the genus of $\mathbb Z^n$: the integer form
$\mathrm{down}(\mathrm{gramZ})$ of the basis $\gamma$ satisfies $F(x) = f(\gamma x)$. Arguments: `f` the form, `γ` the
basis, `h` the integrality of $\gamma\mathbb Z^n$. -/
theorem formOf_down_gramZ (γ : GL (Fin n) ℚ)
    (h : IsIntegral (HilbertModular.formF (Tamagawa.RatBridge.up f)) (latOf γ)) :
    FormOf f γ (Tamagawa.RatBridge.down (gramZ (HilbertModular.formF (Tamagawa.RatBridge.up f)) γ h)) := by
  intro x
  have e : (Tamagawa.RatBridge.down
      (gramZ (HilbertModular.formF (Tamagawa.RatBridge.up f)) γ h)).map (Int.castRingHom ℚ) =
      gramFormF (HilbertModular.formF (Tamagawa.RatBridge.up f)).toQuadraticForm
        (fun j => γ.val *ᵥ Pi.single j 1) := by
    rw [← Tamagawa.RatBridge.formF_up, Tamagawa.RatBridge.up_down]
    exact gramZ_map _ γ h
  rw [← map_evalIn_rat, e]
  have := evalIn_gramFormF_col (HilbertModular.formF (Tamagawa.RatBridge.up f)) γ x
  rw [this, Tamagawa.RatBridge.formF_up, map_evalIn_rat]

/-- **Every lattice of the genus of $\mathbb Z^n$ is a basis lattice with an integral form of the genus of $f$**: for
$M$ in the genus of $\mathbb Z^n$ in $(\mathbb Q^n, f)$ there are $\gamma \in \mathrm{GL}_n(\mathbb Q)$ with
$M = \gamma\mathbb Z^n$ and an integer-valued form $F$ in the Siegel genus of $f$ with $F(x) = f(\gamma x)$.
Arguments: `f` the form, `M` the lattice, `hM` that $M$ is in the genus of $\mathbb Z^n$. -/
theorem exists_form_of_lattice (M : Lat ℚ n)
    (hM : SameGenus (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n).1 M.1) :
    ∃ (γ : GL (Fin n) ℚ) (F : QuadForm ℤ n), M.1 = latOf γ ∧ FormOf f γ F ∧ Siegel.SameGenus f F := by
  rw [← Tamagawa.RatBridge.formF_up] at hM
  obtain ⟨γ, hMγ, hi⟩ := Tamagawa.RatBridge.exists_free_of_sameGenus f M hM
  have hs : SameGenus (HilbertModular.formF (Tamagawa.RatBridge.up f)) intVec (latOf γ) := hMγ ▸ hM
  exact ⟨γ, _, hMγ, formOf_down_gramZ f γ hi, Tamagawa.RatBridge.sameGenus_down_gramZ f γ hs hi⟩

/-- **Equivalent integral forms give isometric lattices**: if $F(x) = f(\gamma x)$, $F'(x) = f(\gamma' x)$ and
$F'$, $F$ are integrally equivalent, then $\gamma\mathbb Z^n$ and $\gamma'\mathbb Z^n$ are isometric in $(\mathbb Q^n, f)$.
Arguments: `hF`, `hF'` the bases, `h` the equivalence of $F'$ and $F$. -/
theorem isIsometric_of_intEquiv {γ γ' : GL (Fin n) ℚ} {F F' : QuadForm ℤ n} (hF : FormOf f γ F)
    (hF' : FormOf f γ' F') (h : Siegel.IntEquiv F' F) :
    IsIsometric (f.map (Int.castRingHom ℚ)) (latOf γ) (latOf γ') := by
  rw [isIsometric_latOf_iff _ γ γ' (isIntegral_latOf hF) (isIntegral_latOf hF'), gramZ_eq_map hF',
    gramZ_eq_map hF]
  exact Siegel.IsometricGL.map _ h

/-- **Injectivity** (Cassels, Ch. 11, Thm. 1.4 and Lemma 1.1, Cor. 2): if $g_1(x) = f(\gamma_1 x)$ and
$g_2(x) = f(\gamma_2 x)$ with $\det\gamma_i = 1$ and the lattices $\gamma_i\mathbb Z^n$ are in one proper spinor genus,
then $g_1$ and $g_2$ are integrally equivalent ($f$ indefinite, $n \ge 3$). -/
theorem intEquiv_of_sameProperSpinorGenus (hn : 3 ≤ n) (hf : f.hessian.det ≠ 0)
    (hind : IsIndefinite (f.map (Int.castRingHom ℚ))) {g₁ g₂ : QuadForm ℤ n} {γ₁ γ₂ : GL (Fin n) ℚ}
    (h₁ : (γ₁ : Matrix (Fin n) (Fin n) ℚ).det = 1) (F₁ : FormOf f γ₁ g₁)
    (h₂ : (γ₂ : Matrix (Fin n) (Fin n) ℚ).det = 1) (F₂ : FormOf f γ₂ g₂)
    (hsp : SameProperSpinorGenus (f.map (Int.castRingHom ℚ)) ⟨latOf γ₁, latOf_isLattice γ₁⟩
      ⟨latOf γ₂, latOf_isLattice γ₂⟩) : Siegel.IntEquiv g₁ g₂ := by
  have hQnd := nondegenerate_map_of_det_ne_zero f hf
  obtain ⟨σ, hσ, hσL⟩ := isProperIsometric_of_sameProperSpinorGenus (f.map (Int.castRingHom ℚ)) hn hQnd hind hsp
  have hσ1 : ((σ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 := hσ
  have hlat : latOf γ₂ = latOf ((σ : GL (Fin n) ℚ) * γ₁) := by
    show _ = glImage ((σ : GL (Fin n) ℚ) * γ₁) intVec
    rw [glImage_mul]
    exact hσL.symm
  have hdet : (((σ : GL (Fin n) ℚ) * γ₁ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    rw [Units.val_mul, det_mul, hσ1, h₁, one_mul]
  obtain ⟨U, hUdet, hU⟩ := exists_unimod_of_latOf_eq (γ := γ₂) (δ := (σ : GL (Fin n) ℚ) * γ₁)
    (by rw [h₂]; exact one_pos) (by rw [hdet]; exact one_pos) hlat
  have hF' : FormOf f ((σ : GL (Fin n) ℚ) * γ₁) g₁ := fun x => by
    rw [F₁ x, Units.val_mul, ← mulVec_mulVec]
    have := evalIn_mulVec_of_mem (f.map (Int.castRingHom ℚ)) σ.2 (γ₁.val *ᵥ x)
    rw [map_evalIn_rat, map_evalIn_rat] at this
    exact this.symm
  have key := eval_eq_of_latOf_eq f F₂ hF' hU
  exact (Siegel.isometricGL_iff_isometricIn _ _).mpr
    ⟨U, by rw [hUdet]; exact isUnit_one, fun x => (key x).symm⟩

open Classical in
/-- A chosen basis $\gamma$ of determinant $1$ with $g(x) = f(\gamma x)$ (junk value $1$ if none exists). -/
def gammaOfForm (g : QuadForm ℤ n) : GL (Fin n) ℚ :=
  if h : ∃ γ : GL (Fin n) ℚ, (γ : Matrix (Fin n) (Fin n) ℚ).det = 1 ∧ FormOf f γ g then h.choose else 1

theorem gammaOfForm_spec {g : QuadForm ℤ n}
    (h : ∃ γ : GL (Fin n) ℚ, (γ : Matrix (Fin n) (Fin n) ℚ).det = 1 ∧ FormOf f γ g) :
    ((gammaOfForm f g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 ∧ FormOf f (gammaOfForm f g) g := by
  unfold gammaOfForm
  rw [dif_pos h]
  exact h.choose_spec

/-- A form of the genus of $f$ has a basis of determinant $1$ (rational equivalence, Hasse–Minkowski). -/
theorem exists_gamma_of_sameGenus (hn : 1 ≤ n) (hf : f.hessian.det ≠ 0) {g : QuadForm ℤ n}
    (h : Siegel.SameGenus f g) :
    ∃ γ : GL (Fin n) ℚ, (γ : Matrix (Fin n) (Fin n) ℚ).det = 1 ∧ FormOf f γ g := by
  have hd := h.hessian_det_eq
  exact exists_pos_det_one f g hn hd hf (isometricGL_rat_of_sameGenus f g hd hf h)

/-- The proper spinor genus attached to a class: that of $\gamma\mathbb Z^n$ for the chosen basis $\gamma$ of the
chosen representative. -/
def classSpn (c : Siegel.QClass n) : Quotient (properSpnSetoid (f.map (Int.castRingHom ℚ))) :=
  Quotient.mk _ ⟨latOf (gammaOfForm f c.out), latOf_isLattice _⟩

theorem classOf_out (c : Siegel.QClass n) : Siegel.classOf c.out = c := Quotient.out_eq c

theorem sameGenus_out {c : Siegel.QClass n} (hc : c ∈ Siegel.genusClasses f) : Siegel.SameGenus f c.out :=
  Siegel.classOf_mem_genusClasses_iff.mp (by rw [classOf_out]; exact hc)

/-- **Classes in the genus = proper spinor genera in the genus of $\mathbb Z^n$ ($n$ odd, $f$ indefinite)**
(Cassels, Ch. 11, Thm. 1.4, p. 203, with $-1$ an improper automorph for $n$ odd): for an integer-valued indefinite form
$f$ with $\det H_f \ne 0$ in an odd number $n \ge 3$ of variables, the number of $\mathrm{GL}_n(\mathbb Z)$-classes in
the genus of $f$ equals the number of proper spinor genera in the genus of $\mathbb Z^n$ in $(\mathbb Q^n, f)$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.4, p. 203 (indefinite, n odd: classes = spinor genera)"]
theorem ncard_genusClasses_eq_properSpinorGenusNumber (hn : 3 ≤ n) (hodd : Odd n) (hf : f.hessian.det ≠ 0)
    (hind : IsIndefinite (f.map (Int.castRingHom ℚ))) :
    (Siegel.genusClasses f).ncard =
      properSpinorGenusNumber (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n) := by
  have hQnd := nondegenerate_map_of_det_ne_zero f hf
  have e1 : latOf (1 : GL (Fin n) ℚ) = (stdLat : Lat ℚ n).1 := by
    rw [latOf, glImage_one]; rfl
  have hinj : Set.InjOn (classSpn f) (Siegel.genusClasses f) := by
    intro c₁ hc₁ c₂ hc₂ h
    have hs₁ := sameGenus_out f hc₁
    have hs₂ := sameGenus_out f hc₂
    obtain ⟨d₁, F₁⟩ := gammaOfForm_spec f (exists_gamma_of_sameGenus f (by omega) hf hs₁)
    obtain ⟨d₂, F₂⟩ := gammaOfForm_spec f (exists_gamma_of_sameGenus f (by omega) hf hs₂)
    have hsp : SameProperSpinorGenus (f.map (Int.castRingHom ℚ)) ⟨latOf (gammaOfForm f c₁.out), latOf_isLattice _⟩
        ⟨latOf (gammaOfForm f c₂.out), latOf_isLattice _⟩ := Quotient.exact h
    rw [← classOf_out c₁, ← classOf_out c₂]
    exact Siegel.classOf_eq_classOf_iff.mpr
      (intEquiv_of_sameProperSpinorGenus f hn hf hind d₁ F₁ d₂ F₂ hsp)
  have himg : classSpn f '' Siegel.genusClasses f = genusProperSpinorGenera (f.map (Int.castRingHom ℚ)) stdLat := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hs := sameGenus_out f hc
      obtain ⟨d, F⟩ := gammaOfForm_spec f (exists_gamma_of_sameGenus f (by omega) hf hs)
      refine ⟨⟨latOf (gammaOfForm f c.out), latOf_isLattice _⟩, rfl, ?_⟩
      have := sameGenus_latOf_of_sameGenus F hs
      rwa [e1] at this
    · rintro ⟨M, rfl, hM⟩
      obtain ⟨γ, F, hMγ, hFγ, hFg⟩ := exists_form_of_lattice f M hM
      refine ⟨Siegel.classOf F, Siegel.classOf_mem_genusClasses_iff.mpr hFg, ?_⟩
      set g := (Siegel.classOf F).out with hg
      have hgF : Siegel.IntEquiv g F := Siegel.classOf_eq_classOf_iff.mp (classOf_out _)
      have hgs : Siegel.SameGenus f g := hFg.trans (Siegel.IntEquiv.sameGenus (Siegel.IsometricGL.symm hgF : Siegel.IntEquiv F g))
      obtain ⟨d, Fg⟩ := gammaOfForm_spec f (exists_gamma_of_sameGenus f (by omega) hf hgs)
      have hiso : IsIsometric (f.map (Int.castRingHom ℚ)) (latOf γ) (latOf (gammaOfForm f g)) :=
        isIsometric_of_intEquiv f hFγ Fg hgF
      have hprop := (isProperIsometric_of_isIsometric _ hQnd hodd hiso).symm
      refine Quotient.sound ?_
      refine IsProperIsometric.sameProperSpinorGenus _ ?_
      change IsProperIsometric _ (latOf (gammaOfForm f g)) M.1
      rw [hMγ]; exact hprop
  rw [properSpinorGenusNumber, ← himg, Set.InjOn.ncard_image hinj]

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Number of classes = $|G|$** (Cassels, Ch. 11, Thm. 1.4 and Thm. 3.1): for an indefinite integer-valued form $f$
with $\det H_f \ne 0$ in an odd number $n \ge 3$ of variables and a finite set $P$ of primes outside of which $p \nmid
2\det H_f$ (`hPd`), the number of classes in the genus of $f$ is the order of Cassels' group $G = R/ST$ of
$\Lambda = \mathbb Z^n$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.4 and Thm. 3.1 (indefinite, n odd: classes = |G|)"]
theorem ncard_genusClasses_eq_card_casselsG (hn : 3 ≤ n) (hodd : Odd n) (hf : f.hessian.det ≠ 0)
    (hind : IsIndefinite (f.map (Int.castRingHom ℚ))) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hPd : ∀ v, v ∉ P → ¬ ((ConwaySloane.primeOf v : ℕ) : ℤ) ∣ 2 * f.hessian.det) :
    (Siegel.genusClasses f).ncard =
      Nat.card (CasselsG (f.map (Int.castRingHom ℚ)) (nondegenerate_map_of_det_ne_zero f hf) stdLat P) := by
  rw [ncard_genusClasses_eq_properSpinorGenusNumber f hn hodd hf hind]
  exact properSpinorGenusNumber_eq_card_casselsG _ _ _ P hn
    (ConwaySloane.casselsCond_std (by omega) f (nondegenerate_map_of_det_ne_zero f hf) P hPd)

/-- **Two classes when $|G| = 2$** (corollary): under the hypotheses of `ncard_genusClasses_eq_card_casselsG`, if
$|G| = 2$ then the genus of $f$ has exactly two classes. Argument `hG`: $G$ has order $2$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.4 and Thm. 3.1 (indefinite, n odd: |G| = 2 gives two classes)"]
theorem ncard_genusClasses_eq_two_of_card (hn : 3 ≤ n) (hodd : Odd n) (hf : f.hessian.det ≠ 0)
    (hind : IsIndefinite (f.map (Int.castRingHom ℚ))) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hPd : ∀ v, v ∉ P → ¬ ((ConwaySloane.primeOf v : ℕ) : ℤ) ∣ 2 * f.hessian.det)
    (hG : Nat.card (CasselsG (f.map (Int.castRingHom ℚ)) (nondegenerate_map_of_det_ne_zero f hf) stdLat P) = 2) :
    (Siegel.genusClasses f).ncard = 2 := by
  rw [ncard_genusClasses_eq_card_casselsG f hn hodd hf hind P hPd, hG]

end QuadFormsKB.Lattices
