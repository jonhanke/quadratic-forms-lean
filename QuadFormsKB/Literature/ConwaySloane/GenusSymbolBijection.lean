/-
# Conway–Sloane, Ch. 15, §7.8 made explicit: the genus symbol is a complete invariant of the genus

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7, pp. 378–384
(`conwaysloane1999`).
**The theorem.** Two nondegenerate classically integral forms $f(\vec x) = \vec x^{\mathsf T}A\vec x$,
$g(\vec x) = \vec x^{\mathsf T}B\vec x$ in $n$ variables ($A, B \in M_n(\mathbb Z)$ symmetric) are in the same genus iff
they have the same genus symbol: the same dimension and determinant, the same $(-1)$-adic symbol $+^r-^s$, the same
$p$-adic symbol at every odd prime $p$, and the same **canonical** 2-adic symbol (§7.6).

**The book leaves this implicit.** Conway–Sloane give the pieces (Thm. 9 for $p \ne 2$, p. 379; Thm. 10 and §7.6 for
$p = 2$, pp. 381–382; Sylvester at $p = -1$, §7.1, p. 379; Thm. 11 for existence, p. 383) and then, in §7.8 (p. 384),
use the genus symbol as a name for the genus, without stating the combined theorem. It is stated and proved here.

**Conventions.**
* The genus is `Siegel.SameGenus` (GL-equivalence over $\mathbb Z_p$ for every prime $p$ and over $\mathbb R$, Cassels
  Ch. 9, §1); the forms are `LocalDensity.ofMatrixZ A`.
* `GenusSymbolData.IsSymbolsOf` (`Theorem11.lean`) fixes the $(-1)$-adic model through $r$ only
  ($\langle 1^r, (-1)^{n-r}\rangle$); `IsGenusSymbolOf` adds $r + s = n$, so that $s$ is the symbol's, and lets the
  matrix be indexed by `Fin n` for any `n` with `G.n = n`.
* `SameSymbol` compares the 2-adic symbols through their canonical symbols (`TwoSymbol.canonicalSymbol`, total: the
  canonical symbol of §7.6 when the symbol is eventually of type II, as every symbol of a form is, and the symbol itself
  otherwise). The support bound `N` of `GenusSymbolData` is not part of the symbol and is ignored.
* Indices are 0-based.

**Defines** `TwoSymbol.canonicalSymbol`, `GenusSymbolData.SameSymbol` (an equivalence relation,
`GenusSymbolData.sameSymbolSetoid`), `GenusSymbolData.IsGenusSymbolOf`.

**Proves** (all unconditional)
* `exists_isGenusSymbolOf`: every nondegenerate symmetric integral matrix has a symbol system;
* `sameGenus_iff_sameSymbol` (**the main theorem**): same genus iff same genus symbol;
* `det_eq_of_sameGenus`: the determinant is a genus invariant (no definiteness assumed).
-/
import QuadFormsKB.Literature.ConwaySloane.GenusSymbolBijectionReal
import QuadFormsKB.Literature.ConwaySloane.GenusSymbol
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassification
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma3

namespace QuadFormsKB.ConwaySloane

open Matrix Cassels Siegel

/-! ### The canonical 2-adic symbol as a total function -/

open Classical in
/-- **The canonical 2-adic symbol** (Conway–Sloane, §7.6, p. 382) as a total function on 2-adic symbols: the canonical
symbol `canonical hσ` if $\sigma$ is of type II from some scale on (`EventuallyTypeII`; true for every symbol of a form,
`eventuallyTypeII_of_isTwoSymbolOf`), and $\sigma$ itself otherwise (a convention for symbols that come from no form). -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
noncomputable def TwoSymbol.canonicalSymbol (σ : TwoSymbol) : TwoSymbol :=
  if h : EventuallyTypeII σ then canonical h else σ

theorem TwoSymbol.canonicalSymbol_eq {σ : TwoSymbol} (h : EventuallyTypeII σ) :
    σ.canonicalSymbol = canonical h := by
  simp [TwoSymbol.canonicalSymbol, h]

/-- A symbol supported below $N$ is of type II from the scale $2^N$ on. -/
theorem eventuallyTypeII_of_supportedBelow {σ : TwoSymbol} {N : ℕ} (h : σ.SupportedBelow N) :
    EventuallyTypeII σ :=
  ⟨N, fun k hk => by unfold IsTypeI; rw [h k hk]; simp [TwoFactor.trivial]⟩

/-- Every 2-adic symbol of a form is eventually of type II. -/
theorem eventuallyTypeII_of_isTwoSymbolOf {n : ℕ} {F : Matrix (Fin n) (Fin n) ℚ_[2]} {σ : TwoSymbol}
    (h : IsTwoSymbolOf F σ) : EventuallyTypeII σ := by
  obtain ⟨N, hN⟩ := TwoAdic.supported_of_isTwoSymbolOf h
  exact eventuallyTypeII_of_supportedBelow hN

/-! ### Target 1: the same genus symbol -/

theorem RealSymbol.ext' {x y : RealSymbol} (h₁ : x.pos = y.pos) (h₂ : x.neg = y.neg) : x = y := by
  cases x; cases y; simp_all

/-- **The same genus symbol** (Conway–Sloane, §7.8, p. 384, with §7.6, p. 382): two systems of symbols have the same
dimension $n$, the same determinant $d$, the same $(-1)$-adic symbol $+^r-^s$, the same $p$-adic symbol at every odd
prime $p$ (as functions of the scale $p^k$, $k \ge 0$), and the same canonical 2-adic symbol. The support bound `N` is
ignored. -/
@[kb "conwaysloane1999" "Ch. 15, §7.8, p. 384"]
structure GenusSymbolData.SameSymbol (G H : GenusSymbolData) : Prop where
  /-- The same dimension $n$. -/
  n_eq : G.n = H.n
  /-- The same determinant $d$. -/
  det_eq : G.det = H.det
  /-- The same $(-1)$-adic symbol $+^r-^s$. -/
  real_eq : G.real = H.real
  /-- The same $p$-adic symbol at every odd prime $p$. -/
  odd_eq : ∀ p, p.Prime → p ≠ 2 → G.odd p = H.odd p
  /-- The same canonical 2-adic symbol. -/
  two_eq : G.two.canonicalSymbol = H.two.canonicalSymbol

namespace GenusSymbolData

theorem SameSymbol.refl (G : GenusSymbolData) : G.SameSymbol G :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem SameSymbol.symm {G H : GenusSymbolData} (h : G.SameSymbol H) : H.SameSymbol G :=
  ⟨h.n_eq.symm, h.det_eq.symm, h.real_eq.symm, fun p hp hp2 => (h.odd_eq p hp hp2).symm, h.two_eq.symm⟩

theorem SameSymbol.trans {G H K : GenusSymbolData} (h : G.SameSymbol H) (h' : H.SameSymbol K) : G.SameSymbol K :=
  ⟨h.n_eq.trans h'.n_eq, h.det_eq.trans h'.det_eq, h.real_eq.trans h'.real_eq,
    fun p hp hp2 => (h.odd_eq p hp hp2).trans (h'.odd_eq p hp hp2), h.two_eq.trans h'.two_eq⟩

/-- `SameSymbol` is an equivalence relation. -/
@[kb "conwaysloane1999" "Ch. 15, §7.8, p. 384"]
theorem sameSymbol_equivalence : Equivalence SameSymbol :=
  ⟨SameSymbol.refl, SameSymbol.symm, SameSymbol.trans⟩

/-- The setoid of systems of symbols under `SameSymbol`. -/
def sameSymbolSetoid : Setoid GenusSymbolData := ⟨SameSymbol, sameSymbol_equivalence⟩

/-! ### The symbol system of a matrix indexed by `Fin n` -/

/-- **The genus symbol of an integral form** (Conway–Sloane, §7.7–7.8, pp. 382–384): $G$ is a system of symbols of the
symmetric integral matrix $A \in M_n(\mathbb Z)$: $G.n = n$, $G$ is a system of local symbols of $A$
(`IsSymbolsOf`, after the index cast `Fin G.n = Fin n`), and $r + s = n$ for the $(-1)$-adic symbol $+^r-^s$ (which
`IsSymbolsOf` leaves implicit: its real model is fixed by $r$ alone). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7–7.8, pp. 382–384"]
def IsGenusSymbolOf (G : GenusSymbolData) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ h : G.n = n, G.IsSymbolsOf (A.submatrix (Fin.cast h) (Fin.cast h)) ∧ G.real.pos + G.real.neg = G.n

/-- `IsGenusSymbolOf`, unfolded at the index `Fin n`. -/
theorem isGenusSymbolOf_iff (G : GenusSymbolData) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    G.IsGenusSymbolOf A ↔ G.n = n ∧ G.real.pos + G.real.neg = n ∧ Aᵀ = A ∧ A.det = G.det ∧
      CongrIn ℝ (A.map (Int.castRingHom ℝ)) (Matrix.diagonal fun i => ((realVec n G.real.pos i : ℤ) : ℝ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → IsOddSymbolOf p (A.map (Int.castRingHom ℚ_[p])) (G.odd p)) ∧
      IsTwoSymbolOf (A.map (Int.castRingHom ℚ_[2])) G.two := by
  obtain ⟨n', d, r, o, t, N⟩ := G
  constructor
  · rintro ⟨h, hS, hr⟩
    dsimp only at h hr hS ⊢
    subst h
    exact ⟨rfl, hr, hS⟩
  · rintro ⟨h, hr, hS⟩
    dsimp only at h hr hS ⊢
    subst h
    exact ⟨rfl, hS, hr⟩

end GenusSymbolData

open GenusSymbolData

/-! ### Bridges -/

theorem det_map_intCast {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.castRingHom K)).det = (A.det : K) := by
  have e := RingHom.map_det (Int.castRingHom K) A
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, eq_intCast]

/-- For symmetric integral $A$, $B$ and a characteristic-zero domain $K$: the forms $x^{\mathsf T}Ax$, $x^{\mathsf T}Bx$
are GL-equivalent over $K$ iff $A$ and $B$ are congruent over $K$. -/
theorem isometricGL_map_iff {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B) :
    IsometricGL ((LocalDensity.ofMatrixZ A).map (Int.castRingHom K))
      ((LocalDensity.ofMatrixZ B).map (Int.castRingHom K)) ↔
    CongrIn K (A.map (Int.castRingHom K)) (B.map (Int.castRingHom K)) := by
  have e : ∀ C : Matrix (Fin n) (Fin n) ℤ, LocalDensity.ofMatrixZ C = Cassels.Ch8Ex2.gramForm C := fun _ => rfl
  rw [e, e, gramForm_map, gramForm_map,
    isometricGL_gramForm_iff (transpose_map_of_symm _ hA) (transpose_map_of_symm _ hB)]

theorem det_congrIn {K : Type*} [CommRing K] {n : ℕ} {M M' : Matrix (Fin n) (Fin n) K} (h : CongrIn K M M') :
    ∃ c : K, IsUnit c ∧ M'.det = c ^ 2 * M.det := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g.val.det, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, ?_⟩
  rw [det_mul, det_mul, det_transpose]; ring

theorem det_realVec_ne_zero (n r : ℕ) :
    (Matrix.diagonal fun i => ((realVec n r i : ℤ) : ℝ)).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast realVec_ne_zero n r i

/-- A symmetric integral matrix congruent over $\mathbb R$ to a model $\langle 1^r, (-1)^{n-r}\rangle$ is
nondegenerate. -/
theorem det_ne_zero_of_congrIn_realVec {n r : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (h : CongrIn ℝ (A.map (Int.castRingHom ℝ)) (Matrix.diagonal fun i => ((realVec n r i : ℤ) : ℝ))) :
    A.det ≠ 0 := by
  obtain ⟨c, -, hc⟩ := det_congrIn h
  intro h0
  apply det_realVec_ne_zero n r
  rw [hc, det_map_intCast, h0]; simp

/-- $\mathbb Z_p$-equivalent integral matrices have determinants differing by a unit square of $\mathbb Z_p$. -/
theorem det_unit_of_zpEquiv {p : ℕ} [Fact p.Prime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.castRingHom ℚ_[p])) (B.map (Int.castRingHom ℚ_[p]))) :
    ∃ u : ℤ_[p], IsUnit u ∧ ((B.det : ℤ) : ℤ_[p]) = u * A.det := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.val.det ^ 2, ((Matrix.isUnit_iff_isUnit_det _).mp T.isUnit).pow 2, ?_⟩
  have hd := congrArg Matrix.det hT
  rw [det_mul, det_mul, det_transpose, det_map_intCast, det_map_intCast] at hd
  have e := RingHom.map_det PadicInt.Coe.ringHom T.val
  rw [RingHom.mapMatrix_apply] at e
  rw [← e] at hd
  apply Subtype.ext
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_intCast]
  rw [← hd]
  change _ = (PadicInt.Coe.ringHom T.val.det) ^ 2 * _
  ring

/-- **The determinant is a genus invariant** (Cassels, Ch. 9, Lemma 4.1, p. 139; no definiteness assumed): for
nondegenerate symmetric $A$, $B \in M_n(\mathbb Z)$ equivalent over every $\mathbb Z_p$ and congruent over $\mathbb R$,
$\det A = \det B$. -/
@[kb "cassels1978" "Ch. 9, Lemma 4.1, p. 139"]
theorem det_eq_of_local {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hp : ∀ (p : ℕ) [Fact p.Prime], ZpEquiv (A.map (Int.castRingHom ℚ_[p])) (B.map (Int.castRingHom ℚ_[p])))
    (hR : CongrIn ℝ (A.map (Int.castRingHom ℝ)) (B.map (Int.castRingHom ℝ))) : A.det = B.det := by
  have habs : B.det.natAbs = A.det.natAbs := natAbs_eq_of_local hB hA fun p _ => det_unit_of_zpEquiv (hp p)
  obtain ⟨c, hc, hdet⟩ := det_congrIn hR
  rw [det_map_intCast, det_map_intCast] at hdet
  rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
  · exact h.symm
  · exfalso
    rw [h, Int.cast_neg] at hdet
    have hA' : (A.det : ℝ) ≠ 0 := by exact_mod_cast hA
    have : (A.det : ℝ) * (1 + c ^ 2) = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hA' h1
    · nlinarith [sq_nonneg c]

/-! ### Target 2: every nondegenerate form has a symbol system -/

/-- **Every nondegenerate integral form has a genus symbol** (Conway–Sloane, §7.1–7.4, pp. 379–380): a symmetric
$A \in M_n(\mathbb Z)$ with $\det A \ne 0$ has a system of symbols: Sylvester's normal form over $\mathbb R$
(`exists_congrIn_realVec`), the $p$-adic symbol at every odd prime (`exists_isOddSymbolOf`, Thm. 9) and a 2-adic symbol
(`TwoAdic.exists_isTwoSymbolOf`, §7.4). The support bound is taken to be $0$ (it plays no role in the symbol). -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.4, pp. 379–380"]
theorem exists_isGenusSymbolOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (hdet : A.det ≠ 0) :
    ∃ G : GenusSymbolData, G.IsGenusSymbolOf A := by
  classical
  obtain ⟨r, hr, hR⟩ := exists_congrIn_realVec (A.map (Int.castRingHom ℝ)) (transpose_map_of_symm _ hA)
    (by rw [det_map_intCast]; exact_mod_cast hdet)
  have hodd : ∀ p : ℕ, ∃ σ : OddSymbol,
      ∀ [Fact p.Prime], p ≠ 2 → IsOddSymbolOf p (A.map (Int.castRingHom ℚ_[p])) σ := by
    intro p
    by_cases hp : p.Prime ∧ p ≠ 2
    · have : Fact p.Prime := ⟨hp.1⟩
      obtain ⟨σ, hσ⟩ := exists_isOddSymbolOf hp.2 (transpose_map_of_symm _ hA) (Mass.det_map_ne hdet)
        (Mass.isClassIntegral_map A)
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨fun _ => OddFactor.trivial, fun hp2 => absurd ⟨Fact.out, hp2⟩ hp⟩
  choose odd hodd using hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ⟩ := TwoAdic.exists_isTwoSymbolOf (A.map (Int.castRingHom ℚ_[2])) (transpose_map_of_symm _ hA)
    (Mass.det_map_ne hdet) (Mass.isClassIntegral_map A)
  refine ⟨⟨n, A.det, ⟨r, n - r⟩, odd, τ, 0⟩, (isGenusSymbolOf_iff _ A).2
    ⟨rfl, by dsimp only; omega, hA, rfl, hR, fun p _ hp2 => hodd p hp2, hτ⟩⟩

/-! ### Target 3: the main theorem -/

/-- **Genus ↔ genus symbol** (Conway–Sloane, Ch. 15, §7: Thm. 9, p. 379; Thm. 10 and §7.6, pp. 381–382; §7.8,
p. 384, made explicit): for symmetric $A$, $B \in M_n(\mathbb Z)$ with systems of symbols $G$, $H$
(`IsGenusSymbolOf`; they are nondegenerate, and every nondegenerate matrix has one, `exists_isGenusSymbolOf`), the forms
$x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are in the same genus iff $G$ and $H$ are the same genus symbol: the same
dimension, determinant and $(-1)$-adic symbol, the same $p$-adic symbol at every odd prime, and the same canonical
2-adic symbol.

The book does not state this as one theorem: it gives the local classifications (Thms. 9, 10, §7.6) and in §7.8 uses
the genus symbol as a name of the genus. *Proof:* at odd $p$, Theorem 9 (`theorem9`); at $2$, Theorem 10 with §7.6
(`TwoAdic.zpEquiv_iff_canonical_eq`); at $\infty$, Sylvester's law (`eq_of_congrIn_realVec`); the determinant from the
local equivalences (`det_eq_of_local`). Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §7.8, p. 384 (with Thms. 9, 10 and §7.6, pp. 379–382), made explicit"]
theorem sameGenus_iff_sameSymbol {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} {G H : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) (hH : H.IsGenusSymbolOf B) :
    SameGenus (LocalDensity.ofMatrixZ A) (LocalDensity.ofMatrixZ B) ↔ G.SameSymbol H := by
  obtain ⟨hGn, hGr, hAs, hAd, hAR, hAo, hAt⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨hHn, hHr, hBs, hBd, hBR, hBo, hBt⟩ := (H.isGenusSymbolOf_iff B).1 hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2G := eventuallyTypeII_of_isTwoSymbolOf hAt
  have h2H := eventuallyTypeII_of_isTwoSymbolOf hBt
  constructor
  · rintro ⟨hp, hR⟩
    have hZ : ∀ (p : ℕ) [Fact p.Prime],
        ZpEquiv (A.map (Int.castRingHom ℚ_[p])) (B.map (Int.castRingHom ℚ_[p])) :=
      fun p _ => (Mass.isometricGL_padic_iff hAs hBs).1 (hp p)
    have hCR := (isometricGL_map_iff hAs hBs).1 hR
    have hpos : G.real.pos = H.real.pos :=
      eq_of_congrIn_realVec (by omega) (by omega) (hAR.symm.trans (hCR.trans hBR))
    refine ⟨hGn.trans hHn.symm, ?_, RealSymbol.ext' hpos (by omega), fun p hp hp2 => ?_, ?_⟩
    · rw [← hAd, ← hBd]
      exact det_eq_of_local (det_ne_zero_of_congrIn_realVec hAR) (det_ne_zero_of_congrIn_realVec hBR) hZ hCR
    · have : Fact p.Prime := ⟨hp⟩
      exact oddSymbol_eq_of_zpEquiv hp2 (hZ p) (hAo p hp2) (hBo p hp2)
    · rw [TwoSymbol.canonicalSymbol_eq h2G, TwoSymbol.canonicalSymbol_eq h2H]
      exact (TwoAdic.zpEquiv_iff_canonical_eq hAt hBt h2G h2H).1 (hZ 2)
  · intro hS
    refine ⟨fun p _ => (Mass.isometricGL_padic_iff hAs hBs).2 ?_, (isometricGL_map_iff hAs hBs).2 ?_⟩
    · by_cases hp2 : p = 2
      · subst hp2
        refine (TwoAdic.zpEquiv_iff_canonical_eq hAt hBt h2G h2H).2 ?_
        rw [← TwoSymbol.canonicalSymbol_eq h2G, ← TwoSymbol.canonicalSymbol_eq h2H]
        exact hS.two_eq
      · refine zpEquiv_of_oddSymbol_eq hp2 (hAo p hp2) ?_
        rw [hS.odd_eq p Fact.out hp2]
        exact hBo p hp2
    · refine hAR.trans ?_
      rw [hS.real_eq]
      exact hBR.symm

end QuadFormsKB.ConwaySloane
