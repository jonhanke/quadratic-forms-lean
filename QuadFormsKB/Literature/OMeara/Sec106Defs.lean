/-
# O'Meara §106: definitions for unimodular lattices over $\mathbb Z$

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with a form `Q : QuadForm ℚ n`, lattices `Lat ℚ n` (finitely generated
$\mathcal O_{\mathbb Q}$-submodules spanning $V$; $\mathcal O_{\mathbb Q} = \mathbb Z$). O'Meara's bilinear form is
$B(x, y) = \tfrac12\bigl(Q(x + y) - Q(x) - Q(y)\bigr) = \tfrac12$ `bil Q x y`, so that $B(x, x) = Q(x)$.

**Defines** (O'Meara 1973, §82F and §106, pp. 324–325)
* `omearaDual Q L` $= L^\# = \{x \in V : B(x, L) \subseteq \mathbb Z\}$ (the dual of §82F, p. 230, with O'Meara's $B$);
* `IsUnimodularZ Q L`: $L$ is unimodular, $L^\# = L$ (82:14b: unimodular means $L^\# = L$);
* `IsEvenLat Q L` (106.r3): $Q(L) \subseteq 2\mathbb Z$; a unimodular $L$ is *even* if `IsEvenLat`, *odd* otherwise
  (O'Meara: $\mathfrak nL = 2\mathbb Z$, respectively $\mathfrak nL = \mathbb Z$);
* `IsCompletelyDecomposable Q L` (106.r2): $L$ is an orthogonal sum of lattices of dimension $1$;
* `omearaG Q L` (106.r4): the set $\mathcal G(L)$ of unimodular lattices $K$ on $V$ with $K_p = L_p$ for every odd
  prime $p$.

The claims that come with these definitions in the book (for unimodular $L$, $2\mathbb Z \subseteq \mathfrak nL
\subseteq \mathbb Z$; $L$ is even if and only if $L_2$ is even; the matrix of a completely decomposable unimodular
lattice on $I_n$ is $I_n$) are not formalized.
-/
import QuadFormsKB.Literature.OMeara.Sec105

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ} (Q : QuadForm ℚ n)

/-- **The dual lattice** $L^\# = \{x \in V : B(x, L) \subseteq \mathbb Z\}$ with O'Meara's bilinear form
$B = \tfrac12$ `bil Q` (O'Meara 1973, §82F, p. 230). -/
@[kb "omeara1963" "§82F, p. 230 (the dual L#, with B(x,x) = Q(x))"]
def omearaDual (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Submodule (𝓞 ℚ) (Fin n → ℚ) where
  carrier := {x | ∀ y ∈ L, ∃ m : ℤ, bil Q x y / 2 = m}
  add_mem' {x x'} hx hx' y hy := by
    obtain ⟨m, hm⟩ := hx y hy
    obtain ⟨m', hm'⟩ := hx' y hy
    refine ⟨m + m', ?_⟩
    have e : bil Q (x + x') y = bil Q x y + bil Q x' y := by simp [bil, add_dotProduct]
    rw [e, add_div, hm, hm']; push_cast; ring
  zero_mem' y _ := ⟨0, by simp [bil]⟩
  smul_mem' c x hx y hy := by
    obtain ⟨m, hm⟩ := hx y hy
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
      ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩
    subst hk
    refine ⟨k * m, ?_⟩
    have e : (((k : ℤ) : 𝓞 ℚ) • x) = (k : ℚ) • x := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    have e2 : bil Q ((k : ℚ) • x) y = (k : ℚ) * bil Q x y := by simp [bil, smul_dotProduct]
    rw [e, e2, mul_div_assoc, hm]; push_cast; ring

/-- **A unimodular lattice** over $\mathbb Z$: $L^\# = L$ (O'Meara 1973, 82:14b, p. 232; used throughout §106). -/
@[kb "omeara1963" "§82G, 82:14b, p. 232 (unimodular iff L# = L); §106, p. 324"]
def IsUnimodularZ (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Prop := omearaDual Q L = L

/-- **An even lattice** (O'Meara 1973, §106A, p. 324): $Q(L) \subseteq 2\mathbb Z$. A unimodular lattice is *odd* when it
is not even. -/
@[kb "omeara1963" "§106A, p. 324 (even and odd unimodular lattices: L is even iff Q(L) ⊆ 2Z)"]
def IsEvenLat (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Prop := ∀ x ∈ L, ∃ m : ℤ, Q.eval x = 2 * m

/-- **A completely decomposable lattice** (O'Meara 1973, §106, p. 324): an orthogonal sum of lattices of dimension
$1$ (an orthogonal splitting, `IsOrthSplitting`, whose components span lines). -/
@[kb "omeara1963" "§106, p. 324 (completely decomposable lattice)"]
def IsCompletelyDecomposable (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Prop :=
  ∃ S : Finset (Submodule (𝓞 ℚ) (Fin n → ℚ)), IsOrthSplitting Q L S ∧
    ∀ K ∈ S, Module.finrank ℚ (Submodule.span ℚ (K : Set (Fin n → ℚ))) = 1

/-- **The set $\mathcal G(L)$** (O'Meara 1973, §106B, p. 325): the unimodular lattices $K$ on $V$ with $K_p = L_p$
for every odd prime $p$ (the finite spots $\mathfrak p$ of $\mathbb Q$ with $2 \notin \mathfrak p$). -/
@[kb "omeara1963" "§106B, p. 325 (the set G(L))"]
def omearaG (L : Lat ℚ n) : Set (Lat ℚ n) :=
  {K | IsUnimodularZ Q K.1 ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → loc v K.1 = loc v L.1}

end QuadFormsKB.Lattices
