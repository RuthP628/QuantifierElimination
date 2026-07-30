import Mathlib
import BachelorThesis.SeparatingTypes

set_option linter.style.header false
set_option linter.unusedVariables false

open FirstOrder Language Formula

universe u v w w'
variable {α : Type*}

namespace FirstOrder
namespace Language
namespace Formula


/-- A formula `φ` is quantifier-free if it is obtained from a quantifier-free bounded formula. -/
def IsQF {L : Language} (φ : L.Formula α) : Prop :=
  BoundedFormula.IsQF (φ : L.BoundedFormula α 0)

end Formula

namespace Theory

/-- A theory `T` has quantifier-elimination if in every model of it,
every L-formula is equivalent to a quantifier-free L-formula. -/
def HasQE {L : Language} (T : L.Theory) : Prop :=
  ∀ (α : Type*) (_ : DecidableEq α) (φ : L.Formula α),
  ∃ ψ : L.Formula α, (ψ.IsQF ∧ T ⊨ᵇ (φ.iff ψ))

end Theory

variable {L : Language.{u, v}} (M : Type w) (N : Type w')
variable [L.Structure M] [L.Structure N]

/-- A partial isomorphism between two `L`-structures `M` and `N` is a bijective map between
subsets `A ⊆ M`, `B ⊆ N` that commutes with interpretation of function and relation symbols. -/
structure PartialIso extends (_root_.PartialEquiv M N) where
  /-- A partial isomorphism commutes with interpretation of functions -/
  map_fun' : ∀ {n}, ∀ (f : L.Functions n), ∀ (a : Fin n → M), ∀ (m : M),
    ((∀ x, a x ∈ source) ∧ m ∈ source) →
      (Structure.funMap f a = m ↔ Structure.funMap f (toFun ∘ a) = toFun m)
  /-- A partial isomorphism commutes with interpretation of relations -/
  map_rel' : ∀ {n}, ∀ (r : L.Relations n), ∀ (a : Fin n → M),
    (∀ x, a x ∈ source) → (Structure.RelMap r a ↔ Structure.RelMap r (toFun ∘ a))

namespace PartialIso

/-- For two partial isomorphisms `f` and `g`,
we write `f ≤ g` if `g` extends `f`. -/
instance : LE (L.PartialIso M N) :=
  ⟨ fun f g ↦ (f.source ⊆ g.source ∧ (∀ x ∈ f.source, f.toFun x = g.toFun x))⟩

theorem le_def (f g : L.PartialIso M N) : f ≤ g ↔
  (f.source ⊆ g.source ∧ (∀ x ∈ f.source, f.toFun x = g.toFun x)) :=
  Iff.rfl

/-- If `f` and `g` are two partial isomorphisms with `f ≤ g`,
the domain of `f` is a subset of the domain of `g`. -/
theorem dom_le_dom {f g : L.PartialIso M N} : f ≤ g → f.source ⊆ g.source := fun ⟨le, _⟩ ↦ le

/-- If `f` and `g` are two partial isomorphisms with `f ≤ g`,
the codomain of `f` is a subset of the codomain of `g`. -/
theorem cod_le_cod {f g : L.PartialIso M N} : f ≤ g → f.target ⊆ g.target := by
  intro hfg x hx
  apply (le_def M N f g).1 at hfg
  let y := f.invFun x
  obtain ⟨ hfg₁, hfg₂ ⟩ := hfg
  have hy : y ∈ f.source := f.map_target' hx
  specialize hfg₂ y hy
  have hx : f.toFun y = x := f.right_inv' hx
  rw [hx] at hfg₂
  have hy' : y ∈ g.source := Set.mem_preimage.mp (hfg₁ hy)
  rw [hfg₂]
  exact PartialEquiv.map_source g.toPartialEquiv (hfg₁ hy)

/-- If `f`, `g` and `h` are partial isomorphisms s.t. `g` extends `f`
and `h` extends `g`, then `h` extends `f`. -/
theorem le_trans (f g h : L.PartialIso M N) : f ≤ g → g ≤ h → f ≤ h := by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  intro x hx
  specialize eq_fg x; specialize eq_gh x
  have hx' : x ∈ g.source := Set.mem_of_subset_of_mem le_fg hx
  apply eq_fg at hx
  apply eq_gh at hx'
  rw [hx]
  exact hx'

/-- Every partial isomorphism is an extension of itself. -/
theorem le_refl (f : L.PartialIso M N) : f ≤ f := ⟨le_rfl, by norm_num⟩

end PartialIso

/-- A back-and-forth-system is a set of partial isomorphisms between two structures `M` and `N`
such that for every partial isomorphism contained in it, its domain resp. codomain can be
extended by other elements of the system to include any element of `M` resp. `N`. -/
def IsBackAndForthSystem (F : Set (L.PartialIso M N)) : Prop :=
  (∀ f ∈ F, ∀ (m : M), ∃ g ∈ F, m ∈ g.source ∧ f ≤ g) ∧
  (∀ f ∈ F, ∀ (n : N), ∃ g ∈ F, n ∈ g.target ∧ f ≤ g)

namespace BackAndForth

/-- The domain of any element of a back-and-forth-system `F` between `M` and `N`
can be extended to include any finite number of elements of `M`. -/
lemma back_extends_finite (F : Set (L.PartialIso M N)) (n : ℕ) :
  (L.IsBackAndForthSystem M N F) →
  ∀ f ∈ F, ∀ (v : Fin n → M), ∃ g ∈ F, (∀ (a : Fin n), v a ∈ g.source) ∧ f ≤ g := by {
    intro hF
    unfold IsBackAndForthSystem at hF
    obtain ⟨ back, forth ⟩ := hF
    -- We show the statement by induction over the number of elements `n`
    -- to which we want to extend the domain.
    induction n with
    | zero =>
      -- If `n = 0`, the statement is trivial.
      simp only [IsEmpty.forall_iff, true_and, forall_const]
      intro f hf
      use f
      constructor
      · exact hf
      · exact PartialIso.le_refl M N f
    | succ =>
      -- Suppose that for all `f ∈ F` and all `v : Fin n → M`, we can find
      -- an `f' ∈ F` extending `f` such that all `v(i)` are in the domain of `f'`.
      rename_i n ih
      -- Now, let `f ∈ F` and `v : Fin (n + 1) → M`.
      -- We want to show that there is an `f' ∈ F` extending `f` s.t. for all `0 ≤ i ≤ n`,
      -- `v(i)` is in the domain of `f'`.
      intro f hf v
      let v' : Fin n → M := fun x ↦ v ⟨ x, by norm_num ⟩
      -- By the IH, there is `g ∈ F` extending `f` s.t. for all `0 ≤ i ≤ n-1`,
      -- `v(i)` is in the domain of `g`.
      specialize ih f hf v'
      obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := ih
      -- Moreover, by `back`, there is `g' ∈ F` extending `g` s.t. `v(n)` is in the domain of `g'`
      let hg₄ := back g hg₁ (v ⟨ n, by norm_num ⟩ )
      obtain ⟨ g', hg'₁, hg'₂, hg'₃ ⟩ := hg₄
      -- Then, one can easily see that `g'` has the desired property.
      use g'
      constructor
      · assumption
      · constructor
        · intro a
          by_cases ha : a = ⟨ n, by norm_num ⟩
          · rw [ha]
            assumption
          · have ha' : a < n := Fin.val_lt_last ha
            specialize hg₂ ⟨ a, ha' ⟩
            unfold v' at hg₂
            simp only [Fin.eta] at hg₂
            apply PartialIso.dom_le_dom at hg'₃
            exact Set.mem_preimage.mp (hg'₃ hg₂)
        · exact PartialIso.le_trans  M N f g g' hg₃ hg'₃
  }

/-- The codomain of any element of a back-and-forth-system `F` between `M` and `N`
can be extended to include any finite number of elements of `N`. -/
lemma forth_extends_finite (F : Set (L.PartialIso M N)) (n : ℕ) :
  (L.IsBackAndForthSystem M N F) →
  (∀ f ∈ F, ∀ (v : Fin n → N), ∃ g ∈ F, (∀ (a : Fin n), v a ∈ g.target) ∧ f ≤ g) := by {
    intro hF
    unfold IsBackAndForthSystem at hF
    obtain ⟨ back, forth ⟩ := hF
    -- We show the statement by induction over the number of elements `n`
    -- to which we want to extend the codomain.
    induction n with
    | zero =>
      -- If `n = 0`, the statement is trivial.
      simp only [IsEmpty.forall_iff, true_and, forall_const]
      intro f hf
      use f
      constructor
      · exact hf
      · exact PartialIso.le_refl M N f
    | succ =>
      -- Suppose that for all `f ∈ F` and all `v : Fin n → N`, we can find
      -- an `f' ∈ F` extending `f` such that all `v(i)` are in the domain of `f'`.
      rename_i n ih
      -- Now, let `f ∈ F` and `v : Fin (n + 1) → N`.
      -- We want to show that there is an `f' ∈ F` extending `f` s.t. for all `0 ≤ i ≤ n`,
      -- `v(i)` is in the codomain of `f'`.
      intro f hf v
      let v' : Fin n → N := fun x ↦ v ⟨ x, by norm_num ⟩
      -- By the IH, there is `g ∈ F` extending `f` s.t. for all `0 ≤ i ≤ n-1`,
      -- `v(i)` is in the domain of `g`.
      specialize ih f hf v'
      obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := ih
      -- Moreover, by `forth`, there is `g' ∈ F` extending `g`
      -- s.t. `v(n)` is in the codomain of `g'`
      let hg₄ := forth g hg₁ (v ⟨ n, by norm_num ⟩ )
      obtain ⟨ g', hg'₁, hg'₂, hg'₃ ⟩ := hg₄
      -- Then, one can easily see that `g'` has the desired property.
      use g'
      constructor
      · assumption
      · constructor
        · intro a
          by_cases ha : a = ⟨ n, by norm_num ⟩
          · rw [ha]
            exact hg'₂
          · have ha' : a < n := Fin.val_lt_last ha
            specialize hg₂ ⟨ a, ha'⟩
            unfold v' at hg₂
            simp only [Fin.eta] at hg₂
            apply PartialIso.cod_le_cod at hg'₃
            specialize hg'₃ hg₂
            assumption
        · exact PartialIso.le_trans M N f g g' hg₃ hg'₃
  }

/-- Partial isomorphisms in a back-and-forth-system commute with interpretations of terms. -/
lemma on_term (F : Set (L.PartialIso M N)) (hF : L.IsBackAndForthSystem M N F) (t : L.Term α) :
  ∀ (v : α → M) (ι : L.PartialIso M N) (hι : ι ∈ F) (hv₁ : ∀ x, v x ∈ ι.source)
  (hv₂ : t.realize v ∈ ι.source) (m : M) (hm : m ∈ ι.source),
  t.realize v = m ↔ t.realize (ι.toFun ∘ v) = ι.toFun m := by
  -- We show the statement via induction on terms.
  induction t with
  | var =>
    -- Suppose `t` is a variable symbol.
    intros
    rename_i a v ι hι hv₁ hv₂ m hm
    constructor
    · -- Then, the only-if-part is trivial.
      simp_all only [Term.realize_var, Function.comp_apply, implies_true]
    · -- For the if-part, note that `t.realize (ι.toFun ∘ v) = ι.toFun m` simplifies to
      -- `∀ x, ι.toFun (v x) = ι.toFun (m)`.
      intro h
      simp_all only [Term.realize_var, Function.comp_apply]
      -- Since `ι` is a partial isomorphism, `ι.toFun` is bijective, which proves the goal.
      calc
      v a = ι.invFun (ι.toFun (v a) ) := Eq.symm (ι.left_inv' (hv₁ a))
      _ = ι.invFun (ι.toFun m) := by rw [h]
      _ = m := ι.left_inv' hm
  | func =>
    -- Now, suppose `t` is of the form `f(ts(0), ..., ts(n-1))` for a function symbol `f ∈ L`
    -- and terms `ts(0)`, ..., `ts(n-1)` satisfying the statement.
    -- Then, suppose `t.realize v = m`.
    simp only [Term.realize_func]
    intros
    rename_i l f ts ih v ι hι hv₁ hv₂ m hm
    -- Then, note that there is an extension `ι' ∈ F` such that `(ts(i)).realize v` is in the
    -- domain of `ι'` for all `0 ≤ i ≤ n-1`.
    have hι' := back_extends_finite M N F l hF ι hι (fun i ↦ ((ts i).realize v))
    obtain ⟨ ι', hι'₁, hι'₂, hι'₃ ⟩ := hι'
    apply (PartialIso.le_def M N ι ι').1 at hι'₃
    obtain ⟨ hι'₃, hι'₄ ⟩ := hι'₃
    -- Since `ι'` is a partial isomorphism, it commutes with `f`.
    have hι'₅ := ι'.map_fun' f (fun i ↦ ((ts i).realize v)) m
      ⟨ hι'₂, Set.mem_of_subset_of_mem hι'₃ hm ⟩
    have hv₁' : ∀ x, v x ∈ ι'.source := by tauto
    have hm' : m ∈ ι'.source := Set.mem_of_subset_of_mem hι'₃ hm
    have ih' := fun i ↦ ih i v ι' hι'₁ hv₁' (hι'₂ i) ((ts i).realize v) (hι'₂ i)
    simp only [true_iff] at ih'
    -- By the induction hypothesis, `ι'` commutes with the interpretation of all `ts(i)`.
    have ih'' : (ι'.toFun ∘ (fun i ↦ ((ts i).realize v)))
      = (fun i ↦ ((ts i).realize (ι'.toFun ∘ v))) := by
        ext i
        exact
          (Eq.to_iff
              (congrArg (Eq ((↑ι'.toPartialEquiv ∘ fun i ↦ Term.realize v (ts i)) i)) (ih' i))).mpr
            rfl
    -- Since `ι'` extends `ι`, `ι'(v(x)) = ι(v(x))` for all `x ∈ α`.
    have hι'₆ : ι'.toFun ∘ v = ι.toFun ∘ v := by
      ext x
      simp_all only [Function.comp_apply]
    -- Moreover, `ι'(m) = ι(m)` since `ι'` extends `ι`.
    have hι'₇ : ι'.toFun m = ι.toFun m := by simp_all only
    constructor
    · -- Suppose `t.realize v = m`.
      intro h
      -- Then, the arguments above show that `t.realize (ι.toFun ∘ v) = ι.toFun m`,
      -- which is what we wanted to show.
      apply hι'₅.1 at h
      rw [ih''] at h
      rw [← hι'₆]
      rw [← hι'₇]
      assumption
    · -- Suppose `t.realize (ι.toFun ∘ v) = ι.toFun m`.
      intro h
      -- Then, by the arguments above, `t.realize v = m` holds only if
      -- `t.realize (ι.toFun ∘ v) = ι.toFun m`, which is what we wanted to show.
      apply hι'₅.2
      rw [ih'']
      rw [hι'₆]
      rw [hι'₇]
      assumption


/-- Partial isomorphisms in a back-and-forth-system
commute with interpretations of bounded formulas. -/
theorem on_boundedFormula {n : ℕ} (F : Set (L.PartialIso M N)) (hF : L.IsBackAndForthSystem M N F)
  (φ : L.BoundedFormula α n) :
  ∀ (v : α → M) (xs : Fin n → M) (ι : L.PartialIso M N) (hι : ι ∈ F) (hv : ∀ x, v x ∈ ι.source)
  (hxs : ∀ x, xs x ∈ ι.source),
  φ.Realize v xs ↔ φ.Realize (ι.toFun ∘ v) (ι.toFun ∘ xs) := by
    -- We show the statement by induction over formulas.
    induction φ with
    | falsum =>
      -- If `φ` is `⊥`, the statement is clear.
      intro v xs ι hι hv hxs
      exact Eq.to_iff rfl
    | equal =>
      -- Suppose `φ` is of the form `t₁ = t₂` for two `L`-terms `t₁, t₂`.
      intros
      rename_i l t₁ t₂ v xs ι hι hv hxs
      have hvxs : ∀ x, (Sum.elim v xs) x ∈ ι.source := by
        simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]
        exact ⟨ hv, hxs ⟩
      -- Then, there is `ι' ∈ F` extending `ι` s.t. `t₁^M(v, xs)` is in the domain of `ι'`.
      have hι' := hF.1 ι hι (t₁.realize (Sum.elim v xs))
      obtain ⟨ ι', hι'₁, hι'₂, hι'₃ ⟩ := hι'
      -- Moreover, there is `ι'' ∈ F` extending `ι'`s.t. `t₂^M(v, xs)` is in the domain  of `ι''`.
      have hι'' := hF.1 ι' hι'₁ (t₂.realize (Sum.elim v xs))
      obtain ⟨ ι'', hι''₁, hι''₂, hι''₃ ⟩ := hι''
      have hι''₄ : t₁.realize (Sum.elim v xs) ∈ ι''.source := by
        have h := (PartialIso.dom_le_dom M N hι''₃)
        exact Set.mem_preimage.mp (h hι'₂)
      -- Then, `ι''` extends `ι`.
      have hι''₅ : ι ≤ ι'' := PartialIso.le_trans M N ι ι' ι'' hι'₃ hι''₃
      apply (PartialIso.le_def M N ι ι'').1 at hι''₅
      obtain ⟨ hι''₅, hι''₆ ⟩ := hι''₅
      have hι''₇ : ∀ x, (Sum.elim v xs) x ∈ ι''.source := by
        intro x
        exact Set.mem_preimage.mp (hι''₅ (hvxs x))
      -- By the previous lemma, `ι''` commutes with interpretation of terms.
      -- Hence, for all `m ∈ M`, ``t₁^M(v, xs) = m ↔ t₁^N(ι ∘ v, ι ∘ xs)`
      have hι''₈ := on_term M N F hF t₁ (Sum.elim v xs)
        ι'' hι''₁ hι''₇ hι''₄ (t₂.realize (Sum.elim v xs)) hι''₂
      -- Moreover, for all `m ∈ M`, `t₂^M(v, xs) = m ↔ t₂^N(ι ∘ v, ι ∘ xs)`
      have hι''₉ := on_term M N F hF t₂ (Sum.elim v xs)
        ι'' hι''₁ hι''₇ hι''₂ (t₂.realize (Sum.elim v xs)) hι''₂
      simp only [true_iff] at hι''₉
      have hι''₁₀ : ι''.toFun ∘ (Sum.elim v xs) = Sum.elim (ι''.toFun ∘ v) (ι''.toFun ∘ xs) := by
        ext x
        simp only [Function.comp_apply]
        grind
      have hι''₁₁ : ι''.toFun ∘ v = ι.toFun ∘ v := by
        ext x
        simp_all
      have hι''₁₂ : ι''.toFun ∘ xs = ι.toFun ∘ xs := by
        ext x
        simp_all
      rw [hι''₁₁] at hι''₁₀
      rw [hι''₁₂] at hι''₁₀
      constructor
      · -- Suppose `M ⊨ φ(v,xs)`.
        intro ht₁t₂
        -- This means `t₁^M(v, xs) = t₂^M(v, xs)`.
        apply (BoundedFormula.realize_bdEqual t₁ t₂).1 at ht₁t₂
        -- Moreover, the goal is equivalent to `t₁^N(ι ∘ v, ι ∘ xs) = t₂^N(ι ∘ v, ι ∘ xs)`
        apply (BoundedFormula.realize_bdEqual t₁ t₂).2
        -- Since `ι` commutes with interpretation of terms, we are done.
        apply hι''₈.1 at ht₁t₂
        rw [← hι''₉] at ht₁t₂
        rw [hι''₁₀] at ht₁t₂
        assumption
      · -- Suppose `N ⊨ φ(ι ∘ v, ι ∘ xs)`.
        intro ht₁t₂
        -- This means `t₁^N(ι ∘ v, ι ∘ xs) = t₂^N (ι ∘ v, ι ∘ xs)`.
        apply (BoundedFormula.realize_bdEqual t₁ t₂).2 at ht₁t₂
        -- Moreover, the goal is equivalent to `t₁^M(v, xs) = t₂^M(v, xs)`
        apply (BoundedFormula.realize_bdEqual t₁ t₂).1
        -- Since `ι` commutes with interpretation of terms, we are done.
        apply hι''₈.2
        rw [← hι''₉]
        rw [hι''₁₀]
        assumption
    | rel =>
      -- Suppose `t` is of the form `R(ts(0), ..., ts(l-1))`
      -- and `ts(0)`, ..., `ts(l-1)` are `L`-terms.
      intros
      rename_i n l R ts v xs ι hι hv hxs
      have hvxs : ∀ x, (Sum.elim v xs) x ∈ ι.source := by
        simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]
        exact ⟨ hv, hxs ⟩
      -- Then, there exists `ι' ∈ F` extending `ι`s.t. `(ts i)^M(v,xs)`
      -- is in the domain of `ι'` for all `0 ≤ i ≤ l-1`.
      have hι' := back_extends_finite M N F l hF ι hι (fun i ↦ (ts i).realize (Sum.elim v xs))
      obtain ⟨ ι', hι'₁, hι'₂, hι'₃ ⟩ := hι'
      -- Since `ι'` is a partial isomorphism, it commutes with interpretation of `R`...
      have hι'₄ := ι'.map_rel' R (fun i ↦ (ts i).realize (Sum.elim v xs)) hι'₂
      have hvxs' : ∀ x, (Sum.elim v xs) x ∈ ι'.source := by
        intro x
        apply (PartialIso.le_def M N ι ι').1 at hι'₃
        obtain ⟨ hι'₃, hι'₅ ⟩ := hι'₃
        exact Set.mem_preimage.mp (hι'₃ (hvxs x))
      -- and interpretation of the terms `ts i` for all `0 ≤ i ≤ l-1`.
      have hι'₅ := fun i ↦ on_term M N F hF (ts i) (Sum.elim v xs) ι' hι'₁ hvxs' (hι'₂ i)
        ((ts i).realize (Sum.elim v xs )) (hι'₂ i)
      simp only [true_iff] at hι'₅
      have hι'₆ : (ι'.toFun ∘ fun i ↦ Term.realize (Sum.elim v xs) (ts i))
        = (fun i ↦ Term.realize (ι'.toPartialEquiv ∘ Sum.elim v xs) (ts i)) := by
          ext i
          simp_all
      have hι'₇ : (ι'.toFun ∘ Sum.elim v xs) = Sum.elim (ι'.toFun ∘ v) (ι'.toFun ∘ xs) := by
        ext x
        grind
      have hι'₈ : (ι'.toFun ∘ v) = (ι.toFun ∘ v) := by
        apply (PartialIso.le_def M N ι ι').1 at hι'₃
        obtain ⟨ h₁, h₂ ⟩ := hι'₃
        grind
      have hι'₉ : (ι'.toFun ∘ xs) = (ι.toFun ∘ xs) := by
        apply (PartialIso.le_def M N ι ι').1 at hι'₃
        obtain ⟨ h₁, h₂ ⟩ := hι'₃
        grind
      rw [hι'₈] at hι'₇
      rw [hι'₉] at hι'₇
      constructor
      · -- Now, suppose `M ⊨ φ(v, xs)`.
        intro h
        -- This means `R^M(ts(0)^M(v, xs), ..., ts(l-1)^M(v,xs))` holds.
        apply BoundedFormula.realize_rel.2
        -- We want to show `R^N(ts(0)^N(ι ∘ v, ι ∘ xs), ..., ts(l-1)^N(ι ∘ v, ι ∘ xs))` holds
        apply BoundedFormula.realize_rel.1 at h
        -- Since `ι'` extends `ι` and `ι'` commutes with interpretation
        -- of `R` and `ts(i)` for all `0 ≤ i ≤ l-1`, we are done.
        apply hι'₄.1 at h
        rw [hι'₆] at h
        rw [hι'₇] at h
        assumption
      · -- On the other hand, suppose `N ⊨ φ(ι ∘ v, ι ∘ xs)`
        intro h
        -- This means `R^N(ts(0)^N(ι ∘ v, ι ∘ xs), ..., ts(l-1)^N(ι ∘ v, ι ∘ xs))`
        apply BoundedFormula.realize_rel.1
        -- We want to prove `R^M(ts(0)^M(v, xs), ..., ts(l-1)^M(v,xs))`
        apply BoundedFormula.realize_rel.2 at h
        -- Since `ι'` extends `ι`and `ι'`commutes with interpretation
        -- of `R` and `ts(i)` for all `0 ≤ i ≤ l-1`, we are done.
        apply hι'₄.2
        rw [hι'₆]
        rw [hι'₇]
        assumption
    | imp =>
      -- Now, suppose `φ` is of the form `φ₁ → φ₂` and the statement holds for both `φ₁` and `φ₂`.
      intros
      rename_i n φ₁ φ₂ ih₁ ih₂ v xs ι hι hv hxs
      specialize ih₁ v xs ι hι hv hxs
      specialize ih₂ v xs ι hι hv hxs
      constructor
      · -- Suppose `M ⊨ φ(v, xs)`.
        intro h
        -- Then, we know that `M ⊨ φ₁(v, xs)` implies `M ⊨ φ₂(v,xs)`.
        apply BoundedFormula.realize_imp.1 at h
        -- We want to prove that `N ⊨ φ₁(ι ∘ v, ι ∘ xs)`
        -- implies `N ⊨ φ₂(ι ∘ v, ι ∘ xs)`.
        apply BoundedFormula.realize_imp.2
        -- Suppose `N ⊨ φ₁(ι ∘ v, ι ∘ xs)`
        intro h'
        -- By the induction hypothesis, this means `M ⊨ φ₁(v, xs)`
        apply ih₁.2 at h'
        -- Therefore `M ⊨ φ₂(v, xs)`,
        apply h at h'
        -- hence `N ⊨ φ₂(ι ∘ v, ι ∘ xs)` by induction hypothesis.
        apply ih₂.1
        assumption
      · -- Suppose `N ⊨ φ(ι ∘ v, ι ∘ xs)`.
        intro h
        -- Hence, `N ⊨ φ₁(ι ∘ v, ι ∘ xs)` implies `N ⊨ φ₂(ι ∘ v, ι ∘ xs)`
        apply BoundedFormula.realize_imp.1 at h
        -- We want to show `M ⊨ φ₁(v, xs)` implies `M ⊨ φ₂(v, xs)`
        apply BoundedFormula.realize_imp.2
        -- Suppose `M ⊨ φ₁(v, xs)`.
        intro h'
        -- Then, by induction hypothesis, this means `N ⊨ φ₁(ι ∘ v, ι ∘ xs)`
        apply ih₁.1 at h'
        -- Hence, `N ⊨ φ₂(ι ∘ v, ι ∘ xs)`
        apply h at h'
        -- We can conclude the proof by induction hypothesis.
        apply ih₂.2
        assumption
    | all =>
      -- Suppose `φ` is of the form `∀ x, φ'` and the statement holds for `φ'`
      intros
      rename_i n φ' ih v xs ι hι hv hxs
      constructor
      · -- Suppose `M ⊨ φ(v, xs)`.
        intro h
        -- Then, `M ⊨ φ'(v, xs, a)` for all `a ∈ M`.
        apply BoundedFormula.realize_all.1 at h
        -- We need to prove that for all `b ∈ N`, `N ⊨ φ'(ι ∘ v, ι ∘ xs, b)`.
        apply BoundedFormula.realize_all.2
        -- Fix `b ∈ N`.
        intro b
        -- Then, there is a `ι' ∈ F` extending `ι` s.t. `b` is in the codomain of `ι'`
        let hι' := hF.2 ι hι b
        obtain ⟨ ι', hι'₁, hι'₂, hι'₃ ⟩ := hι'
        -- Let `a` be the preimage of `b`under `ι'`
        let a := ι'.invFun b
        -- Then, `M ⊨ φ'(v, xs, a)`
        specialize h a
        apply (PartialIso.le_def M N ι ι').1 at hι'₃
        obtain ⟨ hι'₃, hι'₄ ⟩ := hι'₃
        have hι'xs : ι'.toFun ∘ xs = ι.toFun ∘ xs := by
          ext x
          simp_all
        have hι'v : ι'.toFun ∘ v = ι.toFun ∘ v := by
          ext x
          simp_all
        have hv' : ∀ x, v x ∈ ι'.source := by
          intro x
          exact Set.mem_preimage.mp (hι'₃ (hv x))
        have hxs' : ∀ x, ((@Fin.snoc n (fun a ↦ M) xs a) x ∈ ι'.source) := by
          intro x
          simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq]
          aesop
        -- By the induction hypothesis, this means `N ⊨ φ'(ι' ∘ v, ι' ∘ xs, b)`.
        specialize ih v (@Fin.snoc n (fun a ↦ M) xs a) ι' hι'₁ hv' hxs'
        apply ih.1 at h
        -- Since `ι'` extends `ι`, we get `N ⊨ φ'(ι ∘ v, ι ∘ xs, b)`,
        -- which is what we wanted to show.
        have hι'₅ : ι'.toFun ∘ (@Fin.snoc n (fun a ↦ M) xs a) = Fin.snoc (ι'.toFun ∘ xs) b := by
          ext x
          simp_all only [Function.comp_apply, Fin.snoc, Fin.castSucc_castLT, cast_eq,
            PartialEquiv.invFun_as_coe, iff_true, a]
          split
          next h_1 => simp_all
          next h_1 => simp_all
        rw [hι'₅] at h
        rw [hι'v] at h
        rw [hι'xs] at h
        assumption
      · -- Now, suppose `N ⊨ φ(ι ∘ v, ι ∘ xs)`
        intro h
        -- This means that for all `b ∈ N`, `N ⊨ φ'(ι ∘ v, ι ∘ xs, b)`
        apply BoundedFormula.realize_all.1 at h
        -- We want to prove that for all `a ∈ M`, `M ⊨ φ(v, xs, a)`.
        apply BoundedFormula.realize_all.2
        -- Fix `a ∈ M`.
        intro a
        -- Then, there is `ι'` extending `ι` such that `a` is in the domain of `ι'`
        let hι' := hF.1 ι hι a
        obtain ⟨ ι', hι'₁, hι'₂, hι'₃ ⟩ := hι'
        -- We define `b` as the image of `a` under `ι'`.
        let b := ι'.toFun a
        specialize h b
        apply (PartialIso.le_def M N ι ι').1 at hι'₃
        obtain ⟨ hι'₃, hι'₄ ⟩ := hι'₃
        -- Since `ι'` extends `ι`, we know that `N ⊨ φ'(ι' ∘ v, ι' ∘ xs, b)`.
        have hι'xs : ι'.toFun ∘ xs = ι.toFun ∘ xs := by
          ext x
          simp_all
        have hι'v : ι'.toFun ∘ v = ι.toFun ∘ v := by
          ext x
          simp_all
        rw [← hι'v] at h
        rw [← hι'xs] at h
        have hv' : ∀ x, v x ∈ ι'.source := by
          intro x
          exact Set.mem_preimage.mp (hι'₃ (hv x))
        have hxs' : ∀ x, ((@Fin.snoc n (fun a ↦ M) xs a) x ∈ ι'.source) := by
          intro x
          simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq]
          aesop
        -- By the induction hypothesis, our goal is equivalent to showing
        -- `N ⊨ φ'(ι' ∘ v, ι' ∘ xs, b)`, which is what we wanted to prove.
        specialize ih v (@Fin.snoc n (fun a ↦ M) xs a) ι' hι'₁ hv' hxs'
        apply ih.2
        have hι'₅ : ι'.toFun ∘ (@Fin.snoc n (fun a ↦ M) xs a) = Fin.snoc (ι'.toFun ∘ xs) b := by
          ext x
          simp only [Function.comp_apply, Fin.snoc, Fin.castSucc_castLT, cast_eq]
          aesop
        rw [hι'₅]
        assumption

/-- Partial isomorphisms in a back-and-forth-system commute with interpretations of formulas. -/
theorem on_formula (F : Set (L.PartialIso M N)) (hF : L.IsBackAndForthSystem M N F)
  (φ : L.Formula α) :
  ∀ (v : α → M) (ι : L.PartialIso M N) (hι : ι ∈ F) (hv : ∀ x, v x ∈ ι.source),
  φ.Realize v ↔ φ.Realize (ι.toFun ∘ v) := by
    intro v ι hι hv
    unfold Formula.Realize
    unfold Formula at φ
    let xs : Fin 0 → M := default
    have hxs : ∀ x, xs x ∈ ι.source := by unfold xs; simp only [IsEmpty.forall_iff]
    have h := on_boundedFormula M N F hF φ v xs ι hι hv hxs
    have h' : (ι.toFun ∘ xs) = default := List.ofFn_inj.mp rfl
    unfold xs at h
    rw [h'] at h
    assumption

/-- If there is a nonempty back-and-forth-system between the
`L`-structures `M` and `N`, then `M` and `N` are elementary equivalent. -/
theorem elementarilyEquivalent_if_exists_nonempty :
  (∃ (F : Set (L.PartialIso M N)), (Nonempty F ∧ (L.IsBackAndForthSystem M N F))) →
  L.ElementarilyEquivalent M N := by {
    -- Suppose `F` is a nonempty back-and-forth-system between `M` and `N`
    intro h
    obtain ⟨ F, ι, hF ⟩ := h
    apply Classical.choice at ι
    -- We need to show that for every `L`-sentence `φ`,
    -- `M ⊨ φ` if and only if `N ⊨ φ`.
    apply elementarilyEquivalent_iff.2
    intro φ
    unfold Sentence at φ
    let v : Empty → M := default
    -- Since `F` is nonempty, there exists a partial iso `ι' ∈ F`.
    let ι' : L.PartialIso M N := ι
    have hι' : ι' ∈ F := Subtype.coe_prop ι
    have hv : ∀ (x : Empty), v x ∈ ι'.source := by simp only [IsEmpty.forall_iff]
    unfold Sentence.Realize
    have hv₁ : v = default := Unique.ext_iff.mp rfl
    have hv₂ : ι'.toFun ∘ v = default := by ext x; trivial
    rw [← hv₁]
    rw [← hv₂]
    -- The goal follows from the fact that `ι'` commutes with interpretation of formulas.
    exact on_formula M N F hF φ v ι' hι' hv
  }

end BackAndForth

namespace CompleteType

/-- A partial isomorphism between `M` and `N` mapping an `M`-tuple `a`
to an `N`-tuple `b` that satisfies the same quantifer-free formulas as `a`. -/
noncomputable def toPartialIso [Nonempty M] [Nonempty N]
  (a : α → M) (b : α → N) (hab : ∀ φ : L.Formula α, φ.IsQF → (φ.Realize a ↔ φ.Realize b)) :
  L.PartialIso M N where
    source := {y | ∃ x, a x = y}
    target := {y | ∃ x, b x = y}
    /- `toFun` maps every element of `M` in the image of `a`
    to the image under `b` of a preimage under `a`. -/
    -- Note: `a` and `b` are not necessarily injective, so we still
    -- have to prove that this map does not depend on the choice of the preimage under `a`.
    toFun := fun x ↦ by
      by_cases h : ∃ y, a y = x
      · use b (Classical.choose h)
      · rename_i hM₁ hN₁ hM₂ hN₂
        use (Classical.choice hN₂)
    /- `invFun` maps every element of `M` in the image of `b`
    to the image under `a` of a preimage under `b` -/
    -- Note: Since `a` and `b` are not necessarily injective, it still remains to prove
    -- that this map does not depend on the choice of the preimage under `b`.
    invFun := fun x ↦ by
      by_cases h : ∃ y, b y = x
      · use a (Classical.choose h)
      · rename_i hM₁ hN₁ hM₂ hN₂
        use (Classical.choice hM₂)
    map_source' := by
      intro x hx
      simp_all
    map_target' := by
      intro x hx
      simp_all
    left_inv' := by
      -- Let `x ∈ M`. We need to prove that if `x` is in the image of `a`,
      -- then `invFun(toFun(x)) = x`.
      intro x hx
      -- Since equality of two variables is a quantifier-free formula,
      -- we know that two elements of `α` have the same image under `a`
      -- if and only if they have the same image under `b`.
      have h : ∀ i₁ i₂ : α, a i₁ = a i₂ ↔ b i₁ = b i₂ := by
        intro i₁ i₂
        let t₁ : L.Term (α ⊕ (Fin 0)) := var (Sum.inl i₁)
        let t₂ : L.Term (α ⊕ (Fin 0)) := var (Sum.inl i₂)
        let φ : L.Formula α := BoundedFormula.equal t₁ t₂
        have hφ : φ.IsQF := by
          unfold IsQF
          tauto
        specialize hab φ hφ
        finiteness
      -- Hence, for all `x` in the image of `a`, the image under `b` of
      -- any preimage under `a` equals `x`.
      -- This is what we wanted to prove.
      have h' : ∀ x, x ∈ {y | ∃ x', a x' = y} → ((fun (z : N) ↦ by
        by_cases h : ∃ y, b y = z
        · use a (Classical.choose h)
        · rename_i hM₁ hN₁ hM₂ hN₂ _ _
          use (Classical.choice hM₂)) ((fun (z : M) ↦ by
      by_cases h : ∃ y, a y = z
      · use b (Classical.choose h)
      · rename_i hM₁ hN₁ hM₂ hN₂ _ _
        use (Classical.choice hN₂)) x) = x ) := by
          simp only [Set.mem_ofPred_eq, forall_exists_index, forall_apply_eq_imp_iff,
            exists_apply_eq_apply, ↓reduceDIte]
          grind
      tauto
    right_inv' := by
      -- Let `x ∈ N` be in the image of `b`.
      -- We need to prove `toFun(invFun(x)) = x`
      intro x hx
      -- Again, note that any two elements of `α` have the same image under `a`
      -- if and only if they have the same image under `b`.
      have h : ∀ i₁ i₂ : α, a i₁ = a i₂ ↔ b i₁ = b i₂ := by
        intro i₁ i₂
        let t₁ : L.Term (α ⊕ (Fin 0)) := var (Sum.inl i₁)
        let t₂ : L.Term (α ⊕ (Fin 0)) := var (Sum.inl i₂)
        let φ : L.Formula α := BoundedFormula.equal t₁ t₂
        have hφ : φ.IsQF := by
          unfold IsQF
          tauto
        specialize hab φ hφ
        finiteness
      -- This implies our goal.
      have h' : ∀ x, x ∈ {y | ∃ x, b x = y} → ((fun x ↦ by
      by_cases h : ∃ y, a y = x
      · use b (Classical.choose h)
      · rename_i hM₁ hN₁ hM₂ hN₂ _ _ _
        use (Classical.choice hN₂)) ((fun x ↦ by
      by_cases h : ∃ y, b y = x
      · use a (Classical.choose h)
      · rename_i hM₁ hN₁ hM₂ hN₂ _ _ _
        use (Classical.choice hM₂)) x)) = x := by
          simp only [Set.mem_ofPred_eq, forall_exists_index, forall_apply_eq_imp_iff,
            exists_apply_eq_apply, ↓reduceDIte]
          grind
      tauto
    map_fun' := by
      -- Now, we want to prove that `toFun` commutes with interpretation of function symbols.
      -- Therefore, let `f` be an `n`-ary function symbol and
      -- `v(0)`, ..., `v(n-1)`, `m` be in the image of `a`.
      intro n f v m h
      obtain ⟨ hv, hm ⟩ := h
      simp only [Set.mem_ofPred_eq] at hv
      simp only [Set.mem_ofPred_eq] at hm
      -- Now, let `φ` be the formula `f(x₁, ..., xₙ) = x_{n+1}`.
      -- Here, `x₁, ..., xₙ` are preimages of `v(0)`, ..., `v(n-1)` under `a`
      -- and `x_{n-1}` is a preimage of `m` under `a`.
      let φ : L.Formula α :=
        BoundedFormula.equal
        (Term.func f (fun x ↦ Term.var (Sum.inl (Classical.choose (hv x)))))
        (Term.var (Sum.inl (Classical.choose hm)))
      -- Then, `φ` is quantifier-free.
      have hφ : φ.IsQF := by
        unfold IsQF
        tauto
      rename_i hM₁ hN₁ hM₂ hN₂
      -- Note that `toFun` is indeed meaningfully defined on `m`
      have hm' : (@dite N (∃ y, a y = m) (Classical.propDecidable (∃ y, a y = m))
      (fun h ↦ b (Classical.choose h)) fun h ↦ Classical.choice hN₂)
      = b (Classical.choose hm) := by
        simp_all only [↓reduceDIte]
      rw [hm']
      -- analogously, note that `toFun` is meaningfully defined on all `v(i)` for `0 ≤ i ≤ n-1`
      have hv' : (fun x ↦
      (@dite N (∃ y, a y = x) (Classical.propDecidable (∃ y, a y = x))
      (fun h ↦ b (Classical.choose h)) fun h ↦ Classical.choice hN₂)) ∘ v
      = (fun i ↦ b (Classical.choose (hv i))) := by
        ext x
        simp_all
      rw [hv']
      have hma : a (Classical.choose hm) = m := by grind
      have hva : (fun i ↦ a (Classical.choose (hv i))) = v := by
        ext x
        grind
      constructor
      · -- Suppose `f^M(v(0), ..., v(n-1)) = m`.
        intro hf
        -- Then, `M ⊨ φ(a)` by definition of `φ`.
        have hφa : φ.Realize a := by
          unfold φ
          apply (BoundedFormula.realize_bdEqual
            (Term.func f (fun x ↦ Term.var (Sum.inl (Classical.choose (hv x)))))
            ((Term.var (Sum.inl (Classical.choose hm))))).2
          simp only [Term.realize_func, Term.realize_var, Sum.elim_inl]
          rwa [hma, hva]
        -- Hence, `N ⊨ φ(b)` since `φ` is quantifier-free.
        apply (hab φ hφ).1 at hφa
        unfold φ at hφa
        -- This implies `f^N(toFun ∘ v) = toFun(m)`, which is what we wanted to show.
        apply (BoundedFormula.realize_bdEqual
          (Term.func f (fun x ↦ Term.var (Sum.inl (Classical.choose (hv x)))))
          ((Term.var (Sum.inl (Classical.choose hm))))).1 at hφa
        simp_all
      · -- On the other hand, suppose `f^N(toFun(v(0)), ..., toFun(v(n-1))) = toFun(m)`.
        intro h
        -- Then, by definition of `φ`, we get `N ⊨ φ(b)`
        have hφb : φ.Realize b := by
          unfold φ
          apply (BoundedFormula.realize_bdEqual
            (Term.func f (fun x ↦ Term.var (Sum.inl (Classical.choose (hv x)))))
            ((Term.var (Sum.inl (Classical.choose hm))))).2
          simpa
        -- Hence, `M ⊨ φ(a)` since `φ` is quantifier-free
        apply (hab φ hφ).2 at hφb
        unfold φ at hφb
        -- This implies `f^M(v(0), ..., v(n-1)) = m`, which is what we wanted to prove.
        apply (BoundedFormula.realize_bdEqual
          (Term.func f (fun x ↦ Term.var (Sum.inl (Classical.choose (hv x)))))
          ((Term.var (Sum.inl (Classical.choose hm))))).1 at hφb
        simp_all
    map_rel' := by
      -- Next, we are going to prove that `toFun` commutes with
      -- interpretation of relation symbols.
      -- Hence, let `r` be an `n`-ary relation symbol in `L` and
      -- `v(0)`, ..., `v(n-1)` be in the image of `a`.
      intro n r v hv
      rename_i hM₁ hN₁ hM₂ hN₂
      simp only [Set.mem_ofPred_eq] at hv
      -- Then, `toFun v(i)` is meaningfully defined for all `0 ≤ i ≤ n-1`.
      have hv' : (fun x ↦
      (@dite N (∃ y, a y = x) (Classical.propDecidable (∃ y, a y = x))
      (fun h ↦ b (Classical.choose h)) fun h ↦ Classical.choice hN₂)) ∘ v
      = (fun i ↦ b (Classical.choose (hv i))) := by
        ext x
        simp_all
      rw [hv']
      -- Let `φ` be the `L`-formula `r(x₁, ..., xₙ)`, where
      -- `x₁`, ..., `xₙ` are preimages of `v(0)`, ..., `v(n-1)` under `a`.
      let φ : L.Formula α :=
        BoundedFormula.rel r (fun i ↦ Term.var (Sum.inl (Classical.choose (hv i))))
      -- One can easily see that `φ` is quantifier-free.
      have hφ : φ.IsQF := by unfold IsQF; tauto
      have hv'' : (fun i ↦ a (Classical.choose (hv i))) = v := by
        ext x
        grind
      constructor
      · -- Suppose that `r^M(v(0), ..., v(n-1))` holds.
        intro h
        -- Then, `M ⊨ φ(a)`.
        have hφa : φ.Realize a := by
          unfold φ
          apply BoundedFormula.realize_rel.2
          simp only [Term.realize_var, Sum.elim_inl]
          rwa [hv'']
        -- Since `φ` is quantifier-free, this implies `N ⊨ φ(b)` by assumption.
        apply (hab φ hφ).1 at hφa
        -- Hence, `r^N(toFun(v(0)), ..., toFun(v(n-1)))` holds.
        unfold φ at hφa
        apply BoundedFormula.realize_rel.1 at hφa
        simp_all
      · -- On the other hand, suppose `r^N(toFun(v(0)), ..., toFun(v(n-1)))` holds.
        intro h
        -- Then, `N ⊨ φ(b)` by definition of `φ`.
        have hφb : φ.Realize b := by
          unfold φ
          apply BoundedFormula.realize_rel.2
          simpa
        -- Since `φ` is quantifier-free, this implies `M ⊨ φ(a)` by assumption.
        apply (hab φ hφ).2 at hφb
        -- Hence, `r^M(v(0), ..., v(n-1))`, which is what we wanted to show.
        unfold φ at hφb
        apply BoundedFormula.realize_rel.1 at hφb
        simp only [Term.realize_var, Sum.elim_inl] at hφb
        rwa [← hv'']

/-- `toPartialIso a b hab` maps `a` to `b`. -/
lemma toPartialIso_def [Nonempty M] [Nonempty N]
  (a : α → M) (b : α → N) (hab : ∀ φ : L.Formula α, φ.IsQF → (φ.Realize a ↔ φ.Realize b)) :
  (toPartialIso M N a b hab).toFun ∘ a = b := by
    rename_i hM₁ hN₁ hM₂ hN₂
    ext i
    unfold toPartialIso
    simp only [Function.comp_apply, exists_apply_eq_apply, ↓reduceDIte]
    have h : ∀ i₁ i₂ : α, a i₁ = a i₂ ↔ b i₁ = b i₂ := by
      intro i₁ i₂
      let t₁ : L.Term (α ⊕ (Fin 0)) := var (Sum.inl i₁)
      let t₂ : L.Term (α ⊕ (Fin 0)) := var (Sum.inl i₂)
      let φ : L.Formula α := BoundedFormula.equal t₁ t₂
      have hφ : φ.IsQF := by
        unfold IsQF
        tauto
      specialize hab φ hφ
      finiteness
    grind

end CompleteType

namespace BoundedFormula

namespace IsQF

/-- If `φ.imp ψ` is quantifier-free, then so are `φ` and `ψ`. -/
theorem imp' {n : ℕ} {φ ψ : L.BoundedFormula α n} :
  IsQF (φ.imp ψ) → (IsQF φ ∧ IsQF ψ) := by
    intro hφψ
    cases hφψ
    · contradiction
    · trivial
end IsQF

/-- If `φ` is quantifier-free, then so is `φ.restrictFreeVar f`
for any `f : φ.freeVarFinset → β`. -/
theorem restrictFreeVar_IsQF {n : ℕ} {β : Type*} [DecidableEq α]
  (φ : L.BoundedFormula α n) (f : φ.freeVarFinset → β) :
  φ.IsQF ↔ (φ.restrictFreeVar f).IsQF := by
    induction φ with
    | falsum =>
      unfold restrictFreeVar
      constructor
      · intro h
        exact IsQF.falsum
      · intro h
        exact IsQF.falsum
    | equal t₁ t₂ =>
      unfold restrictFreeVar
      constructor
      · intro h
        tauto
      · intro h
        tauto
    | rel R ts =>
      unfold restrictFreeVar
      constructor
      · intro h
        tauto
      · intro h
        tauto
    | imp f₁ f₂ f₁_ih f₂_ih =>
      unfold restrictFreeVar
      constructor
      · intro h
        apply IsQF.imp' at h
        obtain ⟨ hf₁, hf₂ ⟩ := h
        refine IsQF.imp ?_ ?_
        · simp_all
        · simp_all
      · intro h
        apply IsQF.imp' at h
        obtain ⟨ hf₁, hf₂ ⟩ := h
        refine IsQF.imp ?_ ?_
        · grind
        · grind
    | all f ih =>
      rename_i _ m φ
      constructor
      · intro h
        contradiction
      · intro h
        contradiction

end BoundedFormula

namespace Theory

theorem HasQE_on_finite_if_BackAndForth_of_finite {L : Language} (T : L.Theory) :
  (∀ M N : ModelType.{u, v, max u v} T,
  L.IsBackAndForthSystem M N {f : L.PartialIso M N | Finite f.source})
  → ∀ (α : Type u) (_ : Finite α) (φ : L.Formula α),
  ∃ ψ : L.Formula α, (ψ.IsQF ∧ T ⊨ᵇ (φ.iff ψ)) := by {
    intro hT α _ φ
    let Sigma : Set (L.Formula α) := { ψ : L.Formula α | ψ.IsQF}
    have closed_conj : ∀ φ ψ, (φ ∈ Sigma) ∧ (ψ ∈ Sigma) →  (φ ⊔ ψ) ∈ Sigma := by {
      unfold Sigma; simp only [Set.mem_ofPred_eq, and_imp]; unfold IsQF
      intro φ ψ hφ hψ
      exact BoundedFormula.IsQF.sup hφ hψ
    }
    have closed_disj : ∀ φ ψ, (φ ∈ Sigma) ∧ (ψ ∈ Sigma) → (φ ⊓ ψ) ∈ Sigma := by {
      unfold Sigma; simp only [Set.mem_ofPred_eq, and_imp]; unfold IsQF
      intro φ ψ hφ hψ
      exact BoundedFormula.IsQF.inf hφ hψ
    }
    have contains_top : ⊤ ∈ Sigma := by
      unfold Sigma; unfold IsQF
      simp only [Set.mem_ofPred_eq]
      exact BoundedFormula.IsQF.top
    have contains_bot : ⊥ ∈ Sigma := by
      unfold Sigma; unfold IsQF
      simp only [Set.mem_ofPred_eq]
      exact BoundedFormula.isQF_bot
    apply (CompleteType.ContainsEquivForumulas_iff_SeparatesTypes T Sigma
      closed_conj closed_disj contains_top contains_bot).2
    by_contra h
    push Not at h
    obtain ⟨ p, q, hpq₁, hpq⟩ := h
    have hpq' : ∀ ψ ∈ Sigma, equivSentence ψ ∈ q → equivSentence ψ ∈ p := by
      intro ψ hψ
      have hψ' : ψ.not ∈ Sigma := by
        unfold Sigma
        simp only [Set.mem_ofPred_eq]
        unfold IsQF
        exact BoundedFormula.IsQF.not hψ
      specialize hpq ψ.not hψ'
      intro hψq
      by_contra hψp
      have hψp' : (equivSentence ψ).not ∈ p :=
        (CompleteType.not_mem_iff p (equivSentence ψ)).mpr hψp
      rw [← equivSentence_not] at hψp'
      apply hpq at hψp'
      rw [equivSentence_not] at hψp'
      have hψq' : (equivSentence ψ) ∉ q :=
        (CompleteType.not_mem_iff q (equivSentence ψ)).mp hψp'
      contradiction
    apply hpq₁
    obtain ⟨ M, hM ⟩ := exists_modelType_is_realized_in T p
    obtain ⟨ N, hN ⟩ := exists_modelType_is_realized_in T q
    unfold realizedTypes at hM; unfold realizedTypes at hN
    unfold Set.range at hM; simp only [Set.mem_ofPred_eq] at hM
    unfold Set.range at hN; simp only [Set.mem_ofPred_eq] at hN
    obtain ⟨ a, ha ⟩ := hM; obtain ⟨ b, hb ⟩ := hN
    specialize hT M N
    have hab : ∀ φ : L.Formula α, φ.IsQF → (φ.Realize a ↔ φ.Realize b) := by
      intro φ hφ
      have hφ': φ ∈ Sigma := by unfold Sigma; simp_all
      constructor
      · intro hφ''
        apply (@CompleteType.formula_mem_typeOf L T).2 at hφ''
        rw [ha] at hφ''
        specialize hpq φ hφ hφ''
        rw [← hb] at hpq
        apply (@CompleteType.formula_mem_typeOf L T).1 at hpq
        assumption
      · intro hφ''
        apply (@CompleteType.formula_mem_typeOf L T).2 at hφ''
        rw [hb] at hφ''
        specialize hpq' φ hφ hφ''
        rw [← ha] at hpq'
        apply (@CompleteType.formula_mem_typeOf L T).1 at hpq'
        assumption
    let ι := CompleteType.toPartialIso M N a b hab
    have hι : Finite ι.source := by
      unfold ι
      unfold CompleteType.toPartialIso
      simp_all only [and_imp, ne_eq, Set.coe_ofPred]
      let f : α → (@Subtype ↑M fun y ↦ ∃ x, a x = y ) := fun x ↦ ⟨ a x, by use x ⟩
      have hf : Function.Surjective f := by
        unfold Function.Surjective
        intro b
        grind
      exact Finite.of_surjective f hf
    have hι' : ι ∈ {f : L.PartialIso M N | Finite f.source} := by
      simpa
    ext φ
    rw [← ha]
    rw [← hb]
    have ha' : ∀ x : α, a x ∈ ι.source := by
      unfold ι
      unfold CompleteType.toPartialIso
      simp
    constructor
    · intro hφ
      apply CompleteType.mem_typeOf.1 at hφ
      apply CompleteType.mem_typeOf.2
      have h := BackAndForth.on_formula M N {f : L.PartialIso M N | Finite f.source}
        hT (equivSentence.symm φ) a ι hι ha'
      apply h.1 at hφ
      unfold ι at hφ
      have hab' := CompleteType.toPartialIso_def M N a b hab
      rw [hab'] at hφ
      assumption
    · intro hφ
      apply CompleteType.mem_typeOf.1 at hφ
      apply CompleteType.mem_typeOf.2
      have h := BackAndForth.on_formula M N {f : L.PartialIso M N | Finite f.source}
        hT (equivSentence.symm φ) a ι hι ha'
      apply h.2
      unfold ι
      have hab' := CompleteType.toPartialIso_def M N a b hab
      rw [hab']
      assumption
  }

/-- If for all models `M` and `N` of a theory `T`,
the set of partial isomorphisms with finite domain between `M` and `N` is a back-and-forth system,
then `T` has quantifier elimination. -/
theorem HasQE_if_BackAndForth_of_finite {L : Language} (T : L.Theory) :
  (∀ M N : ModelType.{u, v, max u v} T,
  L.IsBackAndForthSystem M N {f : L.PartialIso M N | Finite f.source})
  → T.HasQE := by
    unfold HasQE
    intro hT α _ φ
    have h₁ : @SetLike.coe (Finset α) α Finset.instSetLike φ.freeVarFinset
      ⊆ @SetLike.coe (Finset α) α Finset.instSetLike φ.freeVarFinset := by trivial
    let f := Set.inclusion h₁
    let φ' : L.Formula (φ.freeVarFinset) := φ.restrictFreeVar f
    have hα' : Finite (BoundedFormula.freeVarFinset φ) :=
      Finite.of_fintype ↥(BoundedFormula.freeVarFinset φ)
    have hφ' := HasQE_on_finite_if_BackAndForth_of_finite T hT
      (BoundedFormula.freeVarFinset φ) hα' φ'
    obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := hφ'
    have _ : DecidableEq (BoundedFormula.freeVarFinset φ) := instDecidableEqOfLawfulBEq
    let f' : ψ.freeVarFinset → α := fun x ↦ x
    let ψ' : L.Formula α := ψ.restrictFreeVar f'
    use ψ'
    constructor
    · unfold ψ'
      apply (BoundedFormula.restrictFreeVar_IsQF ψ f').1
      assumption
    · intro M v xs
      rw [BoundedFormula.realize_iff]
      have hv' : ∀ (a : (@Subtype (φ.freeVarFinset) fun x ↦ x ∈ ψ.freeVarFinset)),
        v (f' a) = (@Function.comp (↥(BoundedFormula.freeVarFinset φ)) α (M) v Subtype.val) a := by
          intro a
          unfold f'
          simp only [Function.comp_apply]
      unfold φ' at hψ₂
      specialize hψ₂ M (v ∘ Subtype.val) xs
      rw [BoundedFormula.realize_iff] at hψ₂
      constructor
      · intro h
        unfold ψ'
        apply (BoundedFormula.realize_restrictFreeVar' h₁).2 at h
        apply hψ₂.1 at h
        apply (BoundedFormula.realize_restrictFreeVar (v ∘ Subtype.val) hv').2
        assumption
      · intro h
        unfold ψ' at h
        apply (BoundedFormula.realize_restrictFreeVar' h₁).1
        apply hψ₂.2
        apply (BoundedFormula.realize_restrictFreeVar (v ∘ Subtype.val) hv').1 at h
        assumption

end Theory
end Language
end FirstOrder
