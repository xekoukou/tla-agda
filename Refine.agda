module Refine where

open import Prelude.Function
open import Def public

action-dom-embed : ∀ {α n vars} → (act1 act2 : Action {α} {n} vars) → Set α
action-dom-embed {α} {_} {vars} act1 act2 = ∀ n → (sys : System vars n) → ((cond act1) n sys → (cond act2) n sys )

action-range-embed : ∀ {α n vars} → (act1 act2 : Action {α} {n} vars) → Set α
action-range-embed {α} {_} {vars} act1 act2 = ∀ n → (sys : System vars n) → (nsys : System vars (suc n)) → (cond act1) n sys → resp act1 n sys nsys → (resp act2) n sys nsys

action-embed : ∀ {α n vars} → (act1 act2 : Action {α} {n} vars) → Set α
action-embed {α} {_} {vars} act1 act2 = action-dom-embed act1 act2 × action-range-embed act1 act2

action-stut-embed : ∀ {α n vars} → (act : Action {α} {n} vars) → Set α
action-stut-embed {α} {_} {vars} act = ∀ n → (sys : System vars n) → (nsys : System vars (suc n)) → (cond act) n sys → resp act n sys nsys → varsEq {vars = vars} sys nsys


action-spec-embed : ∀ {α n k vars} → (act : Action {α} {n} vars) → (spec : Spec {α} {n} {k} vars) → Set (lsuc α)
action-spec-embed act spec = ∃ λ act2 → (act2 ∈v spec) × (action-embed act act2) 

action-spec-embed-with-stut : ∀ {α n k vars} → (act : Action {α} {n} vars) → (spec : Spec {α} {n} {k} vars) → Set (lsuc α)
action-spec-embed-with-stut act spec = action-spec-embed act spec ⊎ action-stut-embed act

spec-embed : ∀ {α n k1 k2 vars} → (spec1 : Spec {α} {n} {k1} vars) → (spec2 : Spec {α} {n} {k2} vars) → Set (lsuc α)
spec-embed {α} {k1 = .0} (x ∷ []) spec2 = action-spec-embed-with-stut x spec2 
spec-embed {α} {k1 = .(suc _)} (x ∷ x₁ ∷ spec1) spec2 = action-spec-embed-with-stut x spec2 × spec-embed (x₁ ∷ spec1) spec2


spec-action-covering : ∀{α n k vars} → (spec1 : Spec {α} {n} {k} vars) → (act :  Action {α} {n} vars) → Set (lsuc α)
spec-action-covering {α} {vars = vars} spec1 act = Σ {b = α} (∃ λ n → Vec (action-spec-embed act spec1) n ) λ x
                                                → let conds = fmap (cond ∘ fst) (snd x)
                                                  in ∀ n → (sys : System vars n) →
                                                     let s = vfoldr (λ x y → (x n sys) ⊎ y) (⊥′ {α}) conds
                                                     in cond act n sys → s


spec-covering : ∀ {α n k1 k2 vars} → (spec1 : Spec {α} {n} {k1} vars) → (spec2 : Spec {α} {n} {k2} vars) → Set (lsuc α)
spec-covering spec1 (x ∷ []) = spec-action-covering spec1 x
spec-covering spec1 (x ∷ x₁ ∷ spec2) = spec-action-covering spec1 x × spec-covering spec1 (x₁ ∷ spec2)
-- There are multiple spec-covering and each one determines a different spec2 implementation.


spec-refinement : ∀ {α n k1 k2 vars} → (spec1 : Spec {α} {n} {k1} vars) → (spec2 : Spec {α} {n} {k2} vars) → Set (lsuc α)
spec-refinement spec1 spec2 = spec-embed spec1 spec2 × spec-covering spec1 spec2




-- spec-covering allows us to construct actions of spec2 from actions of spec1,
-- thus any temporal proofs that used actions of spec2 is also valid for spec1 (with the refinement mapping).
-- There are a multitude of implementations of spec2 , depending on the choice of actions of spec1 that will be chosen in the covering.
-- For each behavior of spec1, one can construct an implementation of spec2 that permits this behavior. (Is this true ?) This is necessary to
-- be able to use the theorems of spec2 for the behaviors of spec1.

-- temporal restrictions on the other hand do not need to construct the actions of spec2. We simply take that behavior through the refinement mapping and check whether it
-- respects it.

