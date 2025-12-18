# Bisikkel

By "dup", I mean one thing can probably be implemented using another (perhaps overlooking technical hurdles).

## Preliminaries
- funext, uip, etc

## Model

### BaseCategory
- `BaseCategory` is a category
  - `IsPreorder`: a category is thin
  - instances: `ω ★ ↑  ⋀`
- `BaseFunctor` is a functor
  - id and comp
- `BaseNatTransf` is a nattrans
  - `_≅ᵇᵗ_`: equivalence of nattranses := equal morphisms for each object
  - thin codomain => uniqueness of nattranses
  
### CwF-Structure
There is an overview file.

#### Context
- `Ctx` is a presheaf (dup of `BaseFunctor`)
- Substitution `_⇒_` is a presheaf morphism (dup of `BaseNatTransf`)
  - `_≅ˢ_`: equivalence of substitutions := equal morphisms for each object (dup of `_≅ᵇᵗ_`)
- `◇`: terminal context/presheaf and its terminality

#### ContextEquivalence
- `_≅ᶜ_`: equivalence of contexts = isomorphism.

#### Yoneda
- `𝕪`: yoneda-embedding of an object
  - stuff making it a functor, but there is no functor type
  - yoneda-lemma as an expanded isomorphism (2 sides & 2 lemmas)

#### Type
- `Ty`: presheaf over category of elements (dup of `Ctx`)
- `_↣_`: nattrans between types (dup of `_⇒_`)
  - `_≅ⁿ_` equivalence of nattranses := equal morphisms for each object (dup of `_≅ˢ_`)
- `_≅ᵗʸ_`: equivalence of types = isomorphism (dup of `_≅ᶜ_`)
  - `_≅ᵉ_` (of two type equivalences): the reverse type nattranses are `_≅ⁿ_`.
- `_[_]`: type substitution
  - `ιc[_]_ ιc⁻¹[_]_` ... along an isomorphism

#### Term
- `Tm`: term; dependent natural transformation
  - `_≅ᵗᵐ_` equivalence of terms := equal type cells for each context cell
- `_[_]'`: term substitution
  - `ιc[_]'_ ιc⁻¹[_]'_` ... along an isomorphism
  
#### ContextExtension
What you would expect.

#### ClosedType
- `ClosedTy` is an arbitrary type in every context.
- `IsClosedNatural`: types are chosen pseudonaturally
- `_[_∣_]cl`: special substitution for terms of closed natural types.
- `_,cl⟨_⟩_`: substitution extension of `id` with a closed natural type.
- `_//cl⟨_⟩`: substitution extension of `π` with a closed natural type.
- `_≅ᶜⁿ_` (of two proofs of `IsClosedNatural` for the same `ClosedTy`):
  the type-equivalences (`≅ᵗʸ`) witnessing pseudonaturality are `≅ᵉ`-equivalent.
- `_≅ᶜᵗʸ_` (of two closed natural types):
  `≅ᵗʸ`-equivalent types for every context and `≅ᵉ`-equivalent witnesses of pseudonaturality.

#### ContextFunctor
- `CtxOp` is a mapping of contexts.
- `IsCtxFunctor` extends it to a functor.
- `CtxFunctor` pairs them up (dup of `BaseFunctor`).
- `CtxNatTransf` is a natural transformation (dup of `BaseNatTransf`).
  - `_≅ᶜᵗ_`: equivalence of nattranses = `≅ˢ`-equivalent substitutions on morphisms (in XTT: dup of `≅ᵇᵗ`).
- `_≅ᶜᶠ_`: equivalence of ctx-functors = natural isomorphism, i.e. invertible `CtxNatTransf` (dup of `≅ᶜ`).

##### LiftBaseFunctor
- `lift-ctx` is upper-star (precomposition) applied to contexts.
- bang requires a quotient (so not implemented)
- lower-star may have been done by [uHnftOad](https://github.com/uHnftOad)

##### LiftBaseNatTransf
- `lift-transf` is upper-star applied to substitutions.

#### Type.ContextTransformation
- helper stuff?

### DRA
There is an overview file.

#### Basics
- `DRA`: a dependent adjunction
  - field `ctx-functor`: the left adjoint
  - `lock`: the action on objects
  - field `⟨_∣_⟩`: the DRA
    - since `Ty` is considered cat-valued, `⟨_∣_⟩` is made to be a functor (although this is automatic)
  - fields `dra-intro dra-elim dra-β dra-η`: transposition as an isomorphism
  - fields for naturality and stuff
- properties
- denotation of the modal elimination rule
- terminal DRA ("unit DRA")
- composition of DRAs
- no identity DRA?

#### Limits
- `<$> <*>` for DRAs
- DRAs preserve type product up to iso
- DRAs preserve unit type up to iso

#### TwoCell
- `TwoCell`: a boxed `CtxNatTransf` (i.e. a nattrans between ctx-functors) between the left adjoints
  - `_≅ᵗᶜ_`: dup of `_≅ᶜᵗ_`, not boxed but duplicated
- properties

#### Equivalence
- `_≅ᵈ_`: an invertible `TwoCell`, up to `≅ᵗᶜ`
- properties

### Type
#### Function
Non-dependent function type
- `PshFun`: 1 cell of the function type
- `_⇛_`: the function type
- `_€⟨_,_⟩_`: application to a shape, ctx-cell and type cell
- properties
#### Constant
Turn an Agda type into a constant presheaf
- Unit, Empty, Nat
#### Sum
Non-dependent coproduct type
#### Product
Non-dependent product type
#### Dependent
##### Function
Analogous to non-dependent
##### Constant
Non-confusion lemma's over non-dependent constant types.
##### Identity
`dra-intro` preserves prop equality

## MSTT

### Parameter
- `MSTT-parameter`: record gathering the stuff from all the submodules

#### ModeTheory
- `MTMode`: specifies the of modes and their semantics, and there is always a `★` modelled in `Set`
- `MTModality`: specifies modalities and their semantics, and there is always the identity modalities
- `MTComposition`: composition of modalities & soundness (must interpret to actual composition)
- `MTCompositionLaws`
- `MTTwoCell`: 2-cells, id, horcomp, vercomp, semantics
- `MTTwoCellLaws`
- `ModeTheory`: contains all of the above

#### TypeExtension
- `TyExt`: specifies the custom type operations:
  - field `TyExtCode`: codes for each list of input modes and output mode (for MSTT).
  - semantics acting on closed natural types.
  
#### TermExtension
- `TmArgInfo` for a given conclusion mode: a premise mode, a telescope, a RHS type
- `TmExt`:
  - field `TmExtCode`: for every conclusion mode, a set of codes for custom term operations
  - conclusion RHS
  - list of premises
  
#### TermExtensionSemantics
- `TmExtSem`:
  - field `⟦_⟧tm-code`: semantics that model the inference rule in an arbitrary context
  - must be natural w.r.t. the context
  - congruence
- `SemTms` for a list of `TmArgInfo`s and a semantic context: semantic terms for the arguments
  
#### TermExtensionNormalization
(of course there is a forward dependency on syntax)
- `TmExtNormalization`: specifies how to normalize additional terms

### Syntax
There is an overview file.

#### Types
MSTT types & decidable equality

#### Contexts
- MSTT contexts - `Ctx`
  - variables have strings, which we now know is very annoying
- MSTT telescopes - `Telescope`
  - `NamelessTele`
- Lock telescopes - `LockTele`
  - `locksˡᵗ`: concatenate all the locks
  - decidable equality
  
#### Terms
- `Var`: **variables** with trailing telescope `Λ`
- `Tm`: intrinsically typed MTT syntax
  - note `global-def : DefName → {Tm ◇ T} → Tm Γ T`
- `var`: access a variable by name and 2-cell
- `svar`: acces a variable by name and the identity 2-cell

- `ExtTmArgs` for a list of `TmArgInfo`s and a syntactic context: syntactic terms for the arguments

#### Substitution
- `TravStruct`: allows `Trav` (of type of `Sub`) to function as a substitution
- `AtomicRenSub`: substitutes variables with `V`s
  - key substitution is between lock telescopes
- `RenSubDataStructure`: embeds `vzero` in `V` and `V` in terms
- `RenSub`: list of composable `AtomicRenSub`s.
- `AtomicRenM`: module instantiation of `AtomicRenSub` with renaming data
  - `AtomicRen` = special case of `AtomicRenSub`
- `RenM`: module instantiation of `RenSub` with renaming data
  - `Ren` = special case of `RenSub`
- `AtomicSubM`: module instantiation of `AtomicRenSub` with renaming data
  - `AtomicSub` = special case of `AtomicRenSub`
- `SubM`: module instantiation of `RenSub` with renaming data
  - `Sub` = special case of `RenSub`

### Interpretation
(imports submodule `TypeContext`)
- `⟦_⟧var`
- `⟦_⟧tm`
- `⟦_⟧tmextargs`: interpret the list of syntactic arguments required by a custom operator

- `,ˡᵗ-sound`: if you extend a context with a lock telescope and then interpret that, it's equivalent
  to first interpreting and then applying the lock functor for the composite of the locks.
  
- `⟦_⟧arensub`
- `⟦_⟧rensub`
- `⟦_⟧aren`
- `⟦_⟧ren`
- `⟦_⟧asub`
- `⟦_⟧sub`

#### TypeContext
- `⟦_⟧ty` (for MSTT types)
- `⟦_⟧ctx`

### BasicPrograms
Implements basic programs within MSTT:
- `coe[_]_`
- the modal type former pseudo-preserves identity and composite modalities
- `_⊛_`

### Normalization
(Imports both submodules)
- `normalize`: fueled normalization, no nonsense in type signature.

#### Helpers
- `<$> <*>` for Maybe.
#### ResultType
- `NormalizeResult`: another term that is semantically equivalent (`≅ᵗᵐ`) to the given term

### Extraction
- `ExtractableCtx`: predicate on ★-contexts, listing:
  - Agda type
  - isomorphism (denoted ↔)
- `ExtractableTy`: same idea

- `extract-ctx extract-ty`: infer the Agda thing using instance search
- `tm-extraction-setoid : Setoid`: functions from extracted ctx to extracted type, up to pointwise equality
- `extract-semtm-iso`: a setoid isomorphism between the setoid of terms and `tm-extraction-setoid`

- `ExtractableTm`:
  - Agda term
  - pointwise equality
- `extract-tm`: infer the Agda thing using instance search

- `Extractable[Ctx/Ty]` instances for:
  - empty ctx
  - ctx-ext
  - lock with identity
  - nat, bool, non-dep function, non-dep pair (still MSTT)
  
- `Only𝟙`: predicate on lock telescopes that all modalities are 1, + properties
- `ExtractableVar` (datatype)
  - this should require that the var's type is extractable
  - if you add that, then these are variables with extractable context containing only identity modalities
- `extract-var`: creates a projection in Agda
- `extract-var-iso`: `extract-var` is the one you get by actually extracting

- `ExtractableTm` instances for:
  - extractable variables
  - modal constructor of identity modality
  - function application
  - zero, suc, true, false, pair, fst, snd
  - global-def
  
## Parameter
(Imports submodules)
- parameter for MSTT+µLF

### ArgInfo
- `ArgInfo`: for a given conclusion mode: a premise mode, a program telescope (this is the info that you need to know for proof arguments of custom proof operators, relevant to intrinsic typing, since proofs are mostly extrinsically typed).

### bPropExtension
- `bPropExtension`: new **proposition** formers
  - type of constructor codes with decidable equality
  - for each constructor: program arguments & **proposition** arguments
  
### bPropExtensionSemantics
Bunch of stuff that takes a list of program arguments and **proposition** arguments
- `SemPropConstructorLocal`: for a specific context, what it means to give a semantics there
- `SemPropConstructor`: same in any context
- `SemPropConstructorLocalNatural`: for any specific substitution, what it means to give compatible semantics in dom & cod
- `SemPropConstructorNatural`: naturality of `SemPropConstructor`
- `SemPropConstructorLocalEquiv`: proposition that two `SemPropConstructorLocal`s send equivalent args to equivalent outputs.
- `SemPropConstructorLocalCong`: same but for one `SemPropConstructorLocal`
- `SemPropConstructorCong`: same but for `SemPropConstructor`, contextwise.

- `bPropExtSem`: semantics: `SemPropConstructor SemPropConstructorNatural SemPropConstructorCong`.

- helper proofs

### ProofExtension
- `ProofExt`:
  - type of constructor codes
  - for each constructor: program arguments & proposition arguments & proof arguments
  - `pf-code-check`: krijgt
    - intrinsically typed program args
    - intrinsically typed proposition args
    - for each proof arg: not the concrete argument, but a type-checker in which the argument and the corresponding program context have been plugged in, but that can still be fed a proof ctx and a proposition. Differently put, rather than getting the arguments, you get the induction hypotheses for the arguments.
    
## LogicalFramework
There is an overview file.

### bProp
There is an overview file.

#### Syntax
- `bProp`
  - `ExtBPArgs`: tuples of proposition args
- `traverse-bprop` (renaming/substitution of `bProp`)
  - also for `ExtBPArgs`

#### Interpretation
- `⟦_⟧bprop`
- `⟦_⟧bpextargs`

#### Extraction
- `ExtractableProp`
  - Agda type
  - isomorphism (denoted ↔)
- `extract-bprop`: infer the Agda thing using instance search
- bunch of instances

### Proof
There is an overview file.

#### CheckingMonad
- `ErrorMsg = String`
- `PCM` ~= `Either ErrorMsg`
- basic operations

#### Definition
- `Proof` (intrinsically indexed by program context)
- `ExtPfArgs`: tuple of proofs over a given program context
- `≡ᵇ-Reasoning`

#### Context
- `ProofCtx`
- `to-ctx : ProofCtx m → Ctx m`
- `Assumption` (= proof variable)
  - the prefix `as-` stands for `Assumption`
- `as-lt`: all locks to the right of that variable
- `lookup-assumption`: get the proposition proven by this variable, when annotated by a well-modalitied two-cell
- `contains-assumption?`: lookup variable by name
- `⟦_⟧pctx`: semantics of proof-contexts
- `to-ctx-subst`: weakening over all proof variables

#### AlphaEquivalence
- `AlphaEquivCtx`: inductive predicate on contexts
- `alpha-equiv-sub`: convert alpha-equivalence to semantic substitution
...
(Avoid this by having named stuff indexed by nameless stuff)

#### Checker
(Imports submodules)

- `check-proof` takes a plugged judgement (mode, proof context, **proof**, proposition) and checks it.

##### ResultType
- `Goal`: name & judgement (mode, proof context, proposition)
- `SemGoals: List Goal → Set`: how to provide a semantical solution for these goals
- `Evidence: <judgement> -> Set`: how to provide a semantical proof of this judgement
- `PCResult` (for a given judgement):
  - `goals`: list of goals
  - `denotation`: given semantic solutions for the goals, you get a semantical proof of the judgement that has been checked
- `⟅ goals , sgoals ↦ b ⟆` means `⟅ goals , (λ sgoals → b) ⟆`

##### SyntaxViews
Tools to match propositions and proof contexts with patterns of interest.

##### Soundness
Soundness proofs for all built-in BiSikkel inference rules

# Contributions by [uHnftOad](https://github.com/uHnftOad)
TODO: Write an overview, perhaps integrate the code.
