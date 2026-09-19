module
public import Lean

meta section

/-!
The small interface between proof search and optional experiments. This module
contains data and callbacks only: no timers, recorder, file output or search.
An observer must call its continuation exactly once and leave proof state alone.
Experimental middleware may restrict resources or deliberately abort a span;
the engine still owns rollback, accounting and final proof validation.
-/

open Lean Elab Tactic
namespace waterfall

-- Two independent limits matter: effort bounds the number of attempted moves;
-- Lean's ambient heartbeat budget bounds all work, including move enumeration.
-- The initial per-move slice grows with strength. The public effort knob gives
-- the search more opportunities to reach both deeper plans and stronger moves.
/-- Engine resource and enumeration controls. `effort` is the usual tuning knob.
All heartbeat counts here are raw, unlike Lean's `maxHeartbeats` option units. -/
public structure Config where
  /-- Global number of attempted proof operations, including failed branches. -/
  effort : Nat := 1000
  /-- Base raw heartbeat slice for an operation; trial strength scales it.
  The actual slice never exceeds the enclosing remaining allowance. -/
  attemptHeartbeats : Nat := 20000000
  /-- Print the final search summary, including failure diagnostics. -/
  report : Bool := false
  /-- Generate batches only after earlier continuations fail. -/
  lazy : Bool := true
  /-- Delay applicability probes until their candidate is considered. -/
  deferChecks : Bool := false
  deriving Inhabited

-- These counters live in IO.Ref so restoring a failed branch cannot refund work.
-- `choices` comes from the winning checkpoint's plan after the whole trial
-- succeeds. Its reverse chronological order is for diagnostics, not execution.
/-- Work spent across all attempted branches, plus the winning proof path. -/
public structure Stats where
  attempts : Nat := 0
  nodes : Nat := 0
  depth : Nat := 0
  strength : Nat := 1
  choices : Array String := #[]
  deriving Inhabited


/-- Groups retain the original operation order. Their generators can be delayed
independently; reordering groups must retain every group to preserve reachability. -/
public inductive Group where
  /-- Leaf solvers; an accepted move must leave no child obligations. -/
  | close
  /-- Introductions, extensionality, normalization and target splitting. -/
  | basic
  /-- Case analysis and inversion of assumptions. -/
  | hypotheses
  /-- Backward application of assumptions, supplied rules and constructors. -/
  | rules
  /-- Backward application of indexed library theorems. -/
  | library
  /-- Forward instantiation, introducing a derived assumption. -/
  | forward
  /-- Induction or case analysis following a function's recursive calls. -/
  | functions
  /-- Induction on data/evidence, with motive variants; ordinary data cases. -/
  | induction
  deriving BEq, Repr, Inhabited, ToJson, FromJson

public def structuralGroups : Array Group :=
  #[.basic, .hypotheses, .rules, .library, .forward, .functions, .induction]

public inductive InductionKind where
  | none | data | evidence | functional
  deriving BEq, Repr, Inhabited, ToJson, FromJson

/-- The shape of the motive prepared for an induction candidate. This is policy
metadata: schedulers should not have to recover semantic choices from labels. -/
public inductive InductionMotive where
  | direct | localGeneralization | indexAbstraction
  | localGeneralizationAndIndexAbstraction
  deriving BEq, Repr, Inhabited, ToJson, FromJson

/-- Deferred inference plus typed policy metadata. Only the engine owns rollback
and acceptance of its complete continuation. Noninduction is the default. -/
public structure Move where
  cost : Nat := 1
  label : String
  run : TacticM Unit
  /-- Optional local stutter pruning: reject a single child whose target and
  assumption types equal the input. This is a heuristic for built-in operations,
  not a test of complete proof-state equality. Extensions default to accepting
  local stutter, since they may advance shared witnesses or other obligations.
  Positive structural costs still bound every accepted extension step. -/
  checkLocalChange : Bool := false
  /-- False when replay needs state or proof inputs absent from the ordinary plan. -/
  replayable : Bool := true
  induction : InductionKind := .none
  motive : InductionMotive := .direct
  /-- Semantic metadata for scheduling, independent of display labels. -/
  major : Option FVarId := none
  /-- Optional subject for inspecting or explaining an operation. Like `major`,
  its free variables belong to the operation's input checkpoint. Search policies
  need not use it; rendering must not recover it by rerunning the inference. -/
  subject : Option Expr := none
  /-- An ordinary command proposal, when the adapter already constructs one.
  Explanations must recheck its printed text in the input checkpoint. Dispatch
  and policy selection never depend on this optional presentation metadata. -/
  command? : Option (TSyntax `tactic) := none
  role : Name := .anonymous
  /-- Optional applicability probe. It runs under temporary state and consumes
  ambient resources, but a rejected candidate is not a dispatched attempt. -/
  check : Option (TacticM Bool) := none

/-- An ordinal in a versioned generator, not a fresh Lean identifier or display
label. Replay also verifies the complete input agenda and generated child count. -/
public structure ActionId where
  group : Group
  index : Nat
  deriving BEq, Repr, Inhabited, ToJson, FromJson

public structure Candidate where
  action : ActionId
  move : Move

public inductive Phase where
  | run | trial | node | enumerate | action | continuation
  deriving BEq, Repr, Inhabited, ToJson, FromJson

public structure Span where
  phase : Phase
  depth : Nat := 0
  strength : Nat := 1
  group : Option Group := none
  action : Option ActionId := none
  induction : InductionKind := .none
  label : String := ""
  deriving Repr, Inhabited, ToJson, FromJson

/-- Explicit outcomes avoid mistaking a normally returned `false` for success.
Enumeration supplies a count; exceptions are observed by the middleware itself. -/
public structure Outcome where
  success : Option Bool := none
  count : Option Nat := none
  deriving Repr, Inhabited, ToJson, FromJson

/-- A retained proof step: which operation was chosen, the full input agenda,
and the number of premises it generated. Its input checkpoint is stored alongside
it in `Node.plan`; observing local success alone does not retain a step. -/
public structure Selection where
  replayable : Bool
  action : ActionId
  induction : InductionKind
  motive : InductionMotive := .direct
  label : String
  role : Name := .anonymous
  strength : Nat
  remaining : Nat
  cost : Nat
  children : Nat
  agenda : List MVarId
  focus : Nat := 0

/-- Lazy, effectful enumeration. `visit` returning true stops enumeration.
The producer runs no later alternative until the visitor has returned false.
This continuation representation avoids an eager array of proof snapshots. -/
public abbrev Choices (α : Type) := (α → TacticM Bool) → TacticM Bool

/-- Siblings have independent ancestry; all goals share one Lean proof state. -/
public structure Job where
  goal : MVarId
  remaining : Nat
  ancestors : List Candidate := []
  deriving Inhabited

/-- A complete search checkpoint, including the retained plan and arbitrary,
typed policy state. It can be stored by another traversal algorithm as a frontier
entry. Proof-search resource counters deliberately live outside this value. -/
public structure Node (σ : Type) where
  saved : Tactic.SavedState
  jobs : List Job
  state : σ
  plan : List (Selection × Tactic.SavedState) := []

/-- Engine-owned transition providers. Empty batches mean the installed default
cascade. Explicit batches permit scheduling and filtering across any goal.
`restart` restores a checkpoint, installs policy state and charges one attempt;
it is not a proof step and does not retain the abandoned plan. Exhausted work
budgets disable expand/restart; policies may still select saved checkpoints. -/
public structure Space (σ : Type) where
  current : Node σ
  root : Node σ
  expand : Nat → Array (Array Group) → (Candidate → Bool) → Choices (Node σ)
  restart : Node σ → σ → Choices (Node σ)

/-- One policy chooses an ordered lazy subsequence of local transitions. State
is immutable along a branch and restored with that branch. The default is the
existing head-first, exhaustive continuation search. -/
public structure SearchPolicy where
  State : Type
  initial : State
  choose : Space State → Choices (Node State)

public def SearchPolicy.default : SearchPolicy := ⟨Unit, (), fun space => space.expand 0 #[] (fun _ => true)⟩

/-- A root-only prefix followed by diagonals, without revisiting prefix pairs.
A prefix of one is ordinary diagonal deepening. Three reproduces the installed
schedule. This helper is convenient, but policies may use any fair enumerator. -/
public def diagonalTrials (rootPrefix round : Nat) : Array (Nat × Nat) :=
  if round == 0 then (List.range (max 1 rootPrefix)).toArray.map (fun i => (0, i + 1))
  else (List.range (round + 1)).toArray.filterMap fun tier =>
    if tier == round && round < rootPrefix then none else some (round - tier, tier + 1)

public structure Hooks where
  /-- Reserve one attempted operation, including a checkpoint restart. Called
  before dispatch and outside rollback. Raising an exception stops the run.
  Schedulers can use this to share a work budget across isolated searches. -/
  charge : TacticM Unit := pure ()
  policy : SearchPolicy := .default
  /-- Finite batches of trials. For eventual reachability, visit every finite
  depth and positive strength; effort truncates this one sequence globally. -/
  trials : Nat → Array (Nat × Nat) := diagonalTrials 3
  /-- Effective admission and path cost. The default charges library moves four
  and constructor closers one; the five ordinary closers remain free.
  Finite fixed costs retain eventual availability. Structural generators may
  have intrinsic floors (library retrieval currently requires depth two).
  Structural costs must be at least max 1 Move.cost; search rejects lower costs
  before dispatch, so zero-cost structural cycles cannot bypass depth limits.
  The callback receives the current goal and node span under its local context
  and full proof-state rollback. External IO effects and spent work are not
  rolled back: replay needs the same deterministic cost for the same input. -/
  cost : MVarId → Span → Candidate → TacticM Nat :=
    fun _ _ c => pure (c.move.cost * (if c.action.group == .library then 2 else 1))
  /-- Opt-in providers append alternatives; original generated selectors keep their indices. -/
  extraMoves : MVarId → Array (TSyntax `term) → Nat → Nat → Group → TacticM (Array Move) :=
    fun _ _ _ _ _ => pure #[]
  /-- Optional experiments may coalesce groups; the engine checks that every
  original group occurs exactly once. Each group's generator remains unchanged. -/
  batches : Array (Array Group) := structuralGroups.map (fun g => #[g])
  /-- Return only a permutation of original selectors, never replacement actions.
  `none` leaves the batch untouched; the engine validates every supplied order.
  Like cost, this runs in the node's input context under full snapshot rollback.
  It may inspect goals and hypotheses or compute features in an optional module. -/
  order : MVarId → Span → Array Candidate → TacticM (Option (Array ActionId)) := fun _ _ _ => pure none
  around : {α : Type} → Span → (α → Outcome) → TacticM α → TacticM α :=
    fun _ _ body => body
  /-- Called only when every child and pending sibling has closed. The snapshot
  is the input to the choice, for read-only recording under temporary restore.
  Calls arrive in reverse plan order after a complete trial succeeds. Traversal
  order need not match the proof path; abandoned branches cannot enter the plan. -/
  accepted : Selection → Tactic.SavedState → TacticM Unit := fun _ _ => pure ()

public def Hooks.bool (hooks : Hooks) (span : Span) (body : TacticM Bool) : TacticM Bool :=
  hooks.around span (fun ok => { success := some ok }) body

public def Hooks.array (hooks : Hooks) (span : Span) (body : TacticM (Array α)) :
    TacticM (Array α) :=
  hooks.around span (fun values => { count := some values.size }) body

end waterfall
