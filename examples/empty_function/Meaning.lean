import Miri.MIR.Contents
import Miri.Interpreter.Stack

/-! Proof-only observations retain the semantic contract of source-shaped MIR
while the interpreter keeps syntax IDs. Successful observation checks every
referenced node; it does not supply an execution-success hypothesis. -/
namespace EmptyFunction.Meaning
open Miri.MIR
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Internal frame invariant established by actual frame creation. This carries
its syntax context through local-value and location updates. -/
@[simp] def FrameMatches {Prov Layout Extra : Type}
    (frame : Miri.Interpreter.Frame Prov Layout Extra) (loaded : Miri.Interpreter.LoadedBody) : Prop :=
  frame.body = loaded.body ∧ frame.bodyId = loaded.bodyId ∧ frame.mirTables = loaded.tables

structure Entry where
  blockId : BlockNodeId
  block : BlockNode
  statementId : StatementId
  statement : StatementNode
  destination : PlaceId
  rvalue : RvalueId
  operand : OperandId
  constant : ConstantId
  retag : WithRetag

structure Entry.References (tables : SyntaxTables) (body : BodyNode) (entry : Entry) : Prop where
  block : body.basicBlocks[0]? = some entry.blockId
  blockNode : tables.blocks.lookup entry.blockId.index = .ok entry.block
  first : entry.block.statements[0]? = some entry.statementId
  statement : tables.statements.lookup entry.statementId.index = .ok entry.statement
  kind : entry.statement.kind = .Assign entry.destination entry.rvalue
  rvalue : tables.rvalues.lookup entry.rvalue.index = .ok (.Use entry.operand entry.retag)
  operand : tables.operands.lookup entry.operand.index = .ok (.Constant entry.constant)

/-- The immutable constant reference at the fixed function's entry assignment. -/
def firstConstantId (tables : SyntaxTables) (node : BodyNode) : Except String ConstantId := do
  let some blockId := node.basicBlocks[0]? | throw "entry block absent"
  let block ← (tables.blocks.lookup blockId.index).mapError (fun _ => "entry block ID absent")
  let some statementId := block.statements[0]? | throw "entry statement absent"
  let statement ← (tables.statements.lookup statementId.index).mapError (fun _ => "entry statement ID absent")
  let .Assign _ rvalueId := statement.kind | throw "entry statement is not an assignment"
  let rvalue ← (tables.rvalues.lookup rvalueId.index).mapError (fun _ => "entry rvalue ID absent")
  let .Use operandId _ := rvalue | throw "entry rvalue is not a use"
  let operand ← (tables.operands.lookup operandId.index).mapError (fun _ => "entry operand ID absent")
  let .Constant constantId := operand | throw "entry operand is not a constant"
  return constantId

theorem firstConstantId_entry (tables : SyntaxTables) (body : BodyNode) (constantId : ConstantId)
    (checked : firstConstantId tables body = .ok constantId) :
    ∃ entry : Entry, entry.constant = constantId ∧ entry.References tables body := by
  unfold firstConstantId at checked
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at checked
  cases blockAt : body.basicBlocks[0]? with
  | none => simp [blockAt] at checked
  | some blockId =>
    simp only [blockAt] at checked
    cases blockNode : tables.blocks.lookup blockId.index with
    | error reason => simp [blockNode, Except.mapError] at checked
    | ok block =>
      simp only [blockNode, Except.mapError] at checked
      cases first : block.statements[0]? with
      | none => simp [first] at checked
      | some statementId =>
        simp only [first] at checked
        cases statementAt : tables.statements.lookup statementId.index with
        | error reason => simp [statementAt, Except.mapError] at checked
        | ok statement =>
          simp only [statementAt, Except.mapError] at checked
          cases kind : statement.kind <;> simp only [kind] at checked
          all_goals try contradiction
          case Assign destination rvalueId =>
            cases rvalueAt : tables.rvalues.lookup rvalueId.index with
            | error reason => simp [rvalueAt, Except.mapError] at checked
            | ok rvalue =>
              simp only [rvalueAt, Except.mapError] at checked
              cases rvalue <;> simp only at checked
              all_goals try contradiction
              case Use operandId retag =>
                cases operandAt : tables.operands.lookup operandId.index with
                | error reason => simp [operandAt, Except.mapError] at checked
                | ok operand =>
                  simp only [operandAt, Except.mapError] at checked
                  cases operand <;> simp only at checked
                  all_goals try contradiction
                  case Constant id =>
                    cases checked
                    exact ⟨⟨blockId,block,statementId,statement,destination,rvalueId,operandId,constantId,retag⟩,
                      rfl, ⟨blockAt,blockNode,first,statementAt,kind,rvalueAt,operandAt⟩⟩

private theorem list_mapM_entry {α β ε : Type} (f : α → Except ε β)
    (xs : List α) (ys : List β) (i : Nat) (x : α)
    (checked : xs.mapM f = .ok ys) (selected : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ f x = .ok y := by
  induction xs generalizing ys i with
  | nil => simp at selected
  | cons head tail ih =>
    simp only [List.mapM_cons] at checked
    cases headEq : f head with
    | error reason => simp [headEq, bind, Except.bind] at checked
    | ok value =>
      cases tailEq : tail.mapM f with
      | error reason => simp [headEq, tailEq, bind, Except.bind] at checked
      | ok values =>
        simp [headEq, tailEq, bind, Except.bind, pure, Except.pure] at checked
        subst ys
        cases i with
        | zero =>
          simp at selected
          subst x
          exact ⟨value, rfl, headEq⟩
        | succ i =>
          exact ih values i tailEq (by simpa using selected)

private theorem list_mapM_length {α β ε : Type} (f : α → Except ε β)
    (xs : List α) (ys : List β) (checked : xs.mapM f = .ok ys) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => simp [List.mapM_nil, pure, Except.pure] at checked; subst ys; rfl
  | cons head tail ih =>
    simp only [List.mapM_cons] at checked
    cases headEq : f head with
    | error reason => simp [headEq, bind, Except.bind] at checked
    | ok value =>
      cases tailEq : tail.mapM f with
      | error reason => simp [headEq, tailEq, bind, Except.bind] at checked
      | ok values =>
        simp [headEq, tailEq, bind, Except.bind, pure, Except.pure] at checked
        subst ys
        simpa using ih values tailEq

theorem array_mapM_size {α β ε : Type} (f : α → Except ε β)
    (xs : Array α) (ys : Array β) (checked : xs.mapM f = .ok ys) : xs.size = ys.size := by
  rw [Array.mapM_eq_mapM_toList] at checked
  cases mapped : xs.toList.mapM f with
  | error reason => simp [mapped, Functor.map, Except.map] at checked
  | ok values =>
    simp [mapped, Functor.map, Except.map] at checked
    subst ys
    simpa using list_mapM_length f xs.toList values mapped

theorem array_mapM_entry {α β ε : Type} (f : α → Except ε β)
    (xs : Array α) (ys : Array β) (i : Nat) (x : α)
    (checked : xs.mapM f = .ok ys) (selected : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ f x = .ok y := by
  rw [Array.mapM_eq_mapM_toList] at checked
  cases mapped : xs.toList.mapM f with
  | error reason => simp [mapped, Functor.map, Except.map] at checked
  | ok values =>
    simp [mapped, Functor.map, Except.map] at checked
    subst ys
    simpa using list_mapM_entry f xs.toList values i x mapped (by simpa using selected)

theorem array_mapM_preimage {α β ε : Type} (f : α → Except ε β)
    (xs : Array α) (ys : Array β) (i : Nat) (y : β)
    (checked : xs.mapM f = .ok ys) (selected : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  obtain ⟨bounded, _⟩ := Array.getElem?_eq_some_iff.mp selected
  have size := array_mapM_size f xs ys checked
  have valid : i < xs.size := by omega
  have sourceAt : xs[i]? = some xs[i] := Array.getElem?_eq_some_getElem xs i valid
  obtain ⟨actual, result, applied⟩ := array_mapM_entry f xs ys i xs[i] checked sourceAt
  have same : actual = y := Option.some.inj (result.symm.trans selected)
  exact ⟨xs[i], sourceAt, same ▸ applied⟩

theorem body_metadata (tables : SyntaxTables) (typeConstants : Array TypeConst)
    (node : BodyNode) (value : Body)
    (checked : Contents.body tables typeConstants node = .ok value) :
    node.phase = value.phase ∧ node.argumentCount = value.argumentCount ∧
    node.spreadArgument = value.spreadArgument ∧ node.locals = value.locals := by
  cases blocks : node.basicBlocks.mapM (Contents.block tables typeConstants) with
  | error reason => simp [Contents.body, blocks, Functor.map, Except.map] at checked
  | ok blocks =>
    simp [Contents.body, blocks, Functor.map, Except.map] at checked
    subst value
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem body_blocks (tables : SyntaxTables) (typeConstants : Array TypeConst)
    (node : BodyNode) (value : Body)
    (checked : Contents.body tables typeConstants node = .ok value) :
    node.basicBlocks.mapM (Contents.block tables typeConstants) = .ok value.basicBlocks := by
  cases blocks : node.basicBlocks.mapM (Contents.block tables typeConstants) with
  | error reason => simp [Contents.body, blocks, Functor.map, Except.map] at checked
  | ok blocks =>
    simp [Contents.body, blocks, Functor.map, Except.map] at checked
    subst value
    rfl

theorem body_block (tables : SyntaxTables) (typeConstants : Array TypeConst)
    (node : BodyNode) (value : Body) (i : Nat) (id : BlockNodeId)
    (checked : Contents.body tables typeConstants node = .ok value)
    (selected : node.basicBlocks[i]? = some id) :
    ∃ block, value.basicBlocks[i]? = some block ∧
      Contents.block tables typeConstants id = .ok block :=
  array_mapM_entry _ _ _ _ _ (body_blocks tables typeConstants node value checked) selected

theorem block_nodes (tables : SyntaxTables) (typeConstants : Array TypeConst)
    (id : BlockNodeId) (value : BasicBlock)
    (checked : Contents.block tables typeConstants id = .ok value) :
    ∃ node, tables.blocks.lookup id.index = .ok node ∧
      node.statements.mapM (Contents.statement tables typeConstants) = .ok value.statements ∧
      Contents.terminator tables node.terminator = .ok value.terminator ∧
      node.cleanup = value.cleanup := by
  change (show Except String BasicBlock from do
    let node ← (tables.blocks.lookup id.index).mapError (fun id => s!"invalid MIR block ID {id}")
    return ⟨← node.statements.mapM (Contents.statement tables typeConstants),
      ← Contents.terminator tables node.terminator, node.cleanup⟩) = .ok value at checked
  cases found : tables.blocks.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    simp only [found, Except.mapError, bind, Except.bind] at checked
    cases statements : node.statements.mapM (Contents.statement tables typeConstants) with
    | error reason => simp [statements] at checked
    | ok decoded =>
      simp only [statements] at checked
      cases terminator : Contents.terminator tables node.terminator with
      | error reason => simp [terminator] at checked
      | ok decodedTerminator =>
        simp [terminator, pure, Except.pure] at checked
        subst value
        exact ⟨node, rfl, statements, terminator, rfl⟩

theorem statement_assignment (tables : SyntaxTables) (typeConstants : Array TypeConst)
    (id : StatementId) (source : SourceInfo) (destination : Place) (value : Rvalue)
    (checked : Contents.statement tables typeConstants id = .ok ⟨source, .Assign destination value⟩) :
    ∃ node place rvalue, tables.statements.lookup id.index = .ok node ∧
      node.kind = .Assign place rvalue ∧ Contents.place tables place = .ok destination ∧
      Contents.rvalue tables typeConstants rvalue = .ok value := by
  change ((tables.statements.lookup id.index).mapError (fun id => s!"invalid MIR statement ID {id}") >>= _) =
    .ok (⟨source, .Assign destination value⟩ : Statement) at checked
  cases found : tables.statements.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    simp only [found, Except.mapError, bind, Except.bind] at checked
    cases kind : node.kind <;> simp only [kind] at checked
    all_goals try (simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at checked)
    case Assign place rvalue =>
      cases placeEq : Contents.place tables place with
      | error reason => simp [placeEq, bind, Except.bind] at checked
      | ok decodedPlace =>
        cases rvalueEq : Contents.rvalue tables typeConstants rvalue with
        | error reason => simp [placeEq, rvalueEq, bind, Except.bind] at checked
        | ok decodedRvalue =>
          simp [placeEq, rvalueEq, bind, Except.bind, pure, Except.pure,
            Functor.map, Except.map] at checked
          obtain ⟨sourceEq, destinationEq, valueEq⟩ := checked
          subst decodedPlace
          subst decodedRvalue
          exact ⟨node, place, rvalue, rfl, kind, placeEq, rvalueEq⟩
    all_goals (split at checked <;> simp_all)
    all_goals rename_i observation
    all_goals (split at observation <;> simp_all)

theorem operand_constant (tables : SyntaxTables) (id : OperandId) (value : ConstOperand)
    (checked : Contents.operand tables id = .ok (.Constant value)) :
    ∃ constant, tables.operands.lookup id.index = .ok (.Constant constant) ∧
      Contents.constant tables constant = .ok value := by
  change ((tables.operands.lookup id.index).mapError (fun id => s!"invalid MIR operand ID {id}") >>= _) =
    .ok (Operand.Constant value) at checked
  cases found : tables.operands.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    simp only [found, Except.mapError, bind, Except.bind] at checked
    cases node with
    | Copy place => cases decoded : Contents.place tables place <;> simp [decoded, pure, Except.pure] at checked
    | Move place => cases decoded : Contents.place tables place <;> simp [decoded, pure, Except.pure] at checked
    | RuntimeChecks check => simp [pure, Except.pure] at checked
    | Constant constant =>
      cases decoded : Contents.constant tables constant with
      | error reason => simp [decoded, pure, Except.pure] at checked
      | ok constantValue =>
        simp [decoded, pure, Except.pure, Functor.map, Except.map] at checked
        subst constantValue
        exact ⟨constant, rfl, decoded⟩

theorem constant_node (tables : SyntaxTables) (id : ConstantId) (value : ConstOperand)
    (checked : Contents.constant tables id = .ok value) :
    ∃ node, tables.constants.lookup id.index = .ok node ∧ node.operand = value := by
  change ((tables.constants.lookup id.index).mapError (fun id => s!"invalid MIR constant ID {id}") >>= _) =
    .ok value at checked
  cases found : tables.constants.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    simp [found, Except.mapError, bind, Except.bind, pure, Except.pure] at checked
    exact ⟨node, rfl, checked⟩

theorem rvalue_use (tables : SyntaxTables) (typeConstants : Array TypeConst)
    (id : RvalueId) (operand : Operand) (retag : WithRetag)
    (checked : Contents.rvalue tables typeConstants id = .ok (.Use operand retag)) :
    ∃ value, tables.rvalues.lookup id.index = .ok (.Use value retag) ∧
      Contents.operand tables value = .ok operand := by
  change ((tables.rvalues.lookup id.index).mapError (fun id => s!"invalid MIR rvalue ID {id}") >>= _) =
    .ok (.Use operand retag : Rvalue) at checked
  cases found : tables.rvalues.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    simp only [found, Except.mapError, bind, Except.bind] at checked
    cases node <;> simp only at checked
    case Use value resetting =>
      cases decoded : Contents.operand tables value with
      | error reason => simp [decoded] at checked
      | ok actual =>
        simp [decoded, pure, Except.pure] at checked
        obtain ⟨operandEq, retagEq⟩ := checked
        subst actual
        subst resetting
        exact ⟨value, rfl, decoded⟩
    all_goals try (simp [pure, Except.pure, Functor.map, Except.map] at checked)
    all_goals try (split at checked <;> simp_all)
    all_goals try rename_i observation
    all_goals try (split at observation <;> simp_all)
    all_goals try rename_i observation2
    all_goals try (split at observation2 <;> simp_all)
    all_goals try rename_i observation3
    all_goals try (split at observation3 <;> simp_all)
    all_goals try (split at checked <;> simp_all)
    all_goals try rename_i observation4
    all_goals try (split at observation4 <;> simp_all)
    all_goals try (split at checked <;> simp_all)
    all_goals try rename_i observation5
    all_goals try (split at observation5 <;> simp_all)
    all_goals cases aggregateEq : Contents.aggregate tables observation5 <;> simp [aggregateEq] at checked
    all_goals cases valuesEq : observation2.mapM (Contents.operand tables) <;>
      simp [valuesEq, pure, Except.pure] at checked

theorem place_empty (tables : SyntaxTables) (id : PlaceId) (localId : LocalId)
    (checked : Contents.place tables id = .ok ⟨localId, #[]⟩) :
    ∃ node, tables.places.lookup id.index = .ok node ∧ node.localId = localId ∧
      tables.projectionLists.lookup node.projection.index = .ok #[] := by
  change ((tables.places.lookup id.index).mapError (fun id => s!"invalid MIR place ID {id}") >>= _) =
    .ok (⟨localId, #[]⟩ : Place) at checked
  cases found : tables.places.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    simp only [found, Except.mapError, bind, Except.bind] at checked
    change ((tables.projectionLists.lookup node.projection.index).mapError
      (fun id => s!"invalid MIR projection list ID {id}") >>= _) =
        .ok (⟨localId, #[]⟩ : Place) at checked
    cases projections : tables.projectionLists.lookup node.projection.index with
    | error reason => simp [projections, Except.mapError, bind, Except.bind] at checked
    | ok ids =>
      simp only [projections, Except.mapError, bind, Except.bind] at checked
      let project := fun (id : ProjectionId) => (tables.projections.lookup id.index).mapError
        (fun id => s!"invalid MIR projection ID {id}")
      change (do let values ← ids.mapM project; pure (⟨node.localId, values⟩ : Place)) =
        .ok ⟨localId, #[]⟩ at checked
      cases decoded : ids.mapM project with
      | error reason => simp [decoded, bind, Except.bind] at checked
      | ok values =>
        simp [decoded, bind, Except.bind, pure, Except.pure] at checked
        have size := array_mapM_size project ids values decoded
        have empty : ids = #[] := Array.eq_empty_iff_size_eq_zero.mpr
          (by simpa [checked.2] using size)
        exact ⟨node, rfl, checked.1, by simpa [empty] using projections⟩

theorem entry_observations (tables : SyntaxTables) (body : BodyNode) (value : Body)
    (entry : Entry) (literal : ConstOperand)
    (checked : Contents.body tables #[] body = .ok value)
    (references : entry.References tables body)
    (instruction : ((value.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
      (fun statement => statement.kind) = some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes))) :
    Contents.place tables entry.destination = .ok ⟨0,#[]⟩ ∧ entry.retag = .Yes ∧
      Contents.constant tables entry.constant = .ok literal := by
  obtain ⟨block, blockAt, blockChecked⟩ := body_block tables #[] body value 0 entry.blockId checked references.block
  obtain ⟨node, found, statements, terminator, cleanup⟩ := block_nodes tables #[] entry.blockId block blockChecked
  have sameBlock : node = entry.block := Except.ok.inj (found.symm.trans references.blockNode)
  subst node
  obtain ⟨statement, statementAt, statementChecked⟩ :=
    array_mapM_entry _ _ _ _ _ statements references.first
  have shape : statement.kind = .Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes) := by
    simpa only [blockAt, Option.bind_some, statementAt, Option.map_some, Option.some.injEq] using instruction
  have assignment : Contents.statement tables #[] entry.statementId =
      .ok ⟨statement.sourceInfo, .Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes)⟩ := by
    cases statement with
    | mk info kind =>
      change kind = .Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes) at shape
      rw [shape] at statementChecked
      exact statementChecked
  obtain ⟨actual, destination, rvalue, actualAt, actualKind, placeChecked, valueChecked⟩ :=
    statement_assignment tables #[] entry.statementId statement.sourceInfo ⟨0,#[]⟩
      (.Use (.Constant literal) .Yes) assignment
  have sameStatement : actual = entry.statement := Except.ok.inj (actualAt.symm.trans references.statement)
  subst actual
  have ids : entry.destination = destination ∧ entry.rvalue = rvalue := by
    simpa only [references.kind, StatementKindForm.Assign.injEq] using actualKind
  rw [← ids.1] at placeChecked
  rw [← ids.2] at valueChecked
  obtain ⟨operand, operandAt, operandChecked⟩ :=
    rvalue_use tables #[] entry.rvalue (.Constant literal) .Yes valueChecked
  have opEq : entry.operand = operand ∧ entry.retag = .Yes := by
    simpa only [Except.ok.injEq, RvalueForm.Use.injEq] using references.rvalue.symm.trans operandAt
  rw [← opEq.1] at operandChecked
  obtain ⟨constant, constantAt, constantChecked⟩ := operand_constant tables entry.operand literal operandChecked
  have constantEq : entry.constant = constant := by
    simpa only [Except.ok.injEq, OperandNode.Constant.injEq] using references.operand.symm.trans constantAt
  exact ⟨placeChecked, opEq.2, constantEq ▸ constantChecked⟩

/-- A source-shaped entry assignment already determines a successful ID
observation; choosing its ID adds no source-code restriction. -/
theorem firstConstantId_exists (tables : SyntaxTables) (body : BodyNode) (value : Body)
    (literal : ConstOperand) (checked : Contents.body tables #[] body = .ok value)
    (instruction : ((value.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
      (fun statement => statement.kind) = some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes))) :
    ∃ id, firstConstantId tables body = .ok id ∧ Contents.constant tables id = .ok literal := by
  cases blockAt : value.basicBlocks[0]? with
  | none => simp [blockAt] at instruction
  | some block =>
    cases statementAt : block.statements[0]? with
    | none => simp [blockAt, statementAt] at instruction
    | some statement =>
      have shape : statement.kind = .Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes) := by
        simpa only [blockAt, Option.bind_some, statementAt, Option.map_some, Option.some.injEq] using instruction
      obtain ⟨blockId, selected, blockChecked⟩ := array_mapM_preimage _ _ _ _ _
        (body_blocks tables #[] body value checked) blockAt
      obtain ⟨node, nodeAt, statements, _, _⟩ := block_nodes tables #[] blockId block blockChecked
      obtain ⟨statementId, first, statementChecked⟩ := array_mapM_preimage _ _ _ _ _ statements statementAt
      have assignment : Contents.statement tables #[] statementId =
          .ok ⟨statement.sourceInfo, .Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes)⟩ := by
        cases statement with
        | mk info kind =>
          change kind = .Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes) at shape
          rw [shape] at statementChecked
          exact statementChecked
      obtain ⟨raw, dest, rvalue, rawAt, rawKind, _, rvalueChecked⟩ :=
        statement_assignment tables #[] statementId statement.sourceInfo ⟨0,#[]⟩
          (.Use (.Constant literal) .Yes) assignment
      obtain ⟨operandId, rvalueAt, operandChecked⟩ :=
        rvalue_use tables #[] rvalue (.Constant literal) .Yes rvalueChecked
      obtain ⟨constantId, operandAt, constantChecked⟩ := operand_constant tables operandId literal operandChecked
      refine ⟨constantId, ?_, constantChecked⟩
      simp [firstConstantId, selected, nodeAt, first, rawAt, rawKind, rvalueAt, operandAt,
        Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The source-shaped assignment determines its syntax ID. No additional
compiler or execution-success premise is used to select it. -/
noncomputable def unitConstantId (tables : SyntaxTables) (body : BodyNode) (value : Body)
    (literal : ConstOperand) (checked : Contents.body tables #[] body = .ok value)
    (instruction : ((value.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
      (fun statement => statement.kind) = some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes))) : ConstantId :=
  Classical.choose (firstConstantId_exists tables body value literal checked instruction)

theorem unitConstantId_reference (tables : SyntaxTables) (body : BodyNode) (value : Body)
    (literal : ConstOperand) (checked : Contents.body tables #[] body = .ok value)
    (instruction : ((value.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
      (fun statement => statement.kind) = some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes))) :
    firstConstantId tables body = .ok (unitConstantId tables body value literal checked instruction) :=
  (Classical.choose_spec (firstConstantId_exists tables body value literal checked instruction)).1

/-- Successful observation of Return preserves the executable terminator kind. -/
theorem terminator_return (tables : SyntaxTables) (id : TerminatorId)
    (value : Terminator) (checked : Contents.terminator tables id = .ok value)
    (kind : value.kind = .Return) :
    ∃ node, tables.terminators.lookup id.index = .ok node ∧ node.kind = .Return := by
  unfold Contents.terminator at checked
  change ((tables.terminators.lookup id.index).mapError (fun id => s!"invalid MIR terminator ID {id}") >>= _) =
    .ok value at checked
  cases found : tables.terminators.lookup id.index with
  | error reason => simp [found, Except.mapError, bind, Except.bind] at checked
  | ok node =>
    refine ⟨node, rfl, ?_⟩
    simp only [found, Except.mapError, bind, Except.bind] at checked
    cases shape : node.kind <;>
      simp only [shape, pure, Except.pure, bind, Except.bind] at checked
    all_goals try (simp only [Except.ok.injEq] at checked; subst value; cases kind)
    all_goals repeat' first
      | (split at checked)
      | (simp only [Except.ok.injEq] at checked; subst value; cases kind)
      | contradiction
    all_goals repeat' (split at * <;> try simp_all)
    all_goals simp_all


/-- The source-shaped Return block supplies all checks made by the ID driver. -/
theorem entry_return (tables : SyntaxTables) (body : BodyNode) (value : Body)
    (entry : Entry) (checked : Contents.body tables #[] body = .ok value)
    (references : entry.References tables body)
    (isCleanup : (value.basicBlocks[0]?).map (·.cleanup) = some false)
    (statementCount : (value.basicBlocks[0]?).map (fun block => block.statements.size) = some 1)
    (isReturn : (value.basicBlocks[0]?).map (fun block => block.terminator.kind) = some .Return) :
    entry.block.cleanup = false ∧ entry.block.statements.size = 1 ∧
      ∃ term : TerminatorNode,
        tables.terminators.lookup entry.block.terminator.index = .ok term ∧ term.kind = .Return := by
  obtain ⟨observed, selected, blockChecked⟩ := body_block tables #[] body value
    0 entry.blockId checked references.block
  obtain ⟨node, found, statements, terminator, cleanup⟩ :=
    block_nodes tables #[] entry.blockId observed blockChecked
  have same : node = entry.block := Except.ok.inj (found.symm.trans references.blockNode)
  subst node
  have sourceCleanup : observed.cleanup = false := by
    simpa only [selected, Option.map_some, Option.some.injEq] using isCleanup
  have sourceCount : observed.statements.size = 1 := by
    simpa only [selected, Option.map_some, Option.some.injEq] using statementCount
  have sourceReturn : observed.terminator.kind = .Return := by
    simpa only [selected, Option.map_some, Option.some.injEq] using isReturn
  refine ⟨cleanup.trans sourceCleanup, (array_mapM_size _ _ _ statements).trans sourceCount, ?_⟩
  exact terminator_return tables entry.block.terminator observed.terminator terminator sourceReturn

end EmptyFunction.Meaning
