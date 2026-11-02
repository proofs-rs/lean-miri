import empty_function.Target
import Miri.Input.CompilerExternStatic
import Miri.Input.CompilerForeignSymbols

/-! Pure current-data mapping for foreign CTFE relocation declarations.
These records follow ExternStatic.resolve / CompilerExternStatic.hooksOn's
branch precedence, but contain no stateful resolver/root/address success law.
Adequacy for the actual resolver remains a separate proof obligation. -/
namespace EmptyFunction.ExternMapping
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open WholeCall
set_option autoImplicit false

def runtime (before : State) : ExternStatic.State :=
  before.machine.user.payload.payload.user.runtime.externStatics

def entries (before : State) (decl : CompilerExternStatic.Declaration) :
    Array (String × StrictPointer) :=
  if decl.linkage == .none then (runtime before).symbols else (runtime before).imports

/-- Exact immutable declaration row, independent of runtime resolution. -/
structure Declaration (s : Static) (definition : DefId)
    (decl : CompilerExternStatic.Declaration) : Prop where
  lookup : s.prepared.compiler.externStatics.declarations.find? (·.definition == definition) = some decl
  supported : decl.result = .ok ()

/-- The runtime pointer and backing metadata are current data. The source
checks size/alignment for shim and winner branches; weak-cell fallback does
not perform that check and is represented separately below. -/
structure LayoutBinding (before : State) (decl : CompilerExternStatic.Declaration)
    (backing : AllocId) where
  info : AllocationInfo
  lookup : before.machine.memory.getAllocInfo backing = .ok info
  size : decl.size.bytes ≤ info.size.bytes
  align : decl.align.pow2 ≤ info.align.pow2

/-- Follow the actual shim/weak/exported-winner precedence. Root/address
resources must refer to backing, never to the foreign declaration's AllocId. -/
inductive Selection (s : Static) (before : State) (definition : DefId)
    (backing : AllocId) where
  | shim (decl : CompilerExternStatic.Declaration) (pointer : StrictPointer)
      (declaration : Declaration s definition decl)
      (selected : (entries before decl).find? (·.1 == decl.symbol) = some (decl.symbol,pointer))
      (identity : pointer.provenance.getAllocId = some backing)
      (cached : ∃ base, before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == backing) =
        some ⟨backing,base⟩)
      (layout : LayoutBinding before decl backing)
      (symbols : CompilerForeignSymbols.Prepared)
      (foreignMetadata : s.prepared.compiler.foreignSymbols = .ok symbols)
      (clash : CompilerForeignSymbols.checkSymbolClash symbols decl.symbol = .ok ())
  | weak (decl : CompilerExternStatic.Declaration) (pointer : StrictPointer)
      (declaration : Declaration s definition decl)
      (noShim : (entries before decl).find? (·.1 == decl.symbol) = none)
      (linkage : decl.linkage = .externalWeak)
      (size : decl.size = s.prepared.compiler.externStatics.runtime.target.pointerSize)
      (selected : (runtime before).missingWeak = some pointer)
      (identity : pointer.provenance.getAllocId = some backing)
      (cached : ∃ base, before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == backing) =
        some ⟨backing,base⟩)
  | exported (decl : CompilerExternStatic.Declaration)
      (selected : CompilerExternStatic.Selected)
      (winnerDefinition : DefId) (exportId : Input.AllocationId) (global : GlobalAllocation)
      (declaration : Declaration s definition decl)
      (noShim : (entries before decl).find? (·.1 == decl.symbol) = none)
      (linkage : decl.linkage ≠ .externalWeak)
      (lookup : s.prepared.compiler.externStatics.selected.find? (·.symbol == decl.symbol) = some selected)
      (supported : selected.winner.status = "supported")
      (kind : selected.winner.kind = "static")
      (definition : selected.winner.definition = some winnerDefinition)
      (allocation : selected.winner.allocation = some exportId)
      (image : s.prepared.image.source.any (·.id == exportId) = true)
      (mapping : before.machine.memory.runtimeIdForExport? exportId = some backing)
      (descriptor : before.machine.memory.findGlobal? backing = some global)
      (payload : global.payload = some (.static winnerDefinition true false false))
      (layout : LayoutBinding before decl backing)
      (mutability : (layout.info.mutability == .Mut) = decl.mutable)

/-- CTFE target classification. A direct TLS declaration is not a CTFE global
pointer representation. Runtime TLS storage pointers are classified elsewhere
by their actual storage allocation, and are not excluded by this condition. -/
inductive Target (s : Static) (before : State) (declared backing : AllocId) : Prop where
  | direct (same : backing = declared)
      (supplier : (∃ global,before.machine.memory.findGlobal? declared = some global) ∨
        before.machine.memory.hasExtraFunctionId declared = true ∨
        before.machine.memory.hasVaListId declared = true)
      (staticPredicates : ∀ global, before.machine.memory.findGlobal? declared = some global →
        global.kind = .static → ∃ definition isStatic tls foreign,
          global.payload = some (.static definition isStatic tls foreign))
      (format : ∀ global, before.machine.memory.findGlobal? declared = some global →
        ∀ definition isStatic tls foreign,
        global.payload = some (.static definition isStatic tls foreign) →
        tls = false ∧ foreign = false)
  | foreign (global : GlobalAllocation) (definition : DefId)
      (descriptor : before.machine.memory.findGlobal? declared = some global)
      (payload : global.payload = some (.static definition true false true))
      (selection : Selection s before definition backing)

end EmptyFunction.ExternMapping
