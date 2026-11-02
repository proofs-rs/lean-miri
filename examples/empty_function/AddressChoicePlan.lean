import empty_function.ChoiceSupply

/-! Source-backed address-demand plans for the managed, no-race profile.
Cache/reuse/generation transitions below are the existing pure source
operations. Errors are explicit halted plans, accepting supply without claiming success.
A separate adequacy theorem must connect these plans to MachineAddress and
the actual ordered relocation/projection demands of empty_function. -/
namespace EmptyFunction.AddressChoicePlan
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Memory.AllocAddresses
open EmptyFunction.ChoiceSupply
set_option autoImplicit false

/-- Finish the actual no-race address assignment, including its explicit
post-acquire cache insertion. Errors are retained without restricting supply. -/
def assignedState (result : AddressStateResult AddressAssignment) : Except AddressStateError GlobalAddressState :=
  match result.outcome with
  | .error error => .error error
  | .ok (.ready _) => .ok result.state
  | .ok (.acquireRequired id address _) =>
      let cached := result.state.cacheAddress id address
      match cached.outcome with
      | .error error => .error error
      | .ok () => .ok cached.state

def afterAssignment {budget : Nat} (next : GlobalAddressState → Plan budget)
    (result : AddressStateResult AddressAssignment) : Plan budget :=
  match assignedState result with
  | .error error => .halted (reprStr error)
  | .ok state => next state

/-- After the source Bernoulli choices, compute the exact candidate range
with ReusePool.prepareTakeAddr. The resulting request count is stop-begin;
source assignment sees the same prepared reuse state as MachineAddress. -/
def select {budget : Nat} (initial : GlobalAddressState) (id : AllocId)
    (info : AllocationAddressInfo) (generation : AddressGenerationState)
    (kind : AddressMemoryKind) (reuse cross : Bool)
    (next : GlobalAddressState → Plan budget) : Plan (budget+1) :=
  let prepared := generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind info.thread
  let current := {initial with generation := some {generation with reusePool := prepared.state}}
  match prepared.outcome with
  | .error error => .halted (reprStr error)
  | .ok none =>
      .request (.index .slack 16) fun input _ =>
        match input with
        | .index _ value =>
          if supported : value < 16 then
            afterAssignment next (current.addrFromAllocId id (some info)
              ⟨reuse,cross,0,⟨value,supported⟩⟩)
          else .blocked
        | _ => .blocked
  | .ok (some (begin,stop)) =>
      .request (.index .pool (stop-begin)) fun input _ =>
        match input with
        | .index _ value =>
            afterAssignment next (current.addrFromAllocId id (some info)
              ⟨reuse,cross,begin+value,⟨0,by decide⟩⟩)
        | _ => .blocked

/-- One actual managed address-attempt demand. Cache hits draw nothing;
stack misses have only a slack draw; others have at most three draws. The
uniform type uses three reserve slots, permitting shorter branches. -/
def attempt {budget : Nat} (initial : GlobalAddressState) (id : AllocId)
    (info : AllocationAddressInfo) (next : GlobalAddressState → Plan budget) : Plan (budget+3) :=
  if (initial.baseAddr.find? (fun row => row.allocId == id)).isSome then
    ((next initial).pad.pad).pad
  else if info.kind == .dead || !info.live then .halted (reprStr (AddressStateError.deadAllocation id))
  else
    let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
    if info.kind == .typeId then
      ((afterAssignment next (initial.addrFromAllocId id (some info) unused)).pad.pad).pad
    else if initial.addressMode != .managed then .halted "source external/native address capability required"
    else match initial.generation,info.memoryKind with
      | some generation,some kind =>
        if kind == .stack then
          ((select initial id info generation kind false false next).pad).pad
        else
          .request (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) fun input _ =>
            match input with
            | .boolean _ false => (select initial id info generation kind false false next).pad
            | .boolean _ true =>
              .request (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) fun input _ =>
                match input with
                | .boolean _ cross => select initial id info generation kind true cross next
                | _ => .blocked
            | _ => .blocked
      | _,_ => .halted "source address generation or memory kind unavailable"

/-- An ordered list of ROOT address attempts. Foreign shim/weak pointers do
not enter this list because the actual resolver returns their stored pointer
without requesting a new root address. Exported foreign winners enter with
their resolved backing ID and its current allocation metadata. -/
structure Attempt where
  id : AllocId
  info : AllocationAddressInfo

def ordered : (attempts : List Attempt) → GlobalAddressState → Plan (3*attempts.length)
  | [], _ => .done
  | first::rest, state => by
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using
        attempt state first.id first.info (ordered rest)

/-- Supply retains the actual non-choice failure without calling it safe. -/
theorem afterAssignment_error {budget : Nat} (next : GlobalAddressState → Plan budget)
    (state : GlobalAddressState) (error : AddressStateError) :
    afterAssignment next ⟨state,.error error⟩ = .halted (reprStr error) := rfl

end EmptyFunction.AddressChoicePlan

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.AddressChoicePlan." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function address-plan axiom {dependency}"
