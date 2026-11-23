# Dafny Pessimistic Scheduler Module

Formally verified lock-based (pessimistic) scheduler and conflict-serializability checker in Dafny.

## Architecture & Dispatch

`PessimisticScheduler` composes a `LockPolicy` object and dispatches every schedule operation (`SchedOp`) through it:

```text
PessimisticScheduler.ValidateSchedule(ops)
  └─> policy.Dispatch(state, op)
        └─> op.Accept(policy, state)
              └─> policy.VisitLock / VisitUnlock / VisitRead / VisitWrite / VisitCommit / VisitAbort
```

- **[Types.dfy](Types.dfy)** (`module SchedulerTypes`) — `LockMode` (`Shared`, `Update`, `Exclusive`), `LockTableState`, `PolicyDecision`, and lock-table helpers.
- **[LockPolicy.dfy](LockPolicy.dfy)** (`module LockPolicies`) — `SchedOp` (`LockOp`, `UnlockOp`, `ReadOp`, `WriteOp`, `CommitOp`, `AbortOp` + shorthands `L`, `SL`, `UL`, `XL`, `U`, `R`, `W`, `C`, `A`), `trait LockPolicy`, `SimpleBinaryLockPolicy` (single-mode exclusive 2PL), `MultipleLockPolicy` (Shared/Exclusive 2PL), and `TernaryLockPolicy` (Shared/Update/Exclusive 2PL with asymmetric compatibility and `U → X` upgrades).
- **[Serializability.dfy](Serializability.dfy)** (`module Serializability`) — `IsConflictSerializableTo(s1, targetSerial)` checking whether `s1` is conflict-serializable to a serial target schedule `targetSerial`, with formal reflexivity and no-2-cycle soundness proofs.
- **[PessimisticScheduler.dfy](PessimisticScheduler.dfy)** (`module PessimisticScheduling`) — `PessimisticScheduler` initialized with a `LockPolicy`, exposing `ValidateSchedule`, `IsSerializableTo`, and `ValidateAndCheckSerializable`.
- **[DependencyGraph.dfy](DependencyGraph.dfy)** (`module DependencyGraph`) — Builds the conflict Precedence Graph (`RW`, `WR`, `WW` edges) of a schedule, checks topological transaction orderings, and proves that topological ordering implies no 2-cycles.
- **[DeadlockAndOCC.dfy](DeadlockAndOCC.dfy)** (`module DeadlockAndOCC`) — Models Wait-For graphs, 2-cycle deadlock detection, **Wait-Die** and **Wound-Wait** timestamp deadlock-prevention policies (with formal deadlock-freedom lemmas `LemmaWaitDieDeadlockFree` and `LemmaWoundWaitDeadlockFree`), and **Kung-Robinson 3-Phase Optimistic Concurrency Control (OCC)** validation (`ValidateOccSchedule`).
- **[Main.dfy](Main.dfy)** (`module Main`, `module GraphAndOccTests`) — Statically verified checks and runnable demos.
