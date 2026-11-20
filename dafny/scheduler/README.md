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

- **[Types.dfy](Types.dfy)** (`module SchedulerTypes`) — `LockMode` (`Shared`, `Exclusive`), `LockTableState`, `PolicyDecision`, and lock-table helpers.
- **[LockPolicy.dfy](LockPolicy.dfy)** (`module LockPolicies`) — `SchedOp` (`LockOp`, `UnlockOp`, `ReadOp`, `WriteOp`, `CommitOp`, `AbortOp` + shorthands `SL`, `XL`, `U`, `R`, `W`, `C`, `A`), `trait LockPolicy`, and `MultipleLockPolicy` (Shared/Exclusive Two-Phase Locking with lock upgrades).
- **[Serializability.dfy](Serializability.dfy)** (`module Serializability`) — `IsConflictSerializableTo(s1, targetSerial)` checking whether `s1` is conflict-serializable to a serial target schedule `targetSerial`, with formal reflexivity and no-2-cycle soundness proofs.
- **[PessimisticScheduler.dfy](PessimisticScheduler.dfy)** (`module PessimisticScheduling`) — `PessimisticScheduler` initialized with a `LockPolicy`, exposing `ValidateSchedule`, `IsSerializableTo`, and `ValidateAndCheckSerializable`.
- **[Main.dfy](Main.dfy)** (`module Main`) — Statically verified checks and runnable demos.
