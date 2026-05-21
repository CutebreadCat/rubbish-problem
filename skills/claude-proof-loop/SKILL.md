---
name: claude-proof-loop
description: Run iterative Lean formalization proof attempts using Claude or a Claude-style model, with Lean statements, proof assistant checks, self-review, revision logs, literature cautions for open problems, and optional GitHub commit/push submission. Use when Codex needs to work on hard or open math problems through repeated Lean prove-check-review-repair cycles, especially with local problem materials and a repository target.
---

# Claude Proof Loop

## Core Workflow

Use this skill to manage a bounded Lean formalization loop, not to declare an open problem solved prematurely.

1. Load the local problem statement and source notes.
2. Choose one narrow Lean target lemma or theorem for the current loop.
3. Generate a Lean statement and proof attempt with Claude or a Claude-style model.
4. Run Lean locally with `lake env lean <file>` or `lake build` when a Lake project exists.
5. Review the Lean errors adversarially: distinguish syntax/import problems from mathematical gaps.
6. Rewrite the target statement if the review finds the original claim too broad or not formalizable yet.
7. Save the Lean file, proof attempt, Lean output, review, and next prompt in a dated proof log.
8. Commit only material that is useful and honest: checked Lean lemmas, failed Lean attempts, counterexamples, and review notes.

Never present an open Erdős problem as solved unless the proof survives independent review and verification.

## Iteration Rules

- Work on one Lean lemma per loop.
- Prefer exact small claims over broad asymptotic claims.
- Make hypotheses explicit.
- Separate lower bounds, upper bounds, constructions, and computational evidence.
- Treat every floor, parity, congruence, and "large enough" phrase as a proof obligation.
- Keep failed attempts in the log if they reveal a useful obstruction.
- When using Claude, ask it to output a compilable Lean block first, then a short "mathematical intent" note, a "weakest formalization step" note, and a "possible counterexample search" note.
- Do not accept natural-language proof text as completion; the proof loop is complete only when Lean accepts the target, or when the log clearly records why the current Lean target failed.

## Repo Layout

For a problem workspace, prefer:

```text
problem-XXX/
  README.md
  materials/
    source-summary.md
    research-directions.md
  proof-log/
    iteration-001.lean
    iteration-001-attempt.md
    iteration-001-lean-output.txt
    iteration-001-review.md
    iteration-001-next-prompt.md
```

## Scripted Loop

Use `scripts/claude_proof_loop.ps1` when a repeatable loop is useful.

Example:

```powershell
powershell -ExecutionPolicy Bypass -File .\skills\claude-proof-loop\scripts\claude_proof_loop.ps1 `
  -ProblemDir .\problem-361 `
  -Target "Prove an exact formula for c >= 1, with floors" `
  -LeanFile .\problem-361\proof-log\iteration-001.lean `
  -MaxIterations 3 `
  -AutoGit
```

If the `claude` CLI is available, the script calls it in print mode. If not, it writes the prompt files so the user can paste them into Claude manually.

For a true continuing loop, add `-Continuous`; the loop stops when a review contains `verdict: pass` or when the user interrupts it. Use this only with a configured Claude CLI.
Use `-ClaudeTimeoutSeconds 300` or another larger value for slow model calls.

## Lean Requirements

Every proof iteration must create or update a `.lean` file. Prefer a repo-local Lake project with Mathlib. If no Lake project exists, log that explicitly and still generate Lean code against the intended imports.

Default check order:

1. If `lakefile.lean`, `lakefile.toml`, or `lake-manifest.json` exists, run `lake env lean <lean-file>`.
2. Otherwise, if `lean` is available, run `lean <lean-file>`.
3. If neither command is available, save `iteration-NNN-lean-output.txt` with `Lean toolchain not found`.

Lean files may contain `sorry` only for scaffolding attempts. A verified lemma must be rechecked with no `sorry` in the lemma being claimed as proved.

## GitHub Submission

Only commit after the loop has produced useful artifacts.

1. Run `git status --short`.
2. Stage only relevant problem and skill files.
3. Commit with a clear message such as `Add Erdős 361 proof loop materials`.
4. Push only if the user requested repository submission or the workflow explicitly uses `-Push`.

For open-problem work, commit messages and PR descriptions must avoid solved-claim language unless the result is genuinely verified.

## Erdős 361 Local Reference

For this repository, read `problem-361/materials/source-summary.md`, `problem-361/materials/research-directions.md`, and `problem-361/materials/problem-361.lean` before generating any proof attempt. Formalize small lemmas first, such as the exact `c >= 1` result, before attempting the open `0 < c < 1` range.
