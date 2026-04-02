# Racket Coding Style

## Parenthesis Style

The repository uses an intentionally strict parenthesis style for complex
multi-line Racket code.

### Core Rules

1. Complex multi-line forms should not end with long runs of closing
   parentheses on the same line.
2. In dense branches, avoid `)))` on one line whenever the form can be split
   cleanly.
3. For especially dense code, avoiding even `))` on the same line is preferred.
4. Closing lines for major forms should carry pairing comments when the nesting
   is not obvious.
5. Short, low-ambiguity structural lines may be exempted by the checker when
   they are mechanically common and do not materially hurt readability.

### Forms That Should Usually Be Split

- `define` and `define-values`
- `match` and `match*`
- `cond`
- `if` when the branches are multi-line
- `for/fold`, `for/and`, `for/or`
- `lambda`
- `provide/contract`, `contract-out`, `->i`
- `rename-out`, `only-in`
- `struct` method/property blocks

### Pairing Comment Guidance

Use short comments on key closing lines, for example:

- `; define foo`
- `; cond: queue empty?`
- `; match: node`
- `; lambda: sequence`
- `; provide/contract`

Only add these comments where they materially reduce pairing ambiguity.

### Enforcement Strategy

Phase 1 uses a lightweight repository script that reports dense closing
parenthesis runs. It defaults to warning-oriented checks for runs of three or
more closers on a code line (before comments, and excluding string literal
content), with AST-driven syntax+semantic-aware exemptions for narrow structural patterns
such as compact `for` clause/header lines.

Recommended commands:

```sh
racket tools/check-racket-paren-style.rkt
racket tools/check-racket-paren-style.rkt --show-config --list-rules --list-exemptions --summary-only --limit 20
racket tools/check-racket-paren-style.rkt --enable-rule dense-closing-run --summary-only --limit 20
racket tools/check-racket-paren-style.rkt --disable-rule dense-closing-run --summary-only --limit 20
racket tools/check-racket-paren-style.rkt --summary-only --limit 20
racket tools/check-racket-paren-style.rkt --write-baseline tools/paren-style.baseline
racket tools/check-racket-paren-style.rkt --baseline tools/paren-style.baseline --summary-only --limit 20
racket tools/check-racket-paren-style.rkt --baseline tools/paren-style.baseline --fail-on-violation --fail-path-rx "/safe[.]rkt$"
racket tools/check-racket-paren-style.rkt --max-run 3 --fail-on-violation pvector/safe.rkt
racket tools/check-racket-paren-style.rkt --max-run 2
racket tools/check-racket-paren-style.rkt --max-run 2 --fail-on-violation
```

The script is intentionally conservative. It helps catch regressions, but it
does not replace human review for pairing comments and readability.

### Configuration Visibility

Use these to inspect active behavior:

- `--show-config`: prints active thresholds/paths/flags
- `--list-rules`: prints all built-in style rules
- `--list-exemptions`: prints all built-in narrow exemptions by id and description
- `--enable-rule` / `--disable-rule`: narrow the active rule set
- `--fail-path-rx`: restrict fail-on-violation scope to matching file paths
- Rule specs are data-driven in `tools/paren-style/rules-config.rkt`
- Exemption specs are data-driven in `tools/paren-style/exemptions-config.rkt`
- Exemption specs support optional path scoping, allowing low-generalization
  exceptions that only apply to specific module families (for example
  `*/safe.rkt`).

Recommended rollout:

1. Use `--summary-only` to identify the worst files.
2. Write a baseline to freeze the current warning set when needed.
3. Clean one file or one module group at a time.
4. Enable `--fail-on-violation` only for touched paths, already-clean files,
   or checks run against a baseline.
5. Raise strictness from `--max-run 3` to `--max-run 2` after the warning count
   is materially reduced.
