---
name: Bug report
about: Report a bug in Aeneas
title: 'Bug: <describe the bug>'
labels: bug
---

<!-- Thank you for submitting a bug report! Please check this isn't already reported in another issue.

Aeneas translates the LLBC produced by Charon into Lean, so a reproduction usually needs the Rust code, the Charon command that produced the `.llbc` and the Aeneas command together with its output.

Small, self-contained reproducible examples help us fix bugs much faster and the majority of bugs can be reproduced in a few lines of Rust. 

Add further details as required, delete any part of the template which isn't relevant. -->

**Rust code to reproduce the bug**:

```rust
// add your code here
```

**Charon command**: <!-- the `charon` command you ran to produce the `.llbc`, e.g. `charon cargo --preset=aeneas --dest-file=my_crate.llbc` -->

**Aeneas command**: <!-- the `aeneas` command you ran, e.g. `aeneas -backend lean my_crate.llbc -dest proofs` -->

**Versions**:
- Aeneas: <!-- commit hash -->
- Charon: <!-- version -->

**Aeneas output**:

<!-- In the case that Aeneas generates warnings or errors, include the output:
- If Aeneas aborted with an `Uncaught exception`, paste the full backtrace.
- Otherwise, paste the relevant errors/warnings. 
Running with `-print-error-emitters` includes the compiler source location of each error. -->

**Lean translation**:

<!-- Is the bug related to incorrect Lean code being produced by Aeneas? What is produced? What should instead be produced? -->

**Other steps needed to reproduce**: <!-- if relevant -->

**Explain the bug**: <!-- why is this behavior incorrect, and what do you think Aeneas should do instead -->

**Priority / impact**: <!-- how badly does this block you, and is there a workaround? -->

**Where was this seen?**: <!-- if the minimal example above was reduced from real code, tell us the project / crate / function it came from. -->

**Regression?**: <!-- did this work with an earlier version of Aeneas or Charon? If so, which commit/version last worked? -->
