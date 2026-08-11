# Instructions

Thanks for opening a PR! We welcome external contributions but encourage contributors to
coordinate with us before, either by joining the Zulip or by opening issues with detailed
proposals. In particular, we ask contributors to engage with us before making deep
modifications of the code or implementing non trivial features, as these require in-depth
design discussions and careful reviews. This means for instance that proposals to extend
the translation should be discussed first. On the other hand, you should feel free to
directly submit PRs that fix an issue through a scoped, small fix, or that add theorems to
the standard library. In case of doubt, discuss with us.

**Good practices:**

- please keep your PRs small and scoped: they will be a lot easier to review and accept.
- new models of Rust definitions should be systematically tested (you can annotate unit
  functions with `#[verify::test]` to generate tests at extraction time)
- avoid AI generated PR descriptions: they tend to be verbose and imprecise

**AI assisted PRs:**

Please indicate whether the PR was AI assisted, and by how much: did you use AI in a
limited way or did you completely vibe-code the PR? We welcome AI assisted PRs but need
this information to adjust our level of scrutinee during the review and evaluate whether
it is reasonable to ask for the contributor to completely modify their code. Also note
that we expect contributors to own and understand the code they submit: as we will
carefully review the PR line by line, we expect contributors to have done the same for AI
generated code (reviewing PRs takes time and we have limited resources).
